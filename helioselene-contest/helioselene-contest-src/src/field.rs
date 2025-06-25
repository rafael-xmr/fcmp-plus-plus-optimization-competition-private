use zeroize::DefaultIsZeroes;

use crypto_bigint::{Encoding, Limb, U256};

const TABLE_SIZE: usize = 16;

#[inline(always)]
const fn muladdcarry(x: u64, y: u64, z: u64, w: u64) -> (u64, u64) {
    let res = (x as u128)
        .wrapping_mul(y as u128)
        .wrapping_add(z as u128)
        .wrapping_add(w as u128);
    ((res >> 64) as u64, res as u64)
}

#[inline(always)]
const fn mac(word: u64, b: u64, c: u64, carry: u64) -> (u64, u64) {
    let a = word as u128;
    let b = b as u128;
    let c = c as u128;
    let carry = carry as u128;
    let ret = a + (b * c) + carry;
    (ret as u64, (ret >> 64) as u64)
}

#[inline(always)]
const fn adc(x: [u64; 2], y: [u64; 2]) -> ([u64; 2], bool) {
    let (lo, carry1) = x[0].overflowing_add(y[0]);
    let (hi_temp, carry2) = x[1].overflowing_add(y[1]);
    let (hi, carry3) = hi_temp.overflowing_add(carry1 as u64);
    ([lo, hi], carry2 || carry3)
}

#[inline(always)]
fn mul_wide(x: [u64; 2], y: [u64; 2]) -> ([u64; 2], [u64; 2]) {
    // i = 0
    let (r0, c0) = mac(0u64, x[0], y[0], 0);
    let (r1, c1) = mac(0u64, x[0], y[1], c0);

    let r2 = c1;

    // i = 1
    let (n1_2, c2) = mac(r1, x[1], y[0], 0);
    let r1 = n1_2;
    let (n2_2, c3) = mac(r2, x[1], y[1], c2);
    let r2 = n2_2;
    let r3 = c3;

    ([r0, r1], [r2, r3])
}

#[inline(always)]
fn square_wide(x: [u64; 2]) -> ([u64; 2], [u64; 2]) {
    // First, handle cross products (off-diagonal elements)
    // x[0] * x[1] appears twice in the expansion
    let cross_prod = (x[0] as u128) * (x[1] as u128);

    // Double the cross product - need to handle potential overflow
    let doubled_low = cross_prod << 1;
    let carry_from_double = (cross_prod >> 127) as u64; // Top bit that gets shifted out

    // Place the doubled cross product at positions 1 and 2
    let r1 = doubled_low as u64;
    let r2 = (doubled_low >> 64) as u64;
    let r3 = carry_from_double;

    // Now add the diagonal elements (x[i] * x[i])
    // x[0]²
    let square0 = (x[0] as u128) * (x[0] as u128);
    let r0 = square0 as u64;

    // Add high part of x[0]² to r1
    let carry = square0 >> 64;
    let sum = (r1 as u128) + carry;
    let r1 = sum as u64;
    let carry = sum >> 64;

    // Propagate carry to r2 - constant time version
    let sum = (r2 as u128) + carry;
    let r2 = sum as u64;
    let carry = sum >> 64;

    // Add carry to r3 - always do the addition
    let sum = (r3 as u128) + carry;
    let r3 = sum as u64;

    // x[1]²
    let square1 = (x[1] as u128) * (x[1] as u128);

    // Add to r2 and r3
    let sum = (r2 as u128) + (square1 as u64 as u128);
    let r2 = sum as u64;
    let carry = sum >> 64;

    let sum = (r3 as u128) + (square1 >> 64) + carry;
    let r3 = sum as u64;

    ([r0, r1], [r2, r3])
}

#[inline(always)]
fn bytes_to_words(bytes: [u8; 64]) -> [u64; 8] {
    let mut words = [0u64; 8];
    for (i, chunk) in bytes.chunks_exact(8).enumerate() {
        words[i] = u64::from_le_bytes(chunk.try_into().unwrap());
    }
    words
}

#[inline(always)]
fn reduce_limbs(result: [u64; 8], c_lo: u64, c_hi: u64, modulus_limbs: &'static [Limb; 4]) -> U256 {
    let r3 = result[3];
    let r4 = result[4];
    let r5 = result[5];
    let r6 = result[6];
    let r7 = result[7];

    let high257 = [
        (r4 << 1) | ((r3 >> 63) & 1),
        (r5 << 1) | (r4 >> 63),
        (r6 << 1) | (r5 >> 63),
        (r7 << 1) | (r6 >> 63),
    ];

    let bit_256 = r7 >> 63;
    let mut acc = [result[0], result[1], result[2], r3 & 0x7FFFFFFFFFFFFFFF];
    let mut overflow = [0u64; 4];

    // Multiply high257 by c_lo
    let mut carry = 0u64;
    for i in 0..4 {
        let (c, prod) = muladdcarry(high257[i], c_lo, acc[i], carry);
        acc[i] = prod;
        carry = c;
    }

    overflow[0] = carry;

    // Multiply high257 by c_hi (shifted by 1 position)
    carry = 0;
    for i in 0..4 {
        if i + 1 < 4 {
            let (c, prod) = muladdcarry(high257[i], c_hi, acc[i + 1], carry);
            acc[i + 1] = prod;
            carry = c;
        } else {
            // i + 1 >= 4, so it goes to overflow
            let (c, prod) = muladdcarry(high257[i], c_hi, overflow[i + 1 - 4], carry);
            overflow[i + 1 - 4] = prod;
            carry = c;
        }
    }

    // Final carry goes to overflow[1]
    overflow[1] = overflow[1].wrapping_add(carry);
    overflow[0] = overflow[0].wrapping_add(c_lo & bit_256.wrapping_neg());

    // Second reduction for overflow
    // overflow represents multiples of 2^256 ≡ 2c (mod p)
    let c_doubled_lo = c_lo << 1;
    let c_doubled_hi = (c_hi << 1) | (c_lo >> 63);

    carry = 0;
    for i in 0..4 {
        let (c, prod) = muladdcarry(overflow[i], c_doubled_lo, acc[i], carry);
        acc[i] = prod;
        carry = c;
    }

    // Now multiply overflow by c_doubled_hi (shifted by 1 position)
    carry = 0;
    for i in 0..3 {
        let (c, prod) = muladdcarry(overflow[i], c_doubled_hi, acc[i + 1], carry);
        acc[i + 1] = prod;
        carry = c;
    }

    // For constant time, do one more reduction iteration
    // Multiply by c_doubled_lo
    let (c0, prod0) = muladdcarry(carry, c_doubled_lo, acc[0], 0);
    acc[0] = prod0;

    // Multiply by c_doubled_hi (shifted by 1)
    let (c1, prod1) = muladdcarry(carry, c_doubled_hi, acc[1], c0);
    acc[1] = prod1;

    // Propagate remaining carries
    acc[2] = acc[2].wrapping_add(c1);

    // Subtract modulus with borrow
    let mut reduced = [0u64; 4];
    let mut borrow = 0u64;

    for i in 0..4 {
        let (diff, b1) = acc[i].overflowing_sub(modulus_limbs[i].0);
        let (diff2, b2) = diff.overflowing_sub(borrow);
        reduced[i] = diff2;
        borrow = (b1 | b2) as u64;
    }

    // Conditional select
    let select_reduced = (borrow == 0) as u64;
    let mask = select_reduced.wrapping_neg();

    for i in 0..4 {
        acc[i] = (acc[i] & !mask) | (reduced[i] & mask);
    }

    U256::from_words(acc)
}

mod helios {
    use super::*;
    use subtle::ConditionallyNegatable;

    pub const HELIOS_C_LO: u64 = 19u64;
    pub const HELIOS_C_HI: u64 = 0u64;

    const HELIOS_MODULUS_STR: &str =
        "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed";

    // Square root of -1.
    // Formula from RFC-8032 (modp_sqrt_m1/sqrt8k5 z)
    // 2 ** ((MODULUS - 1) // 4) % MODULUS
    pub const HELIOS_SQRT_M1_MAGIC: HeliosField = HeliosField(U256::from_be_hex(
        "2b8324804fc1df0b2b4d00993dfbd7a72f431806ad2fe478c4ee1b274a0ea0b0",
    ));

    #[derive(Clone, Copy, PartialEq, Eq, Default, Debug)]
    #[repr(C)]
    pub struct HeliosField(pub(crate) U256);

    field!(
        HeliosField,
        HELIOS_MODULUS_STR,
        HELIOS_C_LO,
        HELIOS_C_HI,
        2,
        2,
        "2b8324804fc1df0b2b4d00993dfbd7a72f431806ad2fe478c4ee1b274a0ea0b0",
        "0000000000000000000000000000000000000000000000000000000000000010",
    );

    impl DefaultIsZeroes for HeliosField {}

    impl HeliosField {
        // (p + 3) / 8
        pub const MOD_3_8: HeliosField = HeliosField(
            MODULUS
                .saturating_add(&U256::from_u8(3))
                .wrapping_div(&U256::from_u8(8)),
        );

        // (p + 3) / 8 - 1 = (p - 5) / 8
        const MOD_5_8: HeliosField = HeliosField(
            MODULUS
                .saturating_sub(&U256::from_u8(5))
                .wrapping_div(&U256::from_u8(8)),
        );

        pub fn sqrt(&self) -> CtOption<HeliosField> {
            let tv1 = self.pow(Self::MOD_3_8);
            let tv2 = tv1 * HELIOS_SQRT_M1_MAGIC;
            let candidate = Self::conditional_select(&tv2, &tv1, tv1.square().ct_eq(self));
            CtOption::new(candidate, candidate.square().ct_eq(self))
        }

        pub fn sqrt_ratio(u: &Self, v: &Self) -> (Choice, Self) {
            let i = HELIOS_SQRT_M1_MAGIC;

            let u = *u;
            let v = *v;

            let v3 = v.square() * v;
            let v7 = v3.square() * v;
            let mut r = (u * v3) * (u * v7).pow(Self::MOD_5_8);

            let check = v * r.square();
            let correct_sign = check.ct_eq(&u);
            let flipped_sign = check.ct_eq(&(-u));
            let flipped_sign_i = check.ct_eq(&((-u) * i));

            r.conditional_assign(&(r * i), flipped_sign | flipped_sign_i);

            let r_is_negative = r.is_odd();
            r.conditional_negate(r_is_negative);

            (correct_sign | flipped_sign, r)
        }
    }

    #[test]
    fn test_sqrt_m1() {
        assert_eq!(
            HELIOS_SQRT_M1_MAGIC,
            HeliosField(U256::from_u8(2u8)).pow(HeliosField(
                (HeliosField::ZERO - HeliosField::ONE)
                    .0
                    .wrapping_div(&U256::from_u8(4u8)),
            ))
        );
    }

    #[test]
    fn test_helios_field() {
        ff_group_tests::prime_field::test_prime_field_bits::<_, HeliosField>(&mut rand_core::OsRng);
    }
}
pub use helios::HeliosField;

mod selene {
    use super::*;
    use ff::helpers::sqrt_ratio_generic;

    const SELENE_MODULUS_STR: &str =
        "7fffffffffffffffffffffffffffffffbf7f782cb7656b586eb6d2727927c79f";

    /// For q = 7fffffffffffffffffffffffffffffffbf7f782cb7656b586eb6d2727927c79f
    /// c = 2^256 - 2*q
    pub const SELENE_C_LO: u64 = 0x91492d8d86d83861;
    pub const SELENE_C_HI: u64 = 0x408087d3489a94a7;

    /// The field novel to Helios/Selene - using Crandall reduction
    #[derive(Clone, Copy, PartialEq, Eq, Default, Debug)]
    #[repr(C)]
    pub struct SeleneField(pub(crate) U256);

    impl DefaultIsZeroes for SeleneField {}

    field!(
        SeleneField,
        SELENE_MODULUS_STR,
        SELENE_C_LO,
        SELENE_C_HI,
        5,
        1,
        "7fffffffffffffffffffffffffffffffbf7f782cb7656b586eb6d2727927c79e",
        "0000000000000000000000000000000000000000000000000000000000000019",
    );

    impl SeleneField {
        pub const MOD_1_4: SeleneField = SeleneField(
            MODULUS
                .saturating_add(&U256::ONE)
                .wrapping_div(&U256::from_u8(4)),
        );

        pub fn sqrt(&self) -> CtOption<Self> {
            let res = self.pow(Self::MOD_1_4);
            CtOption::new(res, res.square().ct_eq(self))
        }

        pub fn sqrt_ratio(num: &Self, div: &Self) -> (Choice, Self) {
            sqrt_ratio_generic(num, div)
        }
    }

    #[test]
    fn test_selene_field() {
        ff_group_tests::prime_field::test_prime_field_bits::<_, SeleneField>(&mut rand_core::OsRng);
    }
}
pub use selene::SeleneField;
