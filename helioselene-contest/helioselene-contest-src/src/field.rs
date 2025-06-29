use zeroize::DefaultIsZeroes;

use crypto_bigint::{Encoding, Limb, Zero, U256};

#[cfg(target_pointer_width = "64")]
fn u256_from_u64_array(arr: [u64; 4]) -> U256 {
    U256::from_words(arr)
}

#[cfg(target_pointer_width = "32")]
fn u256_from_u64_array(arr: [u64; 4]) -> U256 {
    let mut words = [0u32; 8];
    for i in 0..4 {
        words[i * 2] = arr[i] as u32;
        words[i * 2 + 1] = (arr[i] >> 32) as u32;
    }
    U256::from_words(words)
}

#[cfg(target_pointer_width = "64")]
fn limbs_to_u64_array<const N: usize>(limbs: &[Limb; N]) -> [u64; 4] {
    [limbs[0].0, limbs[1].0, limbs[2].0, limbs[3].0]
}

#[cfg(target_pointer_width = "32")]
fn limbs_to_u64_array<const N: usize>(limbs: &[Limb; N]) -> [u64; 4] {
    [
        limbs[0].0 as u64 | ((limbs[1].0 as u64) << 32),
        limbs[2].0 as u64 | ((limbs[3].0 as u64) << 32),
        limbs[4].0 as u64 | ((limbs[5].0 as u64) << 32),
        limbs[6].0 as u64 | ((limbs[7].0 as u64) << 32),
    ]
}

#[inline(always)]
const fn muladd(x: u64, y: u64, z: u64) -> (u64, u64) {
    let res = (x as u128).wrapping_mul(y as u128).wrapping_add(z as u128);
    ((res >> 64) as u64, res as u64)
}

#[inline(always)]
const fn muladdcarry(x: u64, y: u64, z: u64, w: u64) -> (u64, u64) {
    let res = (x as u128)
        .wrapping_mul(y as u128)
        .wrapping_add(z as u128)
        .wrapping_add(w as u128);
    ((res >> 64) as u64, res as u64)
}

#[inline(always)]
fn mul_wide(x: [u64; 2], y: [u64; 2]) -> ([u64; 2], [u64; 2]) {
    let mut result = [0u64; 4];

    for i in 0..2 {
        let mut carry = 0u64;
        for j in 0..2 {
            let k = i + j;
            let (c, res) = muladdcarry(x[i], y[j], result[k], carry);
            result[k] = res;
            carry = c;
        }
        result[i + 2] = carry;
    }

    ([result[0], result[1]], [result[2], result[3]])
}

#[inline(always)]
fn square_wide(x: [u64; 2]) -> ([u64; 2], [u64; 2]) {
    // x[0]²
    let r0 = (x[0] as u128) * (x[0] as u128);

    // x[0] * x[1]
    let cross_prod = (x[0] as u128) * (x[1] as u128);
    // Double the cross product - need to handle potential overflow
    let doubled_low = cross_prod << 1;

    // Add high part of x[0]² to r1
    let r1 = (doubled_low & 0xFFFFFFFFFFFFFFFF) + (r0 >> 64);

    // Propagate carry to r2
    let r2 = (doubled_low >> 64) + (r1 >> 64);

    // x[1]²
    let square1 = (x[1] as u128) * (x[1] as u128);

    // Add square1's low part to r2
    let r2_sum = r2 as u64 as u128 + (square1 & 0xFFFFFFFFFFFFFFFF);

    (
        [r0 as u64, r1 as u64],
        [
            r2_sum as u64,
            // Add carry to r3 - always do the addition
            // Add to r2 and r3
            ((((cross_prod >> 127) + (r2 >> 64)) as u64) as u128 + (square1 >> 64) + (r2_sum >> 64))
                as u64,
        ],
    )
}

#[inline(always)]
fn bytes_to_words(bytes: [u8; 64]) -> [u64; 8] {
    let mut words = [0u64; 8];
    for (i, chunk) in bytes.chunks_exact(8).enumerate() {
        words[i] = u64::from_le_bytes(chunk.try_into().unwrap());
    }
    words
}

// https://en.wikipedia.org/wiki/Barrett_reduction tailored for F255
#[inline(always)]
fn reduce_limbs(result: [u64; 8], c_lo: u64, c_hi: u64, modulus_limbs: &'static [u64; 4]) -> U256 {
    // Extract high 257 bits (bits 255-511)
    let mut high257 = [0u64; 4];
    for i in 0..4 {
        high257[i] = (result[i + 4] << 1) | (result[i + 3] >> 63);
    }

    // First reduction: multiply high257 by c
    let mut acc = [0u64; 4];
    let mut carry = 0u64;

    // Multiply high257 by c_lo
    for i in 0..4 {
        let input = if i < 3 {
            result[i]
        } else {
            result[3] & 0x7FFFFFFFFFFFFFFF
        };
        let (c, a) = muladdcarry(high257[i], c_lo, input, carry);
        acc[i] = a;
        carry = c;
    }

    // Multiply high257 by c_hi (shifted by 1 position)
    let mut overflow = [carry, 0u64];
    carry = 0u64;

    for i in 0..4 {
        if i > 0 {
            let (c, a) = muladdcarry(high257[i - 1], c_hi, acc[i], carry);
            acc[i] = a;
            carry = c;
        }
    }

    // Handle final multiplication
    let (overflow1, prod3) = muladdcarry(high257[3], c_hi, overflow[0], carry);
    overflow[0] = prod3.wrapping_add(c_lo & (result[7] >> 63).wrapping_neg());
    overflow[1] = overflow1;

    // Second reduction for overflow
    // Multiply overflow by c_doubled
    let c_doubled_lo = c_lo << 1;
    carry = 0u64;

    for i in 0..2 {
        let (c, a) = muladdcarry(overflow[i], c_doubled_lo, acc[i], carry);
        acc[i] = a;
        carry = c;
    }

    let (acc2, c) = acc[2].overflowing_add(carry);
    acc[2] = acc2;
    let (acc3, _) = acc[3].overflowing_add(c as u64);
    acc[3] = acc3;

    // Multiply overflow by c_doubled_hi (shifted)
    let c_doubled_hi = (c_hi << 1) | (c_lo >> 63);
    carry = 0u64;

    for i in 0..2 {
        if i < 1 {
            let (c, a) = muladdcarry(overflow[0], c_doubled_hi, acc[1], carry);
            acc[1] = a;
            carry = c;
        } else {
            let (c, a) = muladdcarry(overflow[1], c_doubled_hi, acc[2], carry);
            acc[2] = a;
            carry = c;
        }
    }

    let (acc3, c2) = acc[3].overflowing_add(carry);
    acc[3] = acc3;

    // Final reduction iteration
    let (c0, acc0) = muladd(c2 as u64, c_doubled_lo, acc[0]);
    acc[0] = acc0;
    let (c1, acc1) = muladdcarry(c2 as u64, c_doubled_hi, acc[1], c0);
    acc[1] = acc1;
    acc[2] = acc[2].wrapping_add(c1);

    // Subtract modulus with borrow
    let mut diff = [0u64; 4];
    let mut borrow = 0u64;

    for i in 0..4 {
        let (d, b1) = acc[i].overflowing_sub(modulus_limbs[i]);
        let (d, b2) = d.overflowing_sub(borrow);
        diff[i] = d;
        borrow = (b1 | b2) as u64;
    }

    // Constant-time selection
    let mask = ((borrow == 0) as u64).wrapping_neg();
    let mut result_words = [0u64; 4];

    for i in 0..4 {
        result_words[i] = (acc[i] & !mask) | (diff[i] & mask);
    }

    u256_from_u64_array(result_words)
}

#[inline(always)]
fn f255_add(x: U256, y: U256, c_lo: u64, c_hi: u64, modulus_limbs: &'static [u64; 4]) -> U256 {
    let x_limbs = limbs_to_u64_array(x.as_limbs());
    let y_limbs = limbs_to_u64_array(y.as_limbs());

    // Addition with carry propagation
    let mut r = [0u64; 4];
    let mut carry = 0u64;

    for i in 0..4 {
        let (sum, c1) = x_limbs[i].overflowing_add(y_limbs[i]);
        let (sum, c2) = sum.overflowing_add(carry);
        r[i] = sum;
        carry = (c1 | c2) as u64;
    }

    // Compute both with and without carry correction
    let mut a = [0u64; 4];

    // Add 2*c if there was overflow
    let (a0, ca0) = r[0].overflowing_add(c_lo << 1);
    a[0] = a0;
    let mut carry_a = ca0 as u64;

    let (a1, ca1) = r[1].overflowing_add((c_hi << 1) | (c_lo >> 63));
    let (a1, ca1b) = a1.overflowing_add(carry_a);
    a[1] = a1;
    carry_a = (ca1 | ca1b) as u64;

    for i in 2..4 {
        let (sum, c) = r[i].overflowing_add(carry_a);
        a[i] = sum;
        carry_a = c as u64;
    }

    // Constant time select based on carry
    let carry_mask = carry.wrapping_neg();
    for i in 0..4 {
        r[i] = (r[i] & !carry_mask) | (a[i] & carry_mask);
    }

    // Full reduction - subtract modulus
    let mut s = [0u64; 4];
    let mut borrow = 0u64;

    for i in 0..4 {
        let (diff, b1) = r[i].overflowing_sub(modulus_limbs[i]);
        let (diff, b2) = diff.overflowing_sub(borrow);
        s[i] = diff;
        borrow = (b1 | b2) as u64;
    }

    // Constant time select reduced if no borrow
    let no_borrow_mask = ((borrow == 0) as u64).wrapping_neg();
    let mut result = [0u64; 4];

    for i in 0..4 {
        result[i] = (r[i] & !no_borrow_mask) | (s[i] & no_borrow_mask);
    }

    u256_from_u64_array(result)
}

#[inline(always)]
fn f255_sub(x: U256, y: U256, modulus_limbs: &'static [u64; 4]) -> U256 {
    let x_limbs = limbs_to_u64_array(x.as_limbs());
    let y_limbs = limbs_to_u64_array(y.as_limbs());

    // Subtraction with borrow propagation
    let mut r = [0u64; 4];
    let mut borrow = 0u64;

    for i in 0..4 {
        let (diff, b1) = x_limbs[i].overflowing_sub(y_limbs[i]);
        let (diff, b2) = diff.overflowing_sub(borrow);
        r[i] = diff;
        borrow = (b1 | b2) as u64;
    }

    // Add modulus if there was a borrow
    let mut a = [0u64; 4];
    let mut carry = 0u64;

    for i in 0..4 {
        let (sum, c1) = r[i].overflowing_add(modulus_limbs[i]);
        let (sum, c2) = sum.overflowing_add(carry);
        a[i] = sum;
        carry = (c1 | c2) as u64;
    }

    // Select based on borrow
    let borrow_mask = borrow.wrapping_neg();
    let mut result = [0u64; 4];

    for i in 0..4 {
        result[i] = (r[i] & !borrow_mask) | (a[i] & borrow_mask);
    }

    u256_from_u64_array(result)
}

#[inline(always)]
fn f255_mul(x: U256, y: U256, c_lo: u64, c_hi: u64, modulus_limbs: &'static [u64; 4]) -> U256 {
    let x_limbs = limbs_to_u64_array(x.as_limbs());
    let y_limbs = limbs_to_u64_array(y.as_limbs());

    let mut t = [0u64; 8];

    for i in 0..4 {
        let mut carry = 0u64;
        for j in 0..4 {
            let (hi, lo) = muladd(x_limbs[i], y_limbs[j], t[i + j]);
            let (sum, c) = lo.overflowing_add(carry);
            t[i + j] = sum;
            carry = hi.wrapping_add(c as u64);
        }
        t[i + 4] = carry;
    }

    reduce_limbs(t, c_lo, c_hi, modulus_limbs)
}

#[inline(always)]
fn f255_neg(x: U256, modulus_limbs: &'static [u64; 4]) -> U256 {
    let x_limbs = limbs_to_u64_array(x.as_limbs());

    let mut b = 0u64;
    let mut res = [0u64; 4];

    for i in 0..4 {
        let (r, b1) = modulus_limbs[i].overflowing_sub(x_limbs[i]);
        let (r, b2) = r.overflowing_sub(b);
        res[i] = r;
        b = (b1 | b2) as u64;
    }

    let zero_mask = (x.is_zero().unwrap_u8() as u64).wrapping_neg();

    for i in 0..4 {
        res[i] &= !zero_mask;
    }

    u256_from_u64_array(res)
}

#[inline(always)]
fn f255_square(x: U256, c_lo: u64, c_hi: u64, modulus_limbs: &'static [u64; 4]) -> U256 {
    let x_limbs = limbs_to_u64_array(x.as_limbs());

    // Square low part: z0 = x_lo²
    let (z0_lo, z0_hi) = square_wide([x_limbs[0], x_limbs[1]]);

    // Square high part: z2 = x_hi²
    let (z2_lo, z2_hi) = square_wide([x_limbs[2], x_limbs[3]]);

    // Compute x_lo * x_hi for middle term (will be doubled)
    let (z1_lo, z1_hi) = mul_wide([x_limbs[0], x_limbs[1]], [x_limbs[2], x_limbs[3]]);

    // Add 2*z1[0] to r2
    let (r2, c1) = z0_hi[0].overflowing_add(z1_lo[0] << 1);

    // Add 2*z1[1] to r3
    let (r3_temp, c2) = z0_hi[1].overflowing_add(z1_lo[1] << 1);
    let (r3, c3) = r3_temp.overflowing_add((z1_lo[0] >> 63) + (c1 as u64));

    // Add 2*z1[2] to r4
    let (r4_temp, c4) = z2_lo[0].overflowing_add(z1_hi[0] << 1);
    let (r4, c5) = r4_temp.overflowing_add((z1_lo[1] >> 63) + (c2 as u64) + (c3 as u64));

    // Add 2*z1[3] to r5
    let (r5_temp, c6) = z2_lo[1].overflowing_add(z1_hi[1] << 1);
    let (r5, c7) = r5_temp.overflowing_add((z1_hi[0] >> 63) + (c4 as u64) + (c5 as u64));

    // Propagate remaining carry
    let (r6, c) = z2_hi[0].overflowing_add((z1_hi[1] >> 63) + (c6 as u64) + (c7 as u64));

    reduce_limbs(
        [
            z0_lo[0],
            z0_lo[1],
            r2,
            r3,
            r4,
            r5,
            r6,
            z2_hi[1].wrapping_add((c as u64).wrapping_neg() & 1),
        ],
        c_lo,
        c_hi,
        modulus_limbs,
    )
}

#[inline(always)]
fn f255_double(x: U256, c_lo: u64, c_hi: u64, modulus_limbs: &'static [u64; 4]) -> U256 {
    let x_limbs = limbs_to_u64_array(x.as_limbs());

    let mut r = [0u64; 4];
    r[0] = x_limbs[0] << 1;

    // Shift left by 1 bit with carry propagation
    for i in 1..4 {
        r[i] = (x_limbs[i] << 1) | (x_limbs[i - 1] >> 63);
    }

    // Compute both with and without carry correction
    let mut a = [0u64; 4];
    let (a0, ca0) = r[0].overflowing_add(c_lo << 1);
    a[0] = a0;
    let mut carry = ca0 as u64;

    for i in 0..4 {
        let (a_i, ca_i) = r[i].overflowing_add((c_hi << 1) | (c_lo >> 63));
        let (a_i, ca_ib) = a_i.overflowing_add(carry);
        a[i] = a_i;
        carry = (ca_i | ca_ib) as u64;
    }

    // Select based on carry
    let carry_mask = (x_limbs[3] >> 63).wrapping_neg();
    for i in 0..4 {
        r[i] = (r[i] & !carry_mask) | (a[i] & carry_mask);
    }

    let mut s = [0u64; 4];
    let mut b = 0u64;

    for i in 0..4 {
        let (diff, b1) = r[i].overflowing_sub(modulus_limbs[i]);
        let (diff, b2) = diff.overflowing_sub(b);
        s[i] = diff;
        b = (b1 | b2) as u64;
    }

    // Select reduced if no borrow
    let no_borrow_mask = ((b == 0) as u64).wrapping_neg();
    for i in 0..4 {
        r[i] = (r[i] & !no_borrow_mask) | (s[i] & no_borrow_mask);
    }

    u256_from_u64_array(r)
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
