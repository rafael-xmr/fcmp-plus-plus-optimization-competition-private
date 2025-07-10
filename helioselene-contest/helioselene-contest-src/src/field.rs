use zeroize::DefaultIsZeroes;

use crypto_bigint::{Encoding, Limb, Zero, U256};

const MODULUS_STR: &str = "7fffffffffffffffffffffffffffffffbf7f782cb7656b586eb6d2727927c79f";

/// c = 2^256 - 2*q
pub const _C: u128 = 0x81010fa69135294f22925b1b0db070c2;

/// u = 2^255 - q
pub const _U: u128 = 0x408087d3489a94a791492d8d86d83861;

pub const U_LO64: u64 = 0x91492d8d86d83861;
pub const U_LO64_SHF: u64 = U_LO64 << 1;
pub const U_HI64: u64 = 0x408087d3489a94a7;
pub const U_HI64_SHF: u64 = (U_HI64 << 1) | (U_LO64 >> 63);

/// The field novel to Helios/Selene.
#[derive(Clone, Copy, PartialEq, Eq, Default, Debug)]
#[repr(C)]
pub struct HelioseleneField(pub(crate) U256);

impl DefaultIsZeroes for HelioseleneField {}

pub(crate) const MODULUS: U256 = U256::from_be_hex(MODULUS_STR);

#[cfg(target_pointer_width = "64")]
const fn limbs_to_u64_array<const N: usize>(limbs: &[Limb; N]) -> [u64; 4] {
    [limbs[0].0, limbs[1].0, limbs[2].0, limbs[3].0]
}

#[cfg(target_pointer_width = "32")]
const fn limbs_to_u64_array<const N: usize>(limbs: &[Limb; N]) -> [u64; 4] {
    [
        limbs[0].0 as u64 | ((limbs[1].0 as u64) << 32),
        limbs[2].0 as u64 | ((limbs[3].0 as u64) << 32),
        limbs[4].0 as u64 | ((limbs[5].0 as u64) << 32),
        limbs[6].0 as u64 | ((limbs[7].0 as u64) << 32),
    ]
}

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

pub const MODULUS_LIMBS: [u64; 4] = limbs_to_u64_array(&MODULUS.as_limbs());

pub const MOD_1_4: HelioseleneField = HelioseleneField(
    MODULUS
        .saturating_add(&U256::ONE)
        .wrapping_div(&U256::from_u8(4)),
);

/// Computes `x + y`, returning the result and a carry.
#[inline(always)]
const fn add(x: u64, y: u64) -> (u64, u64) {
    let (sum, carry) = x.overflowing_add(y);
    (sum, carry as u64)
}

/// Computes `x + y`, returning the result and a carry.
#[inline(always)]
const fn addcarry(x: u64, y: u64, z: u64) -> (u64, u64) {
    let (sum, carry) = x.overflowing_add(y);
    let (sum, carry2) = sum.overflowing_add(z);
    (sum, carry as u64 | (carry2 as u64))
}

/// Computes `x * y + z`, returning the 128-bit result as two 64-bit words (hi, lo).
#[inline(always)]
const fn muladd(x: u64, y: u64, z: u64) -> (u64, u64) {
    let res = (x as u128).wrapping_mul(y as u128).wrapping_add(z as u128);
    (res as u64, (res >> 64) as u64)
}

/// Computes `x - y - z` (where `z` is a borrow), returning the result and a borrow.
#[inline(always)]
const fn subborrow(x: u64, y: u64, z: u64) -> (u64, u64) {
    let (diff, b1) = x.overflowing_sub(y);
    let (diff, b2) = diff.overflowing_sub(z);
    (diff, (b1 | b2) as u64)
}

/// Computes `x * y + z + w` (where `w` is a carry), returning the 128-bit result as two 64-bit words (hi, lo).
#[inline(always)]
const fn muladdcarry(x: u64, y: u64, z: u64, w: u64) -> (u64, u64) {
    let res = (x as u128)
        .wrapping_mul(y as u128)
        .wrapping_add(z as u128)
        .wrapping_add(w as u128);
    (res as u64, (res >> 64) as u64)
}

/// Computes `a * b`, returning the 128-bit result as two 64-bit words (hi, lo).
#[inline(always)]
fn mulwide(a: u64, b: u64) -> (u64, u64) {
    let product = (a as u128).wrapping_mul(b as u128);
    (product as u64, (product >> 64) as u64)
}

/// Computes the 256-bit product of two 128-bit integers.
/// Input and output are represented as `[lo, hi]` arrays of 64-bit words.
#[inline(always)]
fn mul_wide(x: [u64; 2], y: [u64; 2]) -> ([u64; 2], [u64; 2]) {
    let mut result = [0u64; 4];

    for i in 0..2 {
        let mut carry = 0u64;
        for j in 0..2 {
            let k = i + j;
            (result[k], carry) = muladdcarry(x[i], y[j], result[k], carry);
        }
        result[i + 2] = carry;
    }

    ([result[0], result[1]], [result[2], result[3]])
}

/// Computes the 256-bit square of a 128-bit integer.
/// Input and output are represented as `[lo, hi]` arrays of 64-bit words.
#[inline(always)]
fn square_wide(x: [u64; 2]) -> ([u64; 2], [u64; 2]) {
    // x[0]²
    let (r0_lo, r0_hi) = mulwide(x[0], x[0]);

    // x[0] * x[1]
    let (cross_lo, cross_hi) = mulwide(x[0], x[1]);

    // Add doubled cross product to middle words
    let (r1, carry1) = add(r0_hi, cross_lo << 1);
    let (r2, carry2) = add((cross_hi << 1) | (cross_lo >> 63), carry1 as u64);

    // x[1]²
    let (sq1_lo, sq1_hi) = mulwide(x[1], x[1]);

    // Add square1's low part to r2
    let (r2_final, carry3) = add(r2, sq1_lo);

    // Add remaining parts to r3
    let r3 = sq1_hi
        .wrapping_add(cross_hi >> 63)
        .wrapping_add(carry2)
        .wrapping_add(carry3);

    ([r0_lo, r1], [r2_final, r3])
}

/// Converts a 64-byte little-endian array into eight 64-bit words.
#[inline(always)]
fn bytes_to_words(bytes: [u8; 64]) -> [u64; 8] {
    let mut words = [0u64; 8];
    for (i, chunk) in bytes.chunks_exact(8).enumerate() {
        words[i] = u64::from_le_bytes(chunk.try_into().unwrap());
    }
    words
}

#[inline(always)]
fn reduce_crandall_full(x: [u64; 8]) -> U256 {
    reduce_crandall_final(reduce_512_lazy(x))
}

/// Performs a partial reduction of a 512-bit integer modulo a 256-bit Crandall prime `p`.
///
/// This function is a highly optimized implementation for a prime of the form `p = 2^m - c`.
/// The core principle of Crandall reduction is based on the congruence: `2^m ≡ c (mod p)`.
///
/// For a 512-bit input `x`, we can split it at `m=255` bits: `x = q * 2^255 + r`,
/// where `q` is the high 257 bits and `r` is the low 255 bits.
/// The reduction is then: `x ≡ q * U + r (mod p)`, where `U = 2^255 - p`.
///
/// This function computes `q * U + r`. The result is a "partial" reduction, meaning it may
/// still be slightly larger than `p`. A final reduction step is required.
#[inline(always)]
fn reduce_512_lazy(x: [u64; 8]) -> [u64; 4] {
    // q1 = x >> 255 (257 bits)
    let mut q1 = [0u64; 5];
    for i in 0..4 {
        q1[i] = (x[i + 4] << 1) | (x[i + 3] >> 63);
    }
    q1[4] = x[7] >> 63;

    // r1 = x mod 2^255 (255 bits)
    let mut r1 = [x[0], x[1], x[2], x[3]];
    r1[3] &= 0x7FFFFFFFFFFFFFFF;

    let mut y = [0u64; 8];

    // y = q1 * U + r1
    // This computes `q1 * U_LO64` and adds it to `r1`.
    let (y0, mut carry) = muladd(q1[0], U_LO64, r1[0]);
    y[0] = y0;
    for i in 1..4 {
        (y[i], carry) = muladdcarry(q1[i], U_LO64, r1[i], carry);
    }
    (y[4], carry) = muladd(q1[4], U_LO64, carry);
    y[5] = carry;

    // This computes `q1 * U_HI64` and adds it to the intermediate `y`.
    let (y1, mut carry) = muladd(q1[0], U_HI64, y[1]);
    y[1] = y1;
    for i in 1..5 {
        (y[i + 1], carry) = muladdcarry(q1[i], U_HI64, y[i + 1], carry);
    }
    y[6] = carry;

    // At this point, we have a ~385 bit number in y0..y6

    // q2 = y >> 255 (130 bits)
    let mut q2 = [0u64; 3];
    for i in 0..3 {
        q2[i] = (y[i + 4] << 1) | (y[i + 3] >> 63);
    }

    // r2 = y mod 2^255 (255 bits)
    let mut r2 = [y[0], y[1], y[2], y[3]];
    r2[3] &= 0x7FFFFFFFFFFFFFFF;

    let mut z = [0u64; 4];

    // z = q2 * U + r2
    // This computes `q2 * U_LO64` and adds it to `r2`.
    let (z0, mut carry) = muladd(q2[0], U_LO64, r2[0]);
    z[0] = z0;
    for i in 1..3 {
        (z[i], carry) = muladdcarry(q2[i], U_LO64, r2[i], carry);
    }
    // q2 has no 4th limb
    (z[3], carry) = add(r2[3], carry);
    let z4 = carry;

    // This computes `q2 * U_HI64` and adds it to the intermediate `z`.
    let (z1, mut carry2) = muladd(q2[0], U_HI64, z[1]);
    z[1] = z1;
    for i in 1..3 {
        (z[i + 1], carry2) = muladdcarry(q2[i], U_HI64, z[i + 1], carry2);
    }
    (_, carry2) = add(z4, carry2);
    let mut z5 = carry2;

    // Final accumulation of carries. z5 is at most 1.
    z5 = z5 + carry;

    (z[2], carry) = add(z[2], z5);
    (z[3], _) = add(z[3], carry);

    z
}

/// Performs the final step of a Crandall reduction.
/// It reduces an input `a` (which is known to be slightly larger than the modulus)
/// to the range `[0, p-1]` by conditionally subtracting the modulus.
#[inline(always)]
fn reduce_crandall_final(a: [u64; 4]) -> U256 {
    let mut borrow = 0u64;
    let mut s = [0u64; 4];

    for i in 0..4 {
        (s[i], borrow) = subborrow(a[i], MODULUS_LIMBS[i], borrow);
    }

    // If there was no borrow (a >= p), the result is `s`.
    // Otherwise (a < p), the result is `a`.
    let no_borrow_mask = ((borrow == 0) as u64).wrapping_neg();
    let mut r = [0u64; 4];
    for i in 0..4 {
        r[i] = (a[i] & !no_borrow_mask) | (s[i] & no_borrow_mask);
    }

    u256_from_u64_array(r)
}

/// Performs field addition `x + y mod p`.
#[inline(always)]
fn helioselene_add(x: U256, y: U256, lazy_reduce: bool) -> U256 {
    let x_limbs = limbs_to_u64_array(x.as_limbs());
    let y_limbs = limbs_to_u64_array(y.as_limbs());

    // Standard addition with carry
    let mut r = [0u64; 4];
    let mut carry = 0u64;
    for i in 0..4 {
        (r[i], carry) = addcarry(x_limbs[i], y_limbs[i], carry);
    }

    // If there was a carry, we must add `2*c` (where `p = 2^256 - 2c`).
    // This is equivalent to `r + (2^256 - p)`.
    let mut a = [0u64; 4];
    let (a0, mut carry_a) = add(r[0], U_LO64_SHF);
    a[0] = a0;
    (a[1], carry_a) = addcarry(r[1], U_HI64_SHF, carry_a);
    for i in 2..4 {
        (a[i], carry_a) = add(r[i], carry_a);
    }

    let carry_mask = carry.wrapping_neg();
    for i in 0..4 {
        r[i] = (r[i] & !carry_mask) | (a[i] & carry_mask);
    }

    if lazy_reduce {
        return u256_from_u64_array(r);
    }

    reduce_crandall_final(r)
}

/// Performs field doubling `x + x mod p`.
#[inline(always)]
fn helioselene_double(x: U256, lazy_reduce: bool) -> U256 {
    let x_limbs = limbs_to_u64_array(x.as_limbs());

    let mut r = [0u64; 4];
    r[0] = x_limbs[0] << 1;

    // Shift left by 1 bit with carry propagation
    for i in 1..4 {
        r[i] = (x_limbs[i] << 1) | (x_limbs[i - 1] >> 63);
    }

    // Compute both with and without carry correction
    let mut a = [0u64; 4];
    let (a0, ca0) = r[0].overflowing_add(U_LO64 << 1);
    a[0] = a0;
    let mut carry = ca0 as u64;

    for i in 0..4 {
        let (a_i, ca_i) = r[i].overflowing_add((U_HI64 << 1) | (U_LO64 >> 63));
        let (a_i, ca_ib) = a_i.overflowing_add(carry);
        a[i] = a_i;
        carry = (ca_i | ca_ib) as u64;
    }

    // Select based on carry
    let carry_mask = (x_limbs[3] >> 63).wrapping_neg();
    for i in 0..4 {
        r[i] = (r[i] & !carry_mask) | (a[i] & carry_mask);
    }

    if lazy_reduce {
        return u256_from_u64_array(r);
    }

    reduce_crandall_final(r)
}

/// Performs field subtraction `x - y mod p`.
#[inline(always)]
fn helioselene_sub(x: U256, y: U256) -> U256 {
    let x_limbs = limbs_to_u64_array(x.as_limbs());
    let y_limbs = limbs_to_u64_array(y.as_limbs());

    // Standard subtraction with borrow
    let mut r = [0u64; 4];
    let mut borrow = 0u64;
    for i in 0..4 {
        (r[i], borrow) = subborrow(x_limbs[i], y_limbs[i], borrow);
    }

    // If there was a borrow, we must add the modulus back.
    let mut a = [0u64; 4];
    let mut carry = 0u64;
    for i in 0..4 {
        let (sum, c1) = r[i].overflowing_add(MODULUS_LIMBS[i]);
        let (sum, c2) = sum.overflowing_add(carry);
        a[i] = sum;
        carry = (c1 | c2) as u64;
    }

    // Constant-time select based on original borrow
    let borrow_mask = borrow.wrapping_neg();
    for i in 0..4 {
        r[i] = (r[i] & !borrow_mask) | (a[i] & borrow_mask);
    }

    u256_from_u64_array(r)
}

/// Performs field multiplication `x * y mod p`.
#[inline(always)]
fn helioselene_mul(x: U256, y: U256, lazy_reduce: bool) -> U256 {
    let x_limbs = limbs_to_u64_array(x.as_limbs());
    let y_limbs = limbs_to_u64_array(y.as_limbs());

    let mut r = [0u64; 8];
    for i in 0..4 {
        let mut carry = 0u64;
        for j in 0..4 {
            (r[i + j], carry) = muladdcarry(x_limbs[i], y_limbs[j], r[i + j], carry);
        }
        r[i + 4] = carry;
    }

    if lazy_reduce {
        return u256_from_u64_array(reduce_512_lazy(r));
    }

    reduce_crandall_full(r)
}

/// Performs field negation `-x mod p`.
#[inline(always)]
fn helioselene_neg(x: U256) -> U256 {
    let x_limbs = limbs_to_u64_array(x.as_limbs());

    // Compute `p - x`.
    let mut borrow = 0u64;
    let mut res = [0u64; 4];
    for i in 0..4 {
        (res[i], borrow) = subborrow(MODULUS_LIMBS[i], x_limbs[i], borrow);
    }

    // If x is zero, the result is zero. Otherwise it's `p - x`.
    let zero_mask = (x.is_zero().unwrap_u8() as u64).wrapping_neg();
    for i in 0..4 {
        res[i] &= !zero_mask;
    }

    u256_from_u64_array(res)
}

/// Performs field squaring `x * x mod p`.
#[inline(always)]
fn helioselene_square(x: U256, lazy_reduce: bool) -> U256 {
    let x_limbs = limbs_to_u64_array(x.as_limbs());

    // Karatsuba-style squaring to get a 512-bit result
    let (z0_lo, z0_hi) = square_wide([x_limbs[0], x_limbs[1]]);
    let (z2_lo, z2_hi) = square_wide([x_limbs[2], x_limbs[3]]);
    let (z1_lo, z1_hi) = mul_wide([x_limbs[0], x_limbs[1]], [x_limbs[2], x_limbs[3]]);

    // Combine terms: z0 + (2*z1)*2^128 + z2*2^256
    let (r2, c1) = add(z0_hi[0], z1_lo[0] << 1);
    let (r3_temp, c2) = add(z0_hi[1], z1_lo[1] << 1);
    let (r3, c3) = add(r3_temp, (z1_lo[0] >> 63) + c1);

    let (r4_temp, c4) = add(z2_lo[0], z1_hi[0] << 1);
    let (r4, c5) = add(r4_temp, (z1_lo[1] >> 63) + c2 + c3);

    let (r5_temp, c6) = add(z2_lo[1], z1_hi[1] << 1);
    let (r5, c7) = add(r5_temp, (z1_hi[0] >> 63) + c4 + c5);

    let (r6, c) = add(z2_hi[0], (z1_hi[1] >> 63) + c6 + c7);
    let r7 = z2_hi[1] + c;

    let r = [z0_lo[0], z0_lo[1], r2, r3, r4, r5, r6, r7];

    if lazy_reduce {
        return u256_from_u64_array(reduce_512_lazy(r));
    }

    reduce_crandall_full(r)
}

field!(
    HelioseleneField,
    MODULUS_STR,
    5,
    1,
    "7fffffffffffffffffffffffffffffffbf7f782cb7656b586eb6d2727927c79e",
    "0000000000000000000000000000000000000000000000000000000000000019",
);

impl HelioseleneField {
    /// Performs addition with a partial reduction. The result may not be fully reduced.
    pub fn lazy_add(&self, other: &HelioseleneField) -> HelioseleneField {
        HelioseleneField(helioselene_add(self.0, other.0, true))
    }

    /// Performs multiplication with a partial reduction. The result may not be fully reduced.
    pub fn lazy_mul(&self, other: &HelioseleneField) -> HelioseleneField {
        HelioseleneField(helioselene_mul(self.0, other.0, true))
    }

    /// Performs squaring with a partial reduction. The result may not be fully reduced.
    pub fn lazy_square(&self) -> HelioseleneField {
        HelioseleneField(helioselene_square(self.0, true))
    }

    /// Performs doubling with a partial reduction. The result may not be fully reduced.
    pub fn lazy_double(&self) -> HelioseleneField {
        HelioseleneField(helioselene_double(self.0, true))
    }

    /// Performs a final reduction on a field element.
    pub fn lazy_reduce(&self) -> HelioseleneField {
        HelioseleneField(reduce_crandall_final(limbs_to_u64_array(self.0.as_limbs())))
    }
}

#[test]
fn test_helioselene_field() {
    ff_group_tests::prime_field::test_prime_field_bits::<_, HelioseleneField>(
        &mut rand_core::OsRng,
    );
}

#[test]
fn test_calculate_c_constants() {
    // Calculate c = 2^256 - 2*MODULUS
    let c_val = (U256::ONE << 256).wrapping_sub(&(MODULUS << 1));
    assert_eq!(c_val, U256::from_u128(_C));

    // Calculate u = 2^255 - MODULUS
    let u_val = (U256::ONE << 255).wrapping_sub(&MODULUS);
    assert_eq!(u_val, U256::from_u128(_U));

    let lo = u_val & ((U256::ONE << 64).wrapping_sub(&U256::ONE));
    let hi = u_val >> 64;

    assert_eq!(lo, U256::from_u64(U_LO64));
    assert_eq!(hi, U256::from_u64(U_HI64));
}
