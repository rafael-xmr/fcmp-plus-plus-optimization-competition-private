use zeroize::DefaultIsZeroes;

use crypto_bigint::{Encoding, Limb, Zero, U256};

const MODULUS_STR: &str = "7fffffffffffffffffffffffffffffffbf7f782cb7656b586eb6d2727927c79f";

const INVERTER: BYInverter = BYInverter::new(
    &MODULUS_LIMBS,
    &[
        0x0000000000000001,
        0x0000000000000000,
        0x0000000000000000,
        0x0000000000000000,
    ],
);

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

/// Performs modular inversion using the Bernstein-Yang algorithm
#[inline(always)]
fn helioselene_inverse(x: U256) -> U256 {
    let x_limbs = limbs_to_u64_array(x.as_limbs());

    u256_from_u64_array(INVERTER.invert(&x_limbs))
}

/// Big signed (B * L)-bit integer type, whose variables store
/// numbers in the two's complement code as arrays of B-bit chunks.
/// The ordering of the chunks in these arrays is little-endian.
/// The arithmetic operations for this type are wrapping ones.
#[derive(Clone)]
struct CInt<const B: usize, const L: usize>(pub [u64; L]);

impl<const B: usize, const L: usize> CInt<B, L> {
    /// Mask, in which the B lowest bits are 1 and only they
    pub const MASK: u64 = u64::MAX >> (64 - B);

    /// Representation of -1
    pub const MINUS_ONE: Self = Self([Self::MASK; L]);

    /// Representation of 0
    pub const ZERO: Self = Self([0; L]);

    /// Returns the result of applying B-bit right
    /// arithmetical shift to the current number
    pub fn shift(&self) -> Self {
        let mut data = [0; L];

        let neg_mask = (self.is_negative() as u64).wrapping_neg();
        data[L - 1] = Self::MASK & neg_mask;

        data[..L - 1].copy_from_slice(&self.0[1..]);
        Self(data)
    }

    /// Returns the lowest B bits of the current number
    pub fn lowest(&self) -> u64 {
        self.0[0]
    }

    /// Returns "true" iff the current number is negative
    pub fn is_negative(&self) -> bool {
        self.0[L - 1] > (Self::MASK >> 1)
    }
}

impl<const B: usize, const L: usize> PartialEq for CInt<B, L> {
    fn eq(&self, other: &Self) -> bool {
        let mut diff = 0u64;
        for i in 0..L {
            diff |= self.0[i] ^ other.0[i];
        }
        diff == 0
    }
}

impl<const B: usize, const L: usize> Add for &CInt<B, L> {
    type Output = CInt<B, L>;
    fn add(self, other: Self) -> Self::Output {
        let (mut data, mut carry) = ([0; L], 0);
        for (i, d) in data.iter_mut().enumerate().take(L) {
            let sum = self.0[i] + other.0[i] + carry;
            *d = sum & CInt::<B, L>::MASK;
            carry = sum >> B;
        }
        CInt::<B, L>(data)
    }
}

impl<const B: usize, const L: usize> Add<&CInt<B, L>> for CInt<B, L> {
    type Output = CInt<B, L>;
    fn add(self, other: &Self) -> Self::Output {
        &self + other
    }
}

impl<const B: usize, const L: usize> Add for CInt<B, L> {
    type Output = CInt<B, L>;
    fn add(self, other: Self) -> Self::Output {
        &self + &other
    }
}

impl<const B: usize, const L: usize> Sub for &CInt<B, L> {
    type Output = CInt<B, L>;
    fn sub(self, other: Self) -> Self::Output {
        // For the two's complement code the additive negation is the result of
        // adding 1 to the bitwise inverted argument's representation. Thus, for
        // any encoded integers x and y we have x - y = x + !y + 1, where "!" is
        // the bitwise inversion and addition is done according to the rules of
        // the code. The algorithm below uses this formula and is the modified
        // addition algorithm, where the carry flag is initialized with 1 and
        // the chunks of the second argument are bitwise inverted
        let (mut data, mut carry) = ([0; L], 1);
        for (i, d) in data.iter_mut().enumerate().take(L) {
            let sum = self.0[i] + (other.0[i] ^ CInt::<B, L>::MASK) + carry;
            *d = sum & CInt::<B, L>::MASK;
            carry = sum >> B;
        }
        CInt::<B, L>(data)
    }
}

impl<const B: usize, const L: usize> Sub<&CInt<B, L>> for CInt<B, L> {
    type Output = CInt<B, L>;
    fn sub(self, other: &Self) -> Self::Output {
        &self - other
    }
}

impl<const B: usize, const L: usize> Sub for CInt<B, L> {
    type Output = CInt<B, L>;
    fn sub(self, other: Self) -> Self::Output {
        &self - &other
    }
}

impl<const B: usize, const L: usize> Neg for &CInt<B, L> {
    type Output = CInt<B, L>;
    fn neg(self) -> Self::Output {
        // For the two's complement code the additive negation is the result
        // of adding 1 to the bitwise inverted argument's representation
        let (mut data, mut carry) = ([0; L], 1);
        for (i, d) in data.iter_mut().enumerate().take(L) {
            let sum = (self.0[i] ^ CInt::<B, L>::MASK) + carry;
            *d = sum & CInt::<B, L>::MASK;
            carry = sum >> B;
        }
        CInt::<B, L>(data)
    }
}

impl<const B: usize, const L: usize> Neg for CInt<B, L> {
    type Output = CInt<B, L>;
    fn neg(self) -> Self::Output {
        -&self
    }
}

impl<const B: usize, const L: usize> Mul for &CInt<B, L> {
    type Output = CInt<B, L>;
    fn mul(self, other: Self) -> Self::Output {
        let mut data = [0; L];
        for i in 0..L {
            let mut carry = 0;
            for k in 0..(L - i) {
                let sum = (data[i + k] as u128)
                    + (carry as u128)
                    + (self.0[i] as u128) * (other.0[k] as u128);
                data[i + k] = sum as u64 & CInt::<B, L>::MASK;
                carry = (sum >> B) as u64;
            }
        }
        CInt::<B, L>(data)
    }
}

impl<const B: usize, const L: usize> Mul<&CInt<B, L>> for CInt<B, L> {
    type Output = CInt<B, L>;
    fn mul(self, other: &Self) -> Self::Output {
        &self * other
    }
}

impl<const B: usize, const L: usize> Mul for CInt<B, L> {
    type Output = CInt<B, L>;
    fn mul(self, other: Self) -> Self::Output {
        &self * &other
    }
}

impl<const B: usize, const L: usize> Mul<i64> for &CInt<B, L> {
    type Output = CInt<B, L>;
    fn mul(self, other: i64) -> Self::Output {
        let mut data = [0; L];
        // If the short multiplicand is non-negative, the standard multiplication
        // algorithm is performed. Otherwise, the product of the additively negated
        // multiplicands is found as follows. Since for the two's complement code
        // the additive negation is the result of adding 1 to the bitwise inverted
        // argument's representation, for any encoded integers x and y we have
        // x * y = (-x) * (-y) = (!x + 1) * (-y) = !x * (-y) + (-y),  where "!" is
        // the bitwise inversion and arithmetic operations are performed according
        // to the rules of the code. If the short multiplicand is negative, the
        // algorithm below uses this formula by substituting the short multiplicand
        // for y and turns into the modified standard multiplication algorithm,
        // where the carry flag is initialized with the additively negated short
        // multiplicand and the chunks of the long multiplicand are bitwise inverted
        let (other, mut carry, mask) = if other < 0 {
            (-other, -other as u64, CInt::<B, L>::MASK)
        } else {
            (other, 0, 0)
        };
        for (i, d) in data.iter_mut().enumerate().take(L) {
            let sum = (carry as u128) + ((self.0[i] ^ mask) as u128) * (other as u128);
            *d = sum as u64 & CInt::<B, L>::MASK;
            carry = (sum >> B) as u64;
        }
        CInt::<B, L>(data)
    }
}

impl<const B: usize, const L: usize> Mul<i64> for CInt<B, L> {
    type Output = CInt<B, L>;
    fn mul(self, other: i64) -> Self::Output {
        &self * other
    }
}

impl<const B: usize, const L: usize> Mul<&CInt<B, L>> for i64 {
    type Output = CInt<B, L>;
    fn mul(self, other: &CInt<B, L>) -> Self::Output {
        other * self
    }
}

impl<const B: usize, const L: usize> Mul<CInt<B, L>> for i64 {
    type Output = CInt<B, L>;
    fn mul(self, other: CInt<B, L>) -> Self::Output {
        other * self
    }
}

pub struct BYInverter {
    modulus: CInt<62, 6>,
    adjuster: CInt<62, 6>,
    inverse: i64,
}

type Matrix = [[i64; 2]; 2];

impl BYInverter {
    /// Returns the Bernstein-Yang transition matrix multiplied by 2^62 and the
    /// new value of the delta variable for the 62 basic steps of the
    /// Bernstein-Yang method, which are to be performed sequentially for
    /// specified initial values of f, g and delta
    /// Based on the constant time "variant of divsteps with better worst-case performance" from:
    /// https://github.com/bitcoin-core/secp256k1/blob/master/doc/safegcd_implementation.md
    fn jump(f: &CInt<62, 6>, g: &CInt<62, 6>, mut zeta: i64) -> (i64, Matrix) {
        let (mut f, mut g) = (f.lowest() as i64, g.lowest() as i64);
        let mut u: i64 = 1;
        let mut v: i64 = 0;
        let mut q: i64 = 0;
        let mut r: i64 = 1;

        for _ in 0..62 {
            let c1 = zeta >> 63;

            // Compute conditionally-negated versions of f, u, v
            let x = (f ^ c1) - c1;
            let y = (u ^ c1) - c1;
            let z = (v ^ c1) - c1;

            let c2 = -(g & 1); // Mask for odd g

            // Conditionally add x, y, z to g, q, r
            g += x & c2;
            q += y & c2;
            r += z & c2;

            // c3 = c1 & c2 (mask for zeta < 0 AND odd g)
            let c3 = c1 & c2;

            // Modified algorithm: just XOR for conditional negation
            zeta ^= c3;
            zeta -= 1; // Always decrement

            // Conditionally add g, q, r to f, u, v
            f += g & c3;
            u += q & c3;
            v += r & c3;

            // Shift g right, shift u and v left
            g >>= 1;
            u <<= 1;
            v <<= 1;
        }

        (zeta, [[u, v], [q, r]])
    }

    /// Returns the updated values of the variables f and g for specified
    /// initial ones and Bernstein-Yang transition matrix multiplied by
    /// 2^62. The returned vector is "matrix * (f, g)' / 2^62", where "'" is the
    /// transpose operator
    fn fg(f: CInt<62, 6>, g: CInt<62, 6>, t: Matrix) -> (CInt<62, 6>, CInt<62, 6>) {
        (
            (t[0][0] * &f + t[0][1] * &g).shift(),
            (t[1][0] * &f + t[1][1] * &g).shift(),
        )
    }

    /// Returns the updated values of the variables d and e for specified
    /// initial ones and Bernstein-Yang transition matrix multiplied by
    /// 2^62. The returned vector is congruent modulo M to "matrix * (d, e)' /
    /// 2^62 (mod M)", where M is the modulus the inverter was created for
    /// and "'" stands for the transpose operator. Both the input and output
    /// values lie in the interval (-2 * M, M)
    fn de(&self, d: CInt<62, 6>, e: CInt<62, 6>, t: Matrix) -> (CInt<62, 6>, CInt<62, 6>) {
        let mask = CInt::<62, 6>::MASK as i64;

        // Create proper masks (-1 or 0)
        let d_sign = -(d.is_negative() as i64);
        let e_sign = -(e.is_negative() as i64);

        let mut md = (t[0][0] & d_sign) + (t[0][1] & e_sign);
        let mut me = (t[1][0] & d_sign) + (t[1][1] & e_sign);

        let cd = t[0][0]
            .wrapping_mul(d.lowest() as i64)
            .wrapping_add(t[0][1].wrapping_mul(e.lowest() as i64))
            & mask;
        let ce = t[1][0]
            .wrapping_mul(d.lowest() as i64)
            .wrapping_add(t[1][1].wrapping_mul(e.lowest() as i64))
            & mask;

        md -= (self.inverse.wrapping_mul(cd).wrapping_add(md)) & mask;
        me -= (self.inverse.wrapping_mul(ce).wrapping_add(me)) & mask;

        let cd = t[0][0] * &d + t[0][1] * &e + md * &self.modulus;
        let ce = t[1][0] * &d + t[1][1] * &e + me * &self.modulus;

        (cd.shift(), ce.shift())
    }

    /// Returns either "value (mod M)" or "-value (mod M)", where M is the
    /// modulus the inverter was created for, depending on "negate", which
    /// determines the presence of "-" in the used formula. The input
    /// integer lies in the interval (-2 * M, M)
    fn norm(&self, mut value: CInt<62, 6>, negate: bool) -> CInt<62, 6> {
        // First conditional addition: if value is negative, add modulus
        let is_neg_mask = (value.is_negative() as u64).wrapping_neg();
        let temp_sum = &value + &self.modulus;

        // Constant-time select: value = is_negative ? (value + modulus) : value
        for i in 0..6 {
            value.0[i] = (value.0[i] & !is_neg_mask) | (temp_sum.0[i] & is_neg_mask);
        }

        // Conditional negation: if negate is true, negate the value
        let negate_mask = (negate as u64).wrapping_neg();
        let negated_value = -value.clone();

        // Constant-time select: value = negate ? (-value) : value
        for i in 0..6 {
            value.0[i] = (value.0[i] & !negate_mask) | (negated_value.0[i] & negate_mask);
        }

        // Second conditional addition: if value is negative after negation, add modulus
        let is_neg_mask2 = (value.is_negative() as u64).wrapping_neg();
        let temp_sum2 = &value + &self.modulus;

        // Constant-time select: value = is_negative ? (value + modulus) : value
        for i in 0..6 {
            value.0[i] = (value.0[i] & !is_neg_mask2) | (temp_sum2.0[i] & is_neg_mask2);
        }

        value
    }

    /// Returns a big unsigned integer as an array of O-bit chunks, which is
    /// equal modulo 2 ^ (O * S) to the input big unsigned integer stored as
    /// an array of I-bit chunks. The ordering of the chunks in these arrays
    /// is little-endian
    const fn convert<const I: usize, const O: usize, const S: usize>(input: &[u64]) -> [u64; S] {
        const fn const_min(a: usize, b: usize) -> usize {
            // Constant-time min without branches
            let diff = a.wrapping_sub(b);
            let msb = diff >> (usize::BITS as usize - 1);
            b.wrapping_add(diff.wrapping_mul(msb))
        }

        let mut output = [0u64; S];
        let mask_final = u64::MAX >> (64 - O);

        // Process maximum possible bits
        let max_input_bits = input.len() * I;
        let max_output_bits = S * O;
        let total_bits = const_min(max_input_bits, max_output_bits);

        let mut bit_idx = 0usize;
        while bit_idx < total_bits {
            let i = bit_idx % I;
            let o = bit_idx % O;
            let input_idx = bit_idx / I;
            let output_idx = bit_idx / O;

            // Safe because bit_idx < total_bits ensures valid indices
            let input_val = input[input_idx];
            let bit = (input_val >> i) & 1;
            output[output_idx] |= bit << o;

            bit_idx += 1;
        }

        // Apply final masks
        let mut idx = 0usize;
        while idx < S {
            output[idx] &= mask_final;
            idx += 1;
        }

        output
    }

    /// Returns the multiplicative inverse of the argument modulo 2^62. The
    /// implementation is based on the Hurchalla's method for computing the
    /// multiplicative inverse modulo a power of two. For better
    /// understanding the implementation, the following paper is recommended:
    /// J. Hurchalla, "An Improved Integer Multiplicative Inverse (modulo 2^w)",
    /// <https://arxiv.org/pdf/2204.04342.pdf>
    const fn inv(value: u64) -> i64 {
        let x = value.wrapping_mul(3) ^ 2;
        let y = 1u64.wrapping_sub(x.wrapping_mul(value));
        let (x, y) = (x.wrapping_mul(y.wrapping_add(1)), y.wrapping_mul(y));
        let (x, y) = (x.wrapping_mul(y.wrapping_add(1)), y.wrapping_mul(y));
        let (x, y) = (x.wrapping_mul(y.wrapping_add(1)), y.wrapping_mul(y));
        (x.wrapping_mul(y.wrapping_add(1)) & CInt::<62, 6>::MASK) as i64
    }

    /// Creates the inverter for specified modulus and adjusting parameter
    pub const fn new(modulus: &[u64], adjuster: &[u64]) -> Self {
        Self {
            modulus: CInt::<62, 6>(Self::convert::<64, 62, 6>(modulus)),
            adjuster: CInt::<62, 6>(Self::convert::<64, 62, 6>(adjuster)),
            inverse: Self::inv(modulus[0]),
        }
    }

    /// Returns the adjusted modular multiplicative inverse
    /// Based on the constant time modified algorithm from
    /// https://github.com/bitcoin-core/secp256k1/blob/master/doc/safegcd_implementation.md
    /// Iteration count of 10 is used to ensure sufficient precision
    /// given the 62 count jump = 62 * 10 = 620
    /// while the constant time variant of divsteps with better worst-case performance
    /// reduces the worst case number of iterations to 590 for 256-bit inputs
    pub fn invert(&self, value: &[u64]) -> [u64; 4] {
        let (mut d, mut e) = (CInt::ZERO, self.adjuster.clone());
        let mut g = CInt::<62, 6>(Self::convert::<64, 62, 6>(value));
        let (mut zeta, mut f) = (-1i64, self.modulus.clone());
        let mut matrix;

        for _ in 0..10 {
            (zeta, matrix) = Self::jump(&f, &g, zeta);
            (f, g) = Self::fg(f, g, matrix);
            (d, e) = self.de(d, e, matrix);
        }

        let mut diff = 0u64;
        for i in 0..6 {
            diff |= f.0[i] ^ CInt::<62, 6>::MINUS_ONE.0[i];
        }
        let antiunit = diff == 0;
        Self::convert::<62, 64, 4>(&self.norm(d, antiunit).0)
    }
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
