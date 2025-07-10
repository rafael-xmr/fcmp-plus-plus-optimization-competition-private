// Copyright (c) 2021-2025 Privacy Scaling Explorations team
//
// Permission is hereby granted, free of charge, to any
// person obtaining a copy of this software and associated
// documentation files (the "Software"), to deal in the
// Software without restriction, including without
// limitation the rights to use, copy, modify, merge,
// publish, distribute, sublicense, and/or sell copies of
// the Software, and to permit persons to whom the Software
// is furnished to do so, subject to the following
// conditions:

// The above copyright notice and this permission notice
// shall be included in all copies or substantial portions
// of the Software.

// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF
// ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED
// TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A
// PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT
// SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
// CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
// OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR
// IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
// DEALINGS IN THE SOFTWARE.
//
// NOTICE: This file contains modifications from the original version.

use core::ops::{Add, Mul, Neg, Sub};

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
