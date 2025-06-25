use zeroize::Zeroize;

// Use black_box when possible
#[rustversion::since(1.66)]
use core::hint::black_box;
#[rustversion::before(1.66)]
fn black_box<T>(val: T) -> T {
    val
}

pub(crate) fn u8_from_bool(bit_ref: &mut bool) -> u8 {
    let bit_ref = black_box(bit_ref);

    let mut bit = black_box(*bit_ref);
    let res = black_box(bit as u8);
    bit.zeroize();
    debug_assert!((res | 1) == 1);

    bit_ref.zeroize();
    res
}

macro_rules! math_op {
    (
    $Value: ident,
    $Other: ident,
    $Op: ident,
    $op_fn: ident,
    $Assign: ident,
    $assign_fn: ident,
    $function: expr
  ) => {
        impl $Op<$Other> for $Value {
            type Output = $Value;
            fn $op_fn(self, other: $Other) -> Self::Output {
                Self($function(self.0, other.0))
            }
        }
        impl $Assign<$Other> for $Value {
            fn $assign_fn(&mut self, other: $Other) {
                self.0 = $function(self.0, other.0);
            }
        }
        impl<'a> $Op<&'a $Other> for $Value {
            type Output = $Value;
            fn $op_fn(self, other: &'a $Other) -> Self::Output {
                Self($function(self.0, other.0))
            }
        }
        impl<'a> $Assign<&'a $Other> for $Value {
            fn $assign_fn(&mut self, other: &'a $Other) {
                self.0 = $function(self.0, other.0);
            }
        }
    };
}

macro_rules! from_wrapper {
    ($wrapper: ident, $inner: ident, $uint: ident) => {
        impl From<$uint> for $wrapper {
            fn from(a: $uint) -> $wrapper {
                Self($inner::from(a))
            }
        }
    };
}

macro_rules! field {
    (
    $FieldName: ident,

    $MODULUS_STR: ident,

    $C_LO: ident,
    $C_HI: ident,

    $MULTIPLICATIVE_GENERATOR: literal,
    $S: literal,
    $ROOT_OF_UNITY: literal,
    $DELTA: literal,
  ) => {
        use core::{
            iter::{Product, Sum},
            ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
        };

        use rand_core::RngCore;

        use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, ConstantTimeLess, CtOption};

        use crypto_bigint::{Integer, Limb, Zero};

        use ff::{Field, FieldBits, PrimeField, PrimeFieldBits};

        const MODULUS: U256 = U256::from_be_hex($MODULUS_STR);
        const MODULUS_LIMBS: &[Limb; 4] = MODULUS.as_limbs();

        impl ConstantTimeEq for $FieldName {
            fn ct_eq(&self, other: &Self) -> Choice {
                self.0.ct_eq(&other.0)
            }
        }

        impl ConditionallySelectable for $FieldName {
            fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
                $FieldName(U256::conditional_select(&a.0, &b.0, choice))
            }
        }

        math_op!(
            $FieldName,
            $FieldName,
            Add,
            add,
            AddAssign,
            add_assign,
            |x: U256, y: U256| {
                let x_limbs = x.as_limbs();
                let y_limbs = y.as_limbs();

                let (r0, c0) = x_limbs[0].0.overflowing_add(y_limbs[0].0);
                let (r1, c1) = x_limbs[1].0.overflowing_add(y_limbs[1].0);
                let (r1, c1b) = r1.overflowing_add(c0 as u64);
                let c1 = c1 | c1b;

                let (r2, c2) = x_limbs[2].0.overflowing_add(y_limbs[2].0);
                let (r2, c2b) = r2.overflowing_add(c1 as u64);
                let c2 = c2 | c2b;

                let (r3, c3) = x_limbs[3].0.overflowing_add(y_limbs[3].0);
                let (r3, c3b) = r3.overflowing_add(c2 as u64);
                let carry = (c3 | c3b) as u64;

                // If carry, add 2c - do it unconditionally then mask
                let c_doubled_lo = $C_LO << 1;
                let c_doubled_hi = ($C_HI << 1) | ($C_LO >> 63);

                // Compute both with and without carry correction
                let (a0, ca0) = r0.overflowing_add(c_doubled_lo);
                let (a1, ca1) = r1.overflowing_add(c_doubled_hi);
                let (a1, ca1b) = a1.overflowing_add(ca0 as u64);
                let ca1_total = (ca1 | ca1b) as u64;

                let (a2, ca2) = r2.overflowing_add(ca1_total);
                let (a3, _ca3) = r3.overflowing_add(ca2 as u64);

                // Select based on carry
                let carry_mask = carry.wrapping_neg();
                let r0 = (r0 & !carry_mask) | (a0 & carry_mask);
                let r1 = (r1 & !carry_mask) | (a1 & carry_mask);
                let r2 = (r2 & !carry_mask) | (a2 & carry_mask);
                let r3 = (r3 & !carry_mask) | (a3 & carry_mask);

                // Final reduction - subtract modulus
                let (s0, b0) = r0.overflowing_sub(MODULUS_LIMBS[0].0);
                let (s1, b1) = r1.overflowing_sub(MODULUS_LIMBS[1].0);
                let (s1, b1b) = s1.overflowing_sub(b0 as u64);
                let b1_total = (b1 | b1b) as u64;

                let (s2, b2) = r2.overflowing_sub(MODULUS_LIMBS[2].0);
                let (s2, b2b) = s2.overflowing_sub(b1_total);
                let b2_total = (b2 | b2b) as u64;

                let (s3, b3) = r3.overflowing_sub(MODULUS_LIMBS[3].0);
                let (s3, b3b) = s3.overflowing_sub(b2_total);
                let borrow = (b3 | b3b) as u64;

                // Select reduced if no borrow
                let no_borrow_mask = ((borrow == 0) as u64).wrapping_neg();

                U256::from_words([
                    (r0 & !no_borrow_mask) | (s0 & no_borrow_mask),
                    (r1 & !no_borrow_mask) | (s1 & no_borrow_mask),
                    (r2 & !no_borrow_mask) | (s2 & no_borrow_mask),
                    (r3 & !no_borrow_mask) | (s3 & no_borrow_mask),
                ])
            }
        );

        math_op!(
            $FieldName,
            $FieldName,
            Sub,
            sub,
            SubAssign,
            sub_assign,
            |x: U256, y: U256| {
                let x_limbs = x.as_limbs();
                let y_limbs = y.as_limbs();

                let (r0, b0) = x_limbs[0].0.overflowing_sub(y_limbs[0].0);

                let (r1, b1) = x_limbs[1].0.overflowing_sub(y_limbs[1].0);
                let (r1, b1b) = r1.overflowing_sub(b0 as u64);
                let b1_total = (b1 | b1b) as u64;

                let (r2, b2) = x_limbs[2].0.overflowing_sub(y_limbs[2].0);
                let (r2, b2b) = r2.overflowing_sub(b1_total);
                let b2_total = (b2 | b2b) as u64;

                let (r3, b3) = x_limbs[3].0.overflowing_sub(y_limbs[3].0);
                let (r3, b3b) = r3.overflowing_sub(b2_total);
                let borrow = (b3 | b3b) as u64;

                let (a0, c0) = r0.overflowing_add(MODULUS_LIMBS[0].0);

                let (a1, c1) = r1.overflowing_add(MODULUS_LIMBS[1].0);
                let (a1, c1b) = a1.overflowing_add(c0 as u64);
                let c1_total = (c1 | c1b) as u64;

                let (a2, c2) = r2.overflowing_add(MODULUS_LIMBS[2].0);
                let (a2, c2b) = a2.overflowing_add(c1_total);
                let c2_total = (c2 | c2b) as u64;

                let (a3, _) = r3.overflowing_add(MODULUS_LIMBS[3].0);
                let (a3, _) = a3.overflowing_add(c2_total);

                let borrow_mask = borrow.wrapping_neg();

                U256::from_words([
                    (r0 & !borrow_mask) | (a0 & borrow_mask),
                    (r1 & !borrow_mask) | (a1 & borrow_mask),
                    (r2 & !borrow_mask) | (a2 & borrow_mask),
                    (r3 & !borrow_mask) | (a3 & borrow_mask),
                ])
            }
        );

        math_op!(
            $FieldName,
            $FieldName,
            Mul,
            mul,
            MulAssign,
            mul_assign,
            |x: U256, y: U256| {
                let x_limbs = x.as_limbs();

                let x0 = x_limbs[0].0;
                let x1 = x_limbs[1].0;
                let x2 = x_limbs[2].0;
                let x3 = x_limbs[3].0;

                let y_limbs = y.as_limbs();

                let y0 = y_limbs[0].0;
                let y1 = y_limbs[1].0;
                let y2 = y_limbs[2].0;
                let y3 = y_limbs[3].0;

                // Multiply low and high parts
                let (z0_lo, z0_hi) = mul_wide([x0, x1], [y0, y1]);
                let (z2_lo, z2_hi) = mul_wide([x2, x3], [y2, y3]);

                // Compute sums for middle part
                let (x_sum, x_carry) = adc([x0, x1], [x2, x3]);
                let (y_sum, y_carry) = adc([y0, y1], [y2, y3]);

                // Multiply sums
                let (z1_temp_lo, z1_temp_hi) = mul_wide(x_sum, y_sum);

                // Build z1 with inline carry corrections
                let z1_0 = z1_temp_lo[0];
                let z1_1 = z1_temp_lo[1];
                let z1_2 = z1_temp_hi[0];
                let z1_3 = z1_temp_hi[1];

                // NOTE: Constant-time carry corrections
                let x_carry_mask = (x_carry as u64).wrapping_neg();
                let y_carry_mask = (y_carry as u64).wrapping_neg();
                let both_carry_mask = ((x_carry && y_carry) as u64).wrapping_neg();

                // Add y_sum[0] & x_carry_mask at position 2
                let value = y_sum[0] & x_carry_mask;
                let (sum, carry) = z1_2.overflowing_add(value);
                let z1_2 = sum;
                let (sum, carry) = z1_3.overflowing_add(carry as u64);
                let z1_3 = sum;
                let z1_4 = carry as u64;

                // Add y_sum[1] & x_carry_mask at position 3
                let value = y_sum[1] & x_carry_mask;
                let (sum, carry) = z1_3.overflowing_add(value);
                let z1_3 = sum;
                let (sum, carry) = z1_4.overflowing_add(carry as u64);
                let z1_4 = sum;
                let z1_5 = carry as u64;

                // Add x_sum[0] & y_carry_mask at position 2
                let value = x_sum[0] & y_carry_mask;
                let (sum, carry) = z1_2.overflowing_add(value);
                let z1_2 = sum;
                let (sum, carry) = z1_3.overflowing_add(carry as u64);
                let z1_3 = sum;
                let (sum, carry) = z1_4.overflowing_add(carry as u64);
                let z1_4 = sum;
                let (sum, _carry) = z1_5.overflowing_add(carry as u64);
                let z1_5 = sum;

                // Add x_sum[1] & y_carry_mask at position 3
                let value = x_sum[1] & y_carry_mask;
                let (sum, carry) = z1_3.overflowing_add(value);
                let z1_3 = sum;
                let (sum, carry) = z1_4.overflowing_add(carry as u64);
                let z1_4 = sum;
                let (sum, _carry) = z1_5.overflowing_add(carry as u64);
                let z1_5 = sum;

                // Add both_carry at position 4
                let value = both_carry_mask & 1;
                let (sum, carry) = z1_4.overflowing_add(value);
                let z1_4 = sum;
                let (sum, _carry) = z1_5.overflowing_add(carry as u64);
                let z1_5 = sum;

                // NOTE: Compute z1 = z1_temp - z0 - z2
                // First subtraction: z1 -= z0
                let (val, borrow) = z1_0.overflowing_sub(z0_lo[0]);
                let z1_0 = val;

                let (diff, b) = z1_1.overflowing_sub(z0_lo[1]);
                let (val, b2) = diff.overflowing_sub(borrow as u64);
                let z1_1 = val;
                let borrow = b | b2;

                let (diff, b) = z1_2.overflowing_sub(z0_hi[0]);
                let (val, b2) = diff.overflowing_sub(borrow as u64);
                let z1_2 = val;
                let borrow = b | b2;

                let (diff, b) = z1_3.overflowing_sub(z0_hi[1]);
                let (val, b2) = diff.overflowing_sub(borrow as u64);
                let z1_3 = val;
                let borrow = b | b2;

                let (val, borrow) = z1_4.overflowing_sub(borrow as u64);
                let z1_4 = val;
                let (val, _borrow) = z1_5.overflowing_sub(borrow as u64);
                let z1_5 = val;

                // Second subtraction: z1 -= z2
                let (val, borrow) = z1_0.overflowing_sub(z2_lo[0]);
                let z1_0 = val;

                let (diff, b) = z1_1.overflowing_sub(z2_lo[1]);
                let (val, b2) = diff.overflowing_sub(borrow as u64);
                let z1_1 = val;
                let borrow = b | b2;

                let (diff, b) = z1_2.overflowing_sub(z2_hi[0]);
                let (val, b2) = diff.overflowing_sub(borrow as u64);
                let z1_2 = val;
                let borrow = b | b2;

                let (diff, b) = z1_3.overflowing_sub(z2_hi[1]);
                let (val, b2) = diff.overflowing_sub(borrow as u64);
                let z1_3 = val;
                let borrow = b | b2;

                let (val, borrow) = z1_4.overflowing_sub(borrow as u64);
                let z1_4 = val;
                let (val, _borrow) = z1_5.overflowing_sub(borrow as u64);
                let z1_5 = val;

                // Add z0
                let r0 = z0_lo[0];
                let r1 = z0_lo[1];

                // NOTE: Add z1 << 128 (shift by 2 limbs)
                let (r2, carry) = z0_hi[0].overflowing_add(z1_0);
                let (r3, c) = z0_hi[1].overflowing_add(z1_1);
                let (r3, c2) = r3.overflowing_add(carry as u64);
                let carry = (c | c2) as u64;

                let r4 = z1_2 + carry;
                let r5 = z1_3;
                let r6 = z1_4;
                let r7 = z1_5;

                // Add z2 << 256 (shift by 4 limbs)
                let (r4, carry) = r4.overflowing_add(z2_lo[0]);
                let (r5, c) = r5.overflowing_add(z2_lo[1]);
                let (r5, c2) = r5.overflowing_add(carry as u64);
                let carry = (c | c2) as u64;

                let (r6, c) = r6.overflowing_add(z2_hi[0]);
                let (r6, c2) = r6.overflowing_add(carry as u64);
                let carry = (c | c2) as u64;

                let r7 = r7.wrapping_add(z2_hi[1]).wrapping_add(carry);

                reduce_limbs(
                    [r0, r1, r2, r3, r4, r5, r6, r7],
                    $C_LO,
                    $C_HI,
                    MODULUS_LIMBS,
                )
            }
        );

        from_wrapper!($FieldName, U256, u8);
        from_wrapper!($FieldName, U256, u16);
        from_wrapper!($FieldName, U256, u32);
        from_wrapper!($FieldName, U256, u64);
        from_wrapper!($FieldName, U256, u128);

        impl Neg for $FieldName {
            type Output = $FieldName;
            fn neg(self) -> $FieldName {
                // Special case: -0 = 0
                let is_zero = self.0.is_zero();
                let zero_mask = is_zero.unwrap_u8() as u64;
                let zero_mask = zero_mask.wrapping_neg();

                let x_limbs = self.0.as_limbs();

                // When subtracting from 0, we always borrow (except for zero)
                // So we compute MODULUS - self directly
                let (r0, b0) = MODULUS_LIMBS[0].0.overflowing_sub(x_limbs[0].0);

                let (r1, b1) = MODULUS_LIMBS[1].0.overflowing_sub(x_limbs[1].0);
                let (r1, b1b) = r1.overflowing_sub(b0 as u64);
                let b1_total = (b1 | b1b) as u64;

                let (r2, b2) = MODULUS_LIMBS[2].0.overflowing_sub(x_limbs[2].0);
                let (r2, b2b) = r2.overflowing_sub(b1_total);
                let b2_total = (b2 | b2b) as u64;

                let r3 = MODULUS_LIMBS[3].0.wrapping_sub(x_limbs[3].0);
                let r3 = r3.wrapping_sub(b2_total);

                // Return 0 if input was 0, otherwise return the result
                Self(U256::from_words([
                    r0 & !zero_mask,
                    r1 & !zero_mask,
                    r2 & !zero_mask,
                    r3 & !zero_mask,
                ]))
            }
        }

        impl<'a> Neg for &'a $FieldName {
            type Output = $FieldName;
            fn neg(self) -> Self::Output {
                (*self).neg()
            }
        }

        impl $FieldName {
            /// Perform an exponentiation.
            pub fn pow(&self, other: $FieldName) -> $FieldName {
                let mut table = [$FieldName::ONE; TABLE_SIZE];
                table[1] = *self;
                table[2] = self.square();

                for i in 3..TABLE_SIZE {
                    table[i] = $FieldName::conditional_select(
                        &(table[i - 1] * self),
                        &table[i / 2].square(),
                        Choice::from(((i % 2) == 0) as u8),
                    );
                }

                let bits = other.to_le_bits();
                let mut res = $FieldName::ONE;

                for window_idx in (0..64).rev() {
                    // Square 4 times (except for the last window)
                    if window_idx != 63 {
                        res = res.square().square().square().square();
                    }

                    // Extract 4-bit window value
                    let bit_idx = window_idx * 4;
                    let mut window_val = 0u8;
                    for j in 0..4 {
                        let idx = bit_idx + j;
                        // Always access bits array, but mask out invalid indices
                        let in_bounds = ((idx < 256) as u8).wrapping_neg();
                        let bit_value = ((idx < 256) as u8) & (bits[idx % 256] as u8);
                        window_val |= (bit_value & in_bounds) << j;
                    }

                    // Constant-time table lookup
                    let mut acc = table[0];
                    for i in 0..TABLE_SIZE {
                        acc = Self::conditional_select(
                            &acc,
                            &table[i],
                            subtle::ConstantTimeEq::ct_eq(&(i as u8), &(window_val as u8)),
                        );
                    }
                    res = Self::conditional_select(&res, &(res * acc), window_val.ct_ne(&0));
                }

                res
            }
        }

        impl Field for $FieldName {
            const ZERO: Self = Self(U256::ZERO);
            const ONE: Self = Self(U256::ONE);

            fn random(mut rng: impl RngCore) -> Self {
                let mut bytes = [0; 64];
                rng.fill_bytes(&mut bytes);
                $FieldName(reduce_limbs(
                    bytes_to_words(bytes),
                    $C_LO,
                    $C_HI,
                    MODULUS_LIMBS,
                ))
            }

            /// Karatsuba squaring with integrated Crandall reduction
            /// Optimized for 256-bit (4 limb) squaring
            fn square(&self) -> Self {
                let x_limbs = self.0.as_limbs();

                let x0 = x_limbs[0].0;
                let x1 = x_limbs[1].0;
                let x2 = x_limbs[2].0;
                let x3 = x_limbs[3].0;

                // Square low part: z0 = x_lo²
                let (z0_lo, z0_hi) = square_wide([x0, x1]);

                // Square high part: z2 = x_hi²
                let (z2_lo, z2_hi) = square_wide([x2, x3]);

                // Compute x_lo * x_hi for middle term (will be doubled)
                let (z1_lo, z1_hi) = mul_wide([x0, x1], [x2, x3]);

                // Add z0 (bits 0-255)
                let r0 = z0_lo[0];
                let r1 = z0_lo[1];
                let r2 = z0_hi[0];
                let r3 = z0_hi[1];

                // Add z2 << 256 (bits 256-511)
                let r4 = z2_lo[0];
                let r5 = z2_lo[1];
                let r6 = z2_hi[0];
                let r7 = z2_hi[1];

                // Add 2*z1 << 128 (shift by 2 limbs)
                // Extract z1 values once
                let z1_0 = z1_lo[0];
                let z1_1 = z1_lo[1];
                let z1_2 = z1_hi[0];
                let z1_3 = z1_hi[1];

                // Double and add z1 with carry propagation
                let carry = 0u64;

                // Add 2*z1[0] to r2
                let doubled = (z1_0 as u128) << 1;
                let sum = (r2 as u128) + (doubled as u64 as u128) + carry as u128;
                let r2 = sum as u64;
                let carry = (doubled >> 64) as u64 + (sum >> 64) as u64;

                // Add 2*z1[1] to r3
                let doubled = (z1_1 as u128) << 1;
                let sum = (r3 as u128) + (doubled as u64 as u128) + carry as u128;
                let r3 = sum as u64;
                let carry = (doubled >> 64) as u64 + (sum >> 64) as u64;

                // Add 2*z1[2] to r4
                let doubled = (z1_2 as u128) << 1;
                let sum = (r4 as u128) + (doubled as u64 as u128) + carry as u128;
                let r4 = sum as u64;
                let carry = (doubled >> 64) as u64 + (sum >> 64) as u64;

                // Add 2*z1[3] to r5
                let doubled = (z1_3 as u128) << 1;
                let sum = (r5 as u128) + (doubled as u64 as u128) + carry as u128;
                let r5 = sum as u64;
                let carry = (doubled >> 64) as u64 + (sum >> 64) as u64;

                // Propagate remaining carry
                let (sum, c) = r6.overflowing_add(carry);
                let r6 = sum;
                let c_mask = (c as u64).wrapping_neg();
                let r7 = r7.wrapping_add(c_mask & 1);

                Self(reduce_limbs(
                    [r0, r1, r2, r3, r4, r5, r6, r7],
                    $C_LO,
                    $C_HI,
                    MODULUS_LIMBS,
                ))
            }

            fn double(&self) -> Self {
                let x_limbs = self.0.as_limbs();

                // Shift left by 1 bit with carry propagation (unrolled)
                let r0 = x_limbs[0].0 << 1;
                let carry0 = x_limbs[0].0 >> 63;

                let r1 = (x_limbs[1].0 << 1) | carry0;
                let carry1 = x_limbs[1].0 >> 63;

                let r2 = (x_limbs[2].0 << 1) | carry1;
                let carry2 = x_limbs[2].0 >> 63;

                let r3 = (x_limbs[3].0 << 1) | carry2;
                let carry = x_limbs[3].0 >> 63;

                let c_doubled_lo = $C_LO << 1;
                let c_doubled_hi = ($C_HI << 1) | ($C_LO >> 63);

                // Compute both with and without carry correction
                let (a0, ca0) = r0.overflowing_add(c_doubled_lo);
                let (a1, ca1) = r1.overflowing_add(c_doubled_hi);
                let (a1, ca1b) = a1.overflowing_add(ca0 as u64);
                let ca1_total = (ca1 | ca1b) as u64;

                let (a2, ca2) = r2.overflowing_add(ca1_total);
                let (a3, _ca3) = r3.overflowing_add(ca2 as u64);

                // Select based on carry
                let carry_mask = carry.wrapping_neg();
                let r0 = (r0 & !carry_mask) | (a0 & carry_mask);
                let r1 = (r1 & !carry_mask) | (a1 & carry_mask);
                let r2 = (r2 & !carry_mask) | (a2 & carry_mask);
                let r3 = (r3 & !carry_mask) | (a3 & carry_mask);

                // Final reduction - subtract modulus
                let (s0, b0) = r0.overflowing_sub(MODULUS_LIMBS[0].0);
                let (s1, b1) = r1.overflowing_sub(MODULUS_LIMBS[1].0);
                let (s1, b1b) = s1.overflowing_sub(b0 as u64);
                let b1_total = (b1 | b1b) as u64;

                let (s2, b2) = r2.overflowing_sub(MODULUS_LIMBS[2].0);
                let (s2, b2b) = s2.overflowing_sub(b1_total);
                let b2_total = (b2 | b2b) as u64;

                let (s3, b3) = r3.overflowing_sub(MODULUS_LIMBS[3].0);
                let (s3, b3b) = s3.overflowing_sub(b2_total);
                let borrow = (b3 | b3b) as u64;

                // Select reduced if no borrow
                let no_borrow_mask = ((borrow == 0) as u64).wrapping_neg();

                Self(U256::from_words([
                    (r0 & !no_borrow_mask) | (s0 & no_borrow_mask),
                    (r1 & !no_borrow_mask) | (s1 & no_borrow_mask),
                    (r2 & !no_borrow_mask) | (s2 & no_borrow_mask),
                    (r3 & !no_borrow_mask) | (s3 & no_borrow_mask),
                ]))
            }

            fn invert(&self) -> CtOption<Self> {
                let (inv, exists) = self.0.inv_odd_mod(&MODULUS);
                CtOption::new($FieldName(inv), exists.into())

                // self.invert_bernstein_yang_for_crandall_prime()
            }

            fn sqrt(&self) -> CtOption<Self> {
                $FieldName::sqrt(self)
            }

            fn sqrt_ratio(num: &Self, div: &Self) -> (Choice, Self) {
                $FieldName::sqrt_ratio(num, div)
            }
        }

        impl PrimeField for $FieldName {
            type Repr = [u8; 32];

            const MODULUS: &'static str = $MODULUS_STR;

            const NUM_BITS: u32 = 255;
            const CAPACITY: u32 = 254;

            const TWO_INV: Self = $FieldName(U256::from_u8(2).inv_odd_mod(&MODULUS).0);

            const MULTIPLICATIVE_GENERATOR: Self = Self(U256::from_u8($MULTIPLICATIVE_GENERATOR));
            const S: u32 = $S;

            const ROOT_OF_UNITY: Self = $FieldName(U256::from_be_hex($ROOT_OF_UNITY));
            const ROOT_OF_UNITY_INV: Self = Self(Self::ROOT_OF_UNITY.0.inv_odd_mod(&MODULUS).0);

            const DELTA: Self = $FieldName(U256::from_be_hex($DELTA));

            fn from_repr(bytes: [u8; 32]) -> CtOption<Self> {
                let res = U256::from_le_bytes(bytes);
                CtOption::new($FieldName(res), res.ct_lt(&MODULUS))
            }

            fn to_repr(&self) -> [u8; 32] {
                self.0.to_le_bytes()
            }

            fn is_odd(&self) -> Choice {
                self.0.is_odd()
            }

            fn from_u128(num: u128) -> Self {
                Self::from(num)
            }
        }

        impl PrimeFieldBits for $FieldName {
            type ReprBits = [u8; 32];

            fn to_le_bits(&self) -> FieldBits<Self::ReprBits> {
                self.to_repr().into()
            }

            fn char_le_bits() -> FieldBits<Self::ReprBits> {
                MODULUS.to_le_bytes().into()
            }
        }

        impl Sum<$FieldName> for $FieldName {
            fn sum<I: Iterator<Item = $FieldName>>(iter: I) -> $FieldName {
                let mut res = $FieldName::ZERO;
                for item in iter {
                    res += item;
                }
                res
            }
        }

        impl<'a> Sum<&'a $FieldName> for $FieldName {
            fn sum<I: Iterator<Item = &'a $FieldName>>(iter: I) -> $FieldName {
                iter.cloned().sum()
            }
        }

        impl Product<$FieldName> for $FieldName {
            fn product<I: Iterator<Item = $FieldName>>(iter: I) -> $FieldName {
                let mut res = $FieldName::ONE;
                for item in iter {
                    res *= item;
                }
                res
            }
        }

        impl<'a> Product<&'a $FieldName> for $FieldName {
            fn product<I: Iterator<Item = &'a $FieldName>>(iter: I) -> $FieldName {
                iter.cloned().product()
            }
        }
    };
}
