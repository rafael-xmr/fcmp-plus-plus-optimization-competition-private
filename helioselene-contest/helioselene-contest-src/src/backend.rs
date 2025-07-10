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

        use crypto_bigint::Integer;

        use ff::{helpers::sqrt_ratio_generic, Field, FieldBits, PrimeField, PrimeFieldBits};

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
            |x: U256, y: U256| helioselene_add(x, y)
        );

        math_op!(
            $FieldName,
            $FieldName,
            Sub,
            sub,
            SubAssign,
            sub_assign,
            |x: U256, y: U256| helioselene_sub(x, y)
        );

        math_op!(
            $FieldName,
            $FieldName,
            Mul,
            mul,
            MulAssign,
            mul_assign,
            |x: U256, y: U256| helioselene_mul(x, y)
        );

        from_wrapper!($FieldName, U256, u8);
        from_wrapper!($FieldName, U256, u16);
        from_wrapper!($FieldName, U256, u32);
        from_wrapper!($FieldName, U256, u64);
        from_wrapper!($FieldName, U256, u128);

        impl Neg for $FieldName {
            type Output = $FieldName;
            fn neg(self) -> $FieldName {
                Self(helioselene_neg(self.0))
            }
        }

        impl<'a> Neg for &'a $FieldName {
            type Output = $FieldName;
            fn neg(self) -> Self::Output {
                (*self).neg()
            }
        }

        impl $FieldName {
            /// Perform an exponentiation using a 4-bit fixed-window algorithm.
            pub fn pow(&self, other: $FieldName) -> $FieldName {
                let mut table = [$FieldName::ONE; 16];
                table[1] = *self;
                table[2] = self.square();

                for i in 3..16 {
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
                    for i in 0..16 {
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
                $FieldName(reduce_crandall_full(bytes_to_words(bytes)))
            }

            fn square(&self) -> Self {
                Self(helioselene_square(self.0))
            }

            fn double(&self) -> Self {
                Self(helioselene_double(self.0))
            }

            fn invert(&self) -> CtOption<Self> {
                let (inv, exists) = self.0.inv_odd_mod(&MODULUS);
                CtOption::new($FieldName(inv), exists.into())
            }

            fn sqrt(&self) -> CtOption<Self> {
                let res = self.pow(MOD_1_4);
                CtOption::new(res, res.square().ct_eq(self))
            }

            fn sqrt_ratio(num: &Self, div: &Self) -> (Choice, Self) {
                sqrt_ratio_generic(num, div)
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
