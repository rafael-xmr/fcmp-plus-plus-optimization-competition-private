use core::{
    iter::Sum,
    ops::{Add, AddAssign, DerefMut, Mul, MulAssign, Neg, Sub, SubAssign},
};

use rand_core::RngCore;

use subtle::{Choice, ConditionallyNegatable, ConditionallySelectable, ConstantTimeEq, CtOption};
use zeroize::Zeroize;

use crypto_bigint::{modular::constant_mod::Residue, U256};

use group::{
    ff::{Field, PrimeField, PrimeFieldBits},
    prime::PrimeGroup,
    Group, GroupEncoding,
};

use crate::{backend::u8_from_bool, field::HelioseleneField};
use dalek_ff_group::FieldElement as Field25519;

macro_rules! curve {
    (
    $Scalar: ident,
    $Field: ident,
    $Point: ident,
    $B: ident,
    $G_X: ident,
    $G_Y: ident,
  ) => {
        const G_X: $Field = $G_X;
        const G_Y: $Field = $G_Y;

        const B: $Field = $B;

        fn recover_y(x: $Field) -> CtOption<$Field> {
            // x**3 + -3x + B
            (((x.square() * x) - x - x - x) + B).sqrt()
        }

        /// Point.
        #[derive(Clone, Copy, Debug, Zeroize)]
        #[repr(C)]
        pub struct $Point {
            x: $Field, // / Z
            y: $Field, // / Z
            z: $Field,
        }

        const G: $Point = $Point {
            x: G_X,
            y: G_Y,
            z: $Field::ONE,
        };

        impl ConstantTimeEq for $Point {
            fn ct_eq(&self, other: &Self) -> Choice {
                let x1 = self.x * other.z;
                let x2 = other.x * self.z;

                let y1 = self.y * other.z;
                let y2 = other.y * self.z;

                (self.x.is_zero() & other.x.is_zero()) | (x1.ct_eq(&x2) & y1.ct_eq(&y2))
            }
        }

        impl PartialEq for $Point {
            fn eq(&self, other: &$Point) -> bool {
                self.ct_eq(other).into()
            }
        }

        impl Eq for $Point {}

        impl ConditionallySelectable for $Point {
            fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
                $Point {
                    x: $Field::conditional_select(&a.x, &b.x, choice),
                    y: $Field::conditional_select(&a.y, &b.y, choice),
                    z: $Field::conditional_select(&a.z, &b.z, choice),
                }
            }
        }

        impl Add for $Point {
            type Output = $Point;
            #[allow(non_snake_case)]
            fn add(self, other: Self) -> Self {
                let X1 = self.x;
                let Y1 = self.y;
                let X2 = other.x;
                let Y2 = other.y;
                let Z1 = self.z;
                let Z2 = other.z;

                let t0 = X1 * X2;
                let t1 = Y1 * Y2;
                let t2 = Z1 * Z2;
                let t3 = (X1 + Y1) * (X2 + Y2) - (t0 + t1);
                let t4 = (Y1 + Z1) * (Y2 + Z2) - (t1 + t2);

                let Y3 = (X1 + Z1) * (X2 + Z2) - (t0 + t2);
                let X3 = Y3 - B * t2;
                let X3 = X3.double() + X3;
                let Z3 = t1 - X3;

                let X3 = t1 + X3;
                let t2 = t2.double() + t2;
                let Y3 = (B * Y3 - t2) - t0;
                let Y3 = Y3.double() + Y3;
                let t0 = (t0.double() + t0) - t2;

                $Point {
                    x: t3 * X3 - t4 * Y3,
                    y: X3 * Z3 + t0 * Y3,
                    z: t4 * Z3 + t3 * t0,
                }
            }
        }

        impl AddAssign for $Point {
            fn add_assign(&mut self, other: $Point) {
                *self = *self + other;
            }
        }

        impl Add<&$Point> for $Point {
            type Output = $Point;
            fn add(self, other: &$Point) -> $Point {
                self + *other
            }
        }

        impl AddAssign<&$Point> for $Point {
            fn add_assign(&mut self, other: &$Point) {
                *self += *other;
            }
        }

        impl Neg for $Point {
            type Output = $Point;
            fn neg(self) -> Self {
                $Point {
                    x: self.x,
                    y: -self.y,
                    z: self.z,
                }
            }
        }

        impl Sub for $Point {
            type Output = $Point;
            #[allow(clippy::suspicious_arithmetic_impl)]
            fn sub(self, other: Self) -> Self {
                self + other.neg()
            }
        }

        impl SubAssign for $Point {
            fn sub_assign(&mut self, other: $Point) {
                *self = *self - other;
            }
        }

        impl Sub<&$Point> for $Point {
            type Output = $Point;
            fn sub(self, other: &$Point) -> $Point {
                self - *other
            }
        }

        impl SubAssign<&$Point> for $Point {
            fn sub_assign(&mut self, other: &$Point) {
                *self -= *other;
            }
        }

        impl Group for $Point {
            type Scalar = $Scalar;
            fn random(mut rng: impl RngCore) -> Self {
                loop {
                    let mut bytes = $Field::random(&mut rng).to_repr();
                    let mut_ref: &mut [u8] = bytes.as_mut();
                    mut_ref[31] |= u8::try_from(rng.next_u32() % 2).unwrap() << 7;
                    let opt = Self::from_bytes(&bytes);
                    if opt.is_some().into() {
                        return opt.unwrap();
                    }
                }
            }
            fn identity() -> Self {
                $Point {
                    x: $Field::ZERO,
                    y: $Field::ONE,
                    z: $Field::ZERO,
                }
            }
            fn generator() -> Self {
                G
            }
            fn is_identity(&self) -> Choice {
                self.x.ct_eq(&$Field::ZERO)
            }
            #[allow(non_snake_case)]
            fn double(&self) -> Self {
                // dbl-2007-bl-2
                let X1 = self.x;
                let Y1 = self.y;
                let Z1 = self.z;

                let w = (X1 - Z1) * (X1 + Z1);
                let w = w.double() + w;
                let s = (Y1 * Z1).double();
                let R = Y1 * s;
                let B_ = (X1 * R).double();
                let h = w.square() - &B_.double();

                Self::conditional_select(
                    &Self {
                        x: h * s,
                        y: (w * (B_ - &h) - &R.square().double()),
                        z: s * s.square(),
                    },
                    &Self::identity(),
                    self.is_identity(),
                )
            }
        }

        impl Sum<$Point> for $Point {
            fn sum<I: Iterator<Item = $Point>>(iter: I) -> $Point {
                let mut res = Self::identity();
                for i in iter {
                    res += i;
                }
                res
            }
        }

        impl<'a> Sum<&'a $Point> for $Point {
            fn sum<I: Iterator<Item = &'a $Point>>(iter: I) -> $Point {
                $Point::sum(iter.cloned())
            }
        }

        impl Mul<$Scalar> for $Point {
            type Output = $Point;
            fn mul(self, mut other: $Scalar) -> $Point {
                // Precompute the optimal amount that's a multiple of 2
                let mut table = [$Point::identity(); 16];
                table[1] = self;
                for i in 2..16 {
                    table[i] = table[i - 1] + self;
                }

                let mut res = Self::identity();
                let mut bits = 0;
                for (i, mut bit) in other.to_le_bits().iter_mut().rev().enumerate() {
                    bits <<= 1;
                    let mut bit = u8_from_bool(bit.deref_mut());
                    bits |= bit;
                    bit.zeroize();

                    if ((i + 1) % 4) == 0 {
                        if i != 3 {
                            res = res.double().double().double().double();
                        }

                        let mut term = table[0];
                        for (j, candidate) in table[1..].iter().enumerate() {
                            let j = j + 1;
                            term = Self::conditional_select(
                                &term,
                                &candidate,
                                usize::from(bits).ct_eq(&j),
                            );
                        }
                        res += term;
                        bits = 0;
                    }
                }
                other.zeroize();
                res
            }
        }

        impl MulAssign<$Scalar> for $Point {
            fn mul_assign(&mut self, other: $Scalar) {
                *self = *self * other;
            }
        }

        impl Mul<&$Scalar> for $Point {
            type Output = $Point;
            fn mul(self, other: &$Scalar) -> $Point {
                self * *other
            }
        }

        impl MulAssign<&$Scalar> for $Point {
            fn mul_assign(&mut self, other: &$Scalar) {
                *self *= *other;
            }
        }

        impl GroupEncoding for $Point {
            type Repr = <$Field as PrimeField>::Repr;

            fn from_bytes(bytes: &Self::Repr) -> CtOption<Self> {
                // Extract and clear the sign bit
                let sign = Choice::from(bytes[31] >> 7);
                let mut bytes = *bytes;
                let mut_ref: &mut [u8] = bytes.as_mut();
                mut_ref[31] &= !(1 << 7);

                // Parse x, recover y
                $Field::from_repr(bytes).and_then(|x| {
                    let is_identity = x.is_zero();

                    let y = recover_y(x).map(|mut y| {
                        y.conditional_negate(y.is_odd().ct_eq(&!sign));
                        y
                    });

                    // If this the identity, set y to 1
                    let y = CtOption::conditional_select(
                        &y,
                        &CtOption::new($Field::ONE, 1.into()),
                        is_identity,
                    );
                    // Create the point if we have a y solution
                    let point = y.map(|y| $Point {
                        x,
                        y,
                        z: $Field::ONE,
                    });

                    let not_negative_zero = !(is_identity & sign);
                    // Only return the point if it isn't -0
                    CtOption::conditional_select(
                        &CtOption::new($Point::identity(), 0.into()),
                        &point,
                        not_negative_zero,
                    )
                })
            }

            fn from_bytes_unchecked(bytes: &Self::Repr) -> CtOption<Self> {
                $Point::from_bytes(bytes)
            }

            fn to_bytes(&self) -> Self::Repr {
                let Some(z) = Option::<$Field>::from(self.z.invert()) else {
                    return [0; 32];
                };
                let x = self.x * z;
                let y = self.y * z;

                let mut bytes = x.to_repr();
                let mut_ref: &mut [u8] = bytes.as_mut();

                // Normalize the sign to 0 when x is 0
                let y_sign =
                    u8::conditional_select(&y.is_odd().unwrap_u8(), &0, x.ct_eq(&$Field::ZERO));
                mut_ref[31] |= y_sign << 7;
                bytes
            }
        }

        impl PrimeGroup for $Point {}

        impl ec_divisors::DivisorCurve for $Point {
            type FieldElement = $Field;

            fn a() -> Self::FieldElement {
                -$Field::from(3u64)
            }
            fn b() -> Self::FieldElement {
                B
            }

            fn to_xy(point: Self) -> Option<(Self::FieldElement, Self::FieldElement)> {
                let z: Self::FieldElement = Option::from(point.z.invert())?;
                Some((point.x * z, point.y * z))
            }
        }
    };
}

mod helios {
    use super::*;

    pub const HELIOS_B: Field25519 = Field25519(Residue::new(&U256::from_be_hex(
        "22e8c739b0ea70b8be94a76b3ebb7b3b043f6f384113bf3522b49ee1edd73ad4",
    )));
    pub const HELIOS_G_X: Field25519 = Field25519(Residue::new(&U256::from_be_hex(
        "0000000000000000000000000000000000000000000000000000000000000003",
    )));
    pub const HELIOS_G_Y: Field25519 = Field25519(Residue::new(&U256::from_be_hex(
        "537b74d97ac0721cbd92668350205f0759003bddc586a5dcd243e639e3183ef4",
    )));

    curve!(
        HelioseleneField,
        Field25519,
        HeliosPoint,
        HELIOS_B,
        HELIOS_G_X,
        HELIOS_G_Y,
    );

    #[test]
    fn test_helios() {
        ff_group_tests::group::test_prime_group_bits::<_, HeliosPoint>(&mut rand_core::OsRng);
    }

    #[test]
    fn generator_helios() {
        use helios::{G, G_X, G_Y};
        assert!(G.x == G_X);
        assert!(G.y == G_Y);
        assert!(recover_y(G.x).unwrap() == -G.y);
    }

    #[test]
    fn zero_x_is_invalid() {
        assert!(Option::<Field25519>::from(recover_y(Field25519::ZERO)).is_none());
    }
}
pub use helios::HeliosPoint;

mod selene {
    use super::*;

    pub const SELENE_B: HelioseleneField = HelioseleneField(U256::from_be_hex(
        "70127713695876c17f51bba595ffe279f3944bdf06ae900e68de0983cb5a4558",
    ));
    pub const SELENE_G_X: HelioseleneField = HelioseleneField(U256::from_be_hex(
        "0000000000000000000000000000000000000000000000000000000000000001",
    ));
    pub const SELENE_G_Y: HelioseleneField = HelioseleneField(U256::from_be_hex(
        "7a19d927b85cca9257c93177455c825f938bb198c8f09b37741e0aa6a1d3fdd2",
    ));

    curve!(
        Field25519,
        HelioseleneField,
        SelenePoint,
        SELENE_B,
        SELENE_G_X,
        SELENE_G_Y,
    );

    #[test]
    fn test_selene() {
        ff_group_tests::group::test_prime_group_bits::<_, SelenePoint>(&mut rand_core::OsRng);
    }

    #[test]
    fn generator_selene() {
        use selene::{G, G_X, G_Y};
        assert!(G.x == G_X);
        assert!(G.y == G_Y);
        assert!(recover_y(G.x).unwrap() == G.y);
    }

    #[test]
    fn zero_x_is_invalid() {
        assert!(Option::<HelioseleneField>::from(recover_y(HelioseleneField::ZERO)).is_none());
    }
}
pub use selene::SelenePoint;

// Checks random won't infinitely loop
#[test]
fn random() {
    HeliosPoint::random(&mut rand_core::OsRng);
    SelenePoint::random(&mut rand_core::OsRng);
}
