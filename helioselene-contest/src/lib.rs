#![allow(non_snake_case)]

use helioselene::{
    group::ff::Field as FieldRef, Field25519 as Field25519Ref, HeliosPoint as HeliosPointRef,
    HelioseleneField as HelioseleneFieldRef, SelenePoint as SelenePointRef,
};
use helioselene_contest_src::{
    group::{ff::PrimeField, Group, GroupEncoding},
    Field25519, HeliosPoint, HelioseleneField, SelenePoint,
};

use rand_core::OsRng;

use rand_chacha::ChaCha20Rng;
use rand_core::SeedableRng;

use paste::paste;

pub fn test_gen_random_helios_scalar() -> (HelioseleneField, HelioseleneFieldRef) {
    let a_ref = HelioseleneFieldRef::random(&mut OsRng);
    let a = HelioseleneField::from_repr(a_ref.to_repr()).expect("Failed to read scalar");
    assert_eq!(a.to_repr(), a_ref.to_repr());
    (a, a_ref)
}

pub fn test_gen_random_selene_scalar() -> (Field25519, Field25519Ref) {
    let a_ref = Field25519Ref::random(&mut OsRng);
    let a = Field25519::from_repr(a_ref.to_repr()).expect("Failed to read scalar");
    assert_eq!(a.to_repr(), a_ref.to_repr());
    (a, a_ref)
}

pub fn test_gen_random_helios_point() -> (HeliosPoint, HeliosPointRef) {
    let A_ref = HeliosPointRef::random(&mut OsRng);
    let A = HeliosPoint::from_bytes(&A_ref.to_bytes()).expect("Failed to read helios point");
    assert_eq!(A.to_bytes(), A_ref.to_bytes());
    (A, A_ref)
}

pub fn test_gen_random_selene_point() -> (SelenePoint, SelenePointRef) {
    let A_ref = SelenePointRef::random(&mut OsRng);
    let A = SelenePoint::from_bytes(&A_ref.to_bytes()).expect("Failed to read selene point");
    assert_eq!(A.to_bytes(), A_ref.to_bytes());
    (A, A_ref)
}

#[cfg(target_arch = "wasm32")]
use getrandom::{register_custom_getrandom, Error};

// https://forum.dfinity.org/t/module-imports-function-wbindgen-describe-from-wbindgen-placeholder-that-is-not-exported-by-the-runtime/11545/8
#[cfg(target_arch = "wasm32")]
pub fn custom_getrandom(_buf: &mut [u8]) -> Result<(), Error> {
    unimplemented!("custom getrandom not implemented")
}

#[cfg(target_arch = "wasm32")]
register_custom_getrandom!(custom_getrandom);

// Tests for https://github.com/kayabaNerve/wasm-cycles
fn init_ref_helios_scalars(rng_seed: [u8; 32]) -> (HelioseleneFieldRef, HelioseleneFieldRef) {
    let mut rng = ChaCha20Rng::from_seed(rng_seed);
    let a = HelioseleneFieldRef::random(&mut rng);
    let b = HelioseleneFieldRef::random(&mut rng);
    (a, b)
}

fn init_contest_helios_scalars(rng_seed: [u8; 32]) -> (HelioseleneField, HelioseleneField) {
    let mut rng = ChaCha20Rng::from_seed(rng_seed);
    let a = HelioseleneField::random(&mut rng);
    let b = HelioseleneField::random(&mut rng);
    (a, b)
}

fn init_ref_selene_scalars(rng_seed: [u8; 32]) -> (Field25519Ref, Field25519Ref) {
    let mut rng = ChaCha20Rng::from_seed(rng_seed);
    let a = Field25519Ref::random(&mut rng);
    let b = Field25519Ref::random(&mut rng);
    (a, b)
}

fn init_contest_selene_scalars(rng_seed: [u8; 32]) -> (Field25519, Field25519) {
    let mut rng = ChaCha20Rng::from_seed(rng_seed);
    let a = Field25519::random(&mut rng);
    let b = Field25519::random(&mut rng);
    (a, b)
}

fn init_ref_helios_points(rng_seed: [u8; 32]) -> (HeliosPointRef, HeliosPointRef) {
    let mut rng = ChaCha20Rng::from_seed(rng_seed);
    let A = HeliosPointRef::random(&mut rng);
    let B = HeliosPointRef::random(&mut rng);
    (A, B)
}

fn init_contest_helios_points(rng_seed: [u8; 32]) -> (HeliosPoint, HeliosPoint) {
    let mut rng = ChaCha20Rng::from_seed(rng_seed);
    let A = HeliosPoint::random(&mut rng);
    let B = HeliosPoint::random(&mut rng);
    (A, B)
}

fn init_ref_selene_points(rng_seed: [u8; 32]) -> (SelenePointRef, SelenePointRef) {
    let mut rng = ChaCha20Rng::from_seed(rng_seed);
    let A = SelenePointRef::random(&mut rng);
    let B = SelenePointRef::random(&mut rng);
    (A, B)
}

fn init_contest_selene_points(rng_seed: [u8; 32]) -> (SelenePoint, SelenePoint) {
    let mut rng = ChaCha20Rng::from_seed(rng_seed);
    let A = SelenePoint::random(&mut rng);
    let B = SelenePoint::random(&mut rng);
    (A, B)
}

use std::sync::LazyLock;

macro_rules! curve_test_params {
    ($StructName:ident, $STRUCT_VAR_NAME:ident, $point_type: ident, $PointType:ident, $ScalarType:ident, $test_type:ident) => {
        paste! {
            struct $StructName {
                s1: $ScalarType,
                #[allow(dead_code)]
                s2: $ScalarType,
                A: $PointType,
                B: $PointType,
            }

            impl $StructName {
                pub fn new(rng_seed: [u8; 32]) -> Self {
                    let (s1, s2) = [<init_ $test_type _ $point_type _scalars>](rng_seed);
                    let (A, B) = [<init_ $test_type _ $point_type _points>](rng_seed);
                    Self {
                        s1,
                        s2,
                        A,
                        B,
                    }
                }
            }

            static mut $STRUCT_VAR_NAME: LazyLock<$StructName> = LazyLock::new(|| $StructName::new([0xff; 32]));
        }
    }
}

curve_test_params!(HeliosTestParamsRef, HELIOS_TEST_PARAMS_REF, helios, HeliosPointRef, HelioseleneFieldRef, ref);
curve_test_params!(SeleneTestParamsRef, SELENE_TEST_PARAMS_REF, selene, SelenePointRef, Field25519Ref, ref);

curve_test_params!(HeliosTestParams, HELIOS_TEST_PARAMS, helios, HeliosPoint, HelioseleneField, contest);
curve_test_params!(SeleneTestParams, SELENE_TEST_PARAMS, selene, SelenePoint, Field25519, contest);

// Use different rng seeds across cases
macro_rules! define_case {
    ($fn_name:ident, $STRUCT_VAR_NAME:ident, $StructName:ident) => {
        paste! {
            #[no_mangle]
            pub extern "C" fn [<case_ $fn_name _1>]() {
                unsafe { $STRUCT_VAR_NAME = LazyLock::new(|| $StructName::new([0xff; 32])) };
                // Read to initialize the struct
                let _ = unsafe { $STRUCT_VAR_NAME.s1 };
            }

            #[no_mangle]
            pub extern "C" fn [<case_ $fn_name _2>]() {
                unsafe { $STRUCT_VAR_NAME = LazyLock::new(|| $StructName::new([0xde; 32])) };
                // Read to initialize the struct
                let _ = unsafe { $STRUCT_VAR_NAME.s1 };
            }
        }
    };
}

macro_rules! define_cases {
    ($fn_name:ident, $STRUCT_VAR_NAME:ident, $StructName:ident) => {
        paste! {
            define_case!([<$fn_name _ref>], [<$STRUCT_VAR_NAME _REF>], [<$StructName Ref>]);
            define_case!([<$fn_name _contest>], $STRUCT_VAR_NAME, $StructName);
        }
    };
}

macro_rules! define_test_a_op_b {
    ($fn_name:ident, $op:tt) => {
        paste! {
            define_cases!($fn_name, HELIOS_TEST_PARAMS, HeliosTestParams);

            #[no_mangle]
            pub extern "C" fn [<test_ $fn_name _ref>]() {
                let (a, b) = unsafe { (HELIOS_TEST_PARAMS_REF.s1, HELIOS_TEST_PARAMS_REF.s2) };
                let _ = core::hint::black_box(a $op b);
            }

            #[no_mangle]
            pub extern "C" fn [<test_ $fn_name _contest>]() {
                let (a, b) = unsafe { (HELIOS_TEST_PARAMS.s1, HELIOS_TEST_PARAMS.s2) };
                let _ = core::hint::black_box(a $op b);
            }
        }
    };
}

macro_rules! define_test_a_dot_method {
    ($fn_name:ident, $method:ident) => {
        paste! {
            define_cases!($fn_name, HELIOS_TEST_PARAMS, HeliosTestParams);

            #[no_mangle]
            pub extern "C" fn [<test_ $fn_name _ref>]() {
                let a = unsafe { HELIOS_TEST_PARAMS_REF.s1 };
                let _ = core::hint::black_box(a.$method());
            }

            #[no_mangle]
            pub extern "C" fn [<test_ $fn_name _contest>]() {
                let a = unsafe { HELIOS_TEST_PARAMS.s1 };
                let _ = core::hint::black_box(a.$method());
            }
        }
    };
}

#[no_mangle]
pub extern "C" fn test_helioselene_sqrt_ref() {
    let a = unsafe { HELIOS_TEST_PARAMS_REF.s1 };
    let _ = core::hint::black_box(a.square().sqrt().unwrap());
}

#[no_mangle]
pub extern "C" fn test_helioselene_sqrt_contest() {
    let a = unsafe { HELIOS_TEST_PARAMS.s1 };
    let _ = core::hint::black_box(a.square().sqrt().unwrap());
}

#[no_mangle]
pub extern "C" fn test_helioselene_pow_ref() {
    let (a, b) = unsafe { (HELIOS_TEST_PARAMS_REF.s1, HELIOS_TEST_PARAMS_REF.s2) };
    let _ = core::hint::black_box(a.pow(b));
}

#[no_mangle]
pub extern "C" fn test_helioselene_pow_contest() {
    let (a, b) = unsafe { (HELIOS_TEST_PARAMS.s1, HELIOS_TEST_PARAMS.s2) };
    let _ = core::hint::black_box(a.pow(b));
}

#[no_mangle]
pub extern "C" fn test_helioselene_neg_ref() {
    let a = unsafe { HELIOS_TEST_PARAMS_REF.s1 };
    let _ = core::hint::black_box(-a);
}

#[no_mangle]
pub extern "C" fn test_helioselene_neg_contest() {
    let a = unsafe { HELIOS_TEST_PARAMS.s1 };
    let _ = core::hint::black_box(-a);
}

macro_rules! define_point_tests {
    ($point_name:ident, $PointType:ident, $STRUCT_VAR_NAME:ident, $StructName:ident) => {
        paste! {
            define_cases!([<$point_name _add>], $STRUCT_VAR_NAME, $StructName);
            define_cases!([<$point_name _mul>], $STRUCT_VAR_NAME, $StructName);
            define_cases!([<$point_name _mul_by_generator>], $STRUCT_VAR_NAME, $StructName);
            define_cases!([<$point_name _sub>], $STRUCT_VAR_NAME, $StructName);
            define_cases!([<$point_name _dbl>], $STRUCT_VAR_NAME, $StructName);
            define_cases!([<$point_name _neg>], $STRUCT_VAR_NAME, $StructName);
            define_cases!([<$point_name _compression>], $STRUCT_VAR_NAME, $StructName);
            define_cases!([<$point_name _decompression>], $STRUCT_VAR_NAME, $StructName);

            #[no_mangle]
            pub extern "C" fn [<test_ $point_name _add_ref>]() {
                let (A, B) = unsafe { ([<$STRUCT_VAR_NAME _REF>].A, [<$STRUCT_VAR_NAME _REF>].B) };
                let _ = core::hint::black_box(A + B);
            }

            #[no_mangle]
            pub extern "C" fn [<test_ $point_name _add_contest>]() {
                let (A, B) = unsafe { ($STRUCT_VAR_NAME.A, $STRUCT_VAR_NAME.B) };
                let _ = core::hint::black_box(A + B);
            }

            #[no_mangle]
            pub extern "C" fn [<test_ $point_name _mul_ref>]() {
                let (A, s) = unsafe { ([<$STRUCT_VAR_NAME _REF>].A, [<$STRUCT_VAR_NAME _REF>].s1) };
                let _ = core::hint::black_box(A * s);
            }

            #[no_mangle]
            pub extern "C" fn [<test_ $point_name _mul_contest>]() {
                let (A, s) = unsafe { ($STRUCT_VAR_NAME.A, $STRUCT_VAR_NAME.s1) };
                let _ = core::hint::black_box(A * s);
            }

            #[no_mangle]
            pub extern "C" fn [<test_ $point_name _mul_by_generator_ref>]() {
                let a = unsafe { [<$STRUCT_VAR_NAME _REF>].s1 };
                let _ = core::hint::black_box([<$PointType Ref>]::generator() * a);
            }

            #[no_mangle]
            pub extern "C" fn [<test_ $point_name _mul_by_generator_contest>]() {
                let a = unsafe { $STRUCT_VAR_NAME.s1 };
                let _ = core::hint::black_box($PointType::generator() * a);
            }

            #[no_mangle]
            pub extern "C" fn [<test_ $point_name _sub_ref>]() {
                let (A, B) = unsafe { ([<$STRUCT_VAR_NAME _REF>].A, [<$STRUCT_VAR_NAME _REF>].B) };
                let _ = core::hint::black_box(A - B);
            }

            #[no_mangle]
            pub extern "C" fn [<test_ $point_name _sub_contest>]() {
                let (A, B) = unsafe { ($STRUCT_VAR_NAME.A, $STRUCT_VAR_NAME.B) };
                let _ = core::hint::black_box(A - B);
            }

            #[no_mangle]
            pub extern "C" fn [<test_ $point_name _dbl_ref>]() {
                let A = unsafe { [<$STRUCT_VAR_NAME _REF>].A };
                let _ = core::hint::black_box(A.double());
            }

            #[no_mangle]
            pub extern "C" fn [<test_ $point_name _dbl_contest>]() {
                let A = unsafe { $STRUCT_VAR_NAME.A };
                let _ = core::hint::black_box(A.double());
            }

            #[no_mangle]
            pub extern "C" fn [<test_ $point_name _compression_ref>]() {
                let A = unsafe { [<$STRUCT_VAR_NAME _REF>].A };
                let _ = core::hint::black_box(A.to_bytes());
            }

            #[no_mangle]
            pub extern "C" fn [<test_ $point_name _compression_contest>]() {
                let A = unsafe { $STRUCT_VAR_NAME.A };
                let _ = core::hint::black_box(A.to_bytes());
            }

            #[no_mangle]
            pub extern "C" fn [<test_ $point_name _decompression_ref>]() {
                let A = unsafe { [<$STRUCT_VAR_NAME _REF>].A };
                let _ = core::hint::black_box([<$PointType Ref>]::from_bytes(&A.to_bytes()).unwrap());
            }

            #[no_mangle]
            pub extern "C" fn [<test_ $point_name _decompression_contest>]() {
                let A = unsafe { $STRUCT_VAR_NAME.A };
                let _ = core::hint::black_box($PointType::from_bytes(&A.to_bytes()).unwrap());
            }
        }
    };
}

// Field wasm tests
define_test_a_op_b!(helioselene_add, +);
define_test_a_op_b!(helioselene_mul, *);
define_test_a_op_b!(helioselene_sub, -);
define_test_a_dot_method!(helioselene_sq, square);
define_test_a_dot_method!(helioselene_dbl, double);
define_test_a_dot_method!(helioselene_inv, invert);
define_test_a_dot_method!(helioselene_odd, is_odd);
define_test_a_dot_method!(helioselene_evn, is_even);
define_cases!(helioselene_sqrt, HELIOS_TEST_PARAMS, HeliosTestParams);
define_cases!(helioselene_pow, HELIOS_TEST_PARAMS, HeliosTestParams);
define_cases!(helioselene_neg, HELIOS_TEST_PARAMS, HeliosTestParams);

// Point wasm tests
define_point_tests!(helios, HeliosPoint, HELIOS_TEST_PARAMS, HeliosTestParams);
define_point_tests!(selene, SelenePoint, SELENE_TEST_PARAMS, SeleneTestParams);
