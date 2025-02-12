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
#[cfg(target_arch = "wasm32")]
use rand_core::RngCore;

static mut RNG_SEED: [u8; 32] = [0xff; 32];

// https://forum.dfinity.org/t/module-imports-function-wbindgen-describe-from-wbindgen-placeholder-that-is-not-exported-by-the-runtime/11545/8
#[cfg(target_arch = "wasm32")]
pub fn custom_getrandom(buf: &mut [u8]) -> Result<(), Error> {
    let mut rng = unsafe { ChaCha20Rng::from_seed(RNG_SEED) };
    rng.fill_bytes(buf);
    Ok(())
}

#[cfg(target_arch = "wasm32")]
register_custom_getrandom!(custom_getrandom);

// Tests for https://github.com/kayabaNerve/wasm-cycles
fn init_ref_helios_scalars() -> (HelioseleneFieldRef, HelioseleneFieldRef) {
    let mut rng = unsafe { ChaCha20Rng::from_seed(RNG_SEED) };
    let a = HelioseleneFieldRef::random(&mut rng);
    let b = HelioseleneFieldRef::random(&mut rng);
    (a, b)
}

fn init_contest_helios_scalars() -> (HelioseleneField, HelioseleneField) {
    let mut rng = unsafe { ChaCha20Rng::from_seed(RNG_SEED) };
    let a = HelioseleneField::random(&mut rng);
    let b = HelioseleneField::random(&mut rng);
    (a, b)
}

fn init_ref_selene_scalars() -> (Field25519Ref, Field25519Ref) {
    let mut rng = unsafe { ChaCha20Rng::from_seed(RNG_SEED) };
    let a = Field25519Ref::random(&mut rng);
    let b = Field25519Ref::random(&mut rng);
    (a, b)
}

fn init_contest_selene_scalars() -> (Field25519, Field25519) {
    let mut rng = unsafe { ChaCha20Rng::from_seed(RNG_SEED) };
    let a = Field25519::random(&mut rng);
    let b = Field25519::random(&mut rng);
    (a, b)
}

// Get random scalar first and mul by G to guarantee constant time
fn init_ref_helios_points() -> (HeliosPointRef, HeliosPointRef) {
    let (a, b) = init_ref_helios_scalars();
    let A = HeliosPointRef::generator() * a;
    let B = HeliosPointRef::generator() * b;
    (A, B)
}

fn init_contest_helios_points() -> (HeliosPoint, HeliosPoint) {
    let (a, b) = init_contest_helios_scalars();
    let A = HeliosPoint::generator() * a;
    let B = HeliosPoint::generator() * b;
    (A, B)
}

fn init_ref_selene_points() -> (SelenePointRef, SelenePointRef) {
    let (a, b) = init_ref_selene_scalars();
    let A = SelenePointRef::generator() * a;
    let B = SelenePointRef::generator() * b;
    (A, B)
}

fn init_contest_selene_points() -> (SelenePoint, SelenePoint) {
    let (a, b) = init_contest_selene_scalars();
    let A = SelenePoint::generator() * a;
    let B = SelenePoint::generator() * b;
    (A, B)
}

macro_rules! define_case {
    ($fn_name:ident) => {
        paste! {
            #[no_mangle]
            pub extern "C" fn [<case_ $fn_name _1>]() {
                unsafe { RNG_SEED =  [0xff; 32]};
            }

            #[no_mangle]
            pub extern "C" fn [<case_ $fn_name _2>]() {
                unsafe { RNG_SEED =  [0xde; 32]};
            }
        }
    };
}

macro_rules! define_cases {
    ($fn_name:ident) => {
        paste! {
            define_case!([<$fn_name _ref>]);
            define_case!([<$fn_name _contest>]);
        }
    }
}

macro_rules! define_test_a_op_b {
    ($fn_name:ident, $op:tt) => {
        paste! {
            define_cases!($fn_name);

            #[no_mangle]
            pub extern "C" fn [<test_ $fn_name _ref>]() {
                let (a, b) = core::hint::black_box(init_ref_helios_scalars());
                let _ = core::hint::black_box(a $op b);
            }

            #[no_mangle]
            pub extern "C" fn [<test_ $fn_name _contest>]() {
                let (a, b) = core::hint::black_box(init_contest_helios_scalars());
                let _ = core::hint::black_box(a $op b);
            }
        }
    };
}

macro_rules! define_test_a_dot_method {
    ($fn_name:ident, $method:ident) => {
        paste! {
            define_cases!($fn_name);

            #[no_mangle]
            pub extern "C" fn [<test_ $fn_name _ref>]() {
                let (a, _) = core::hint::black_box(init_ref_helios_scalars());
                let _ = core::hint::black_box(a.$method());
            }

            #[no_mangle]
            pub extern "C" fn [<test_ $fn_name _contest>]() {
                let (a, _) = core::hint::black_box(init_contest_helios_scalars());
                let _ = core::hint::black_box(a.$method());
            }
        }
    };
}

#[no_mangle]
pub extern "C" fn test_helioselene_sqrt_ref() {
    let (a, _) = core::hint::black_box(init_ref_helios_scalars());
    let _ = core::hint::black_box(a.square().sqrt().unwrap());
}

#[no_mangle]
pub extern "C" fn test_helioselene_sqrt_contest() {
    let (a, _) = core::hint::black_box(init_contest_helios_scalars());
    let _ = core::hint::black_box(a.square().sqrt().unwrap());
}

#[no_mangle]
pub extern "C" fn test_helioselene_pow_ref() {
    let (a, b) = core::hint::black_box(init_ref_helios_scalars());
    let _ = core::hint::black_box(a.pow(b));
}

#[no_mangle]
pub extern "C" fn test_helioselene_pow_contest() {
    let (a, b) = core::hint::black_box(init_contest_helios_scalars());
    let _ = core::hint::black_box(a.pow(b));
}

#[no_mangle]
pub extern "C" fn test_helioselene_neg_ref() {
    let (a, _) = core::hint::black_box(init_ref_helios_scalars());
    let _ = core::hint::black_box(-a);
}

#[no_mangle]
pub extern "C" fn test_helioselene_neg_contest() {
    let (a, _) = core::hint::black_box(init_contest_helios_scalars());
    let _ = core::hint::black_box(-a);
}

macro_rules! define_point_tests {
    ($point_name:ident, $typename:ident) => {
        paste! {
            define_cases!([<$point_name _init_points>]);
            define_cases!([<$point_name _init_scalars>]);
            define_cases!([<$point_name _add>]);
            define_cases!([<$point_name _mul>]);
            define_cases!([<$point_name _mul_by_generator>]);
            define_cases!([<$point_name _sub>]);
            define_cases!([<$point_name _dbl>]);
            define_cases!([<$point_name _neg>]);
            define_cases!([<$point_name _compression>]);
            define_cases!([<$point_name _decompression>]);

            // init_points and init_scalars are useful to noramlize final
            // results (subtract respective cycles to init from cycle count)
            #[no_mangle]
            pub extern "C" fn [<test_ $point_name _init_points_ref>]() {
                let (_, _) = core::hint::black_box([<init_ref_ $point_name _points>]());
            }

            #[no_mangle]
            pub extern "C" fn [<test_ $point_name _init_points_contest>]() {
                let (_, _) = core::hint::black_box([<init_contest_ $point_name _points>]());
            }

            #[no_mangle]
            pub extern "C" fn [<test_ $point_name _init_scalars_ref>]() {
                let (_, _) = core::hint::black_box([<init_ref_ $point_name _scalars>]());
            }

            #[no_mangle]
            pub extern "C" fn [<test_ $point_name _init_scalars_contest>]() {
                let (_, _) = core::hint::black_box([<init_contest_ $point_name _scalars>]());
            }

            #[no_mangle]
            pub extern "C" fn [<test_ $point_name _add_ref>]() {
                let (A, B) = core::hint::black_box([<init_ref_ $point_name _points>]());
                let _ = core::hint::black_box(A + B);
            }

            #[no_mangle]
            pub extern "C" fn [<test_ $point_name _add_contest>]() {
                let (A, B) = core::hint::black_box([<init_contest_ $point_name _points>]());
                let _ = core::hint::black_box(A + B);
            }

            #[no_mangle]
            pub extern "C" fn [<test_ $point_name _mul_ref>]() {
                let (A, _) = core::hint::black_box([<init_ref_ $point_name _points>]());
                let (s, _) = core::hint::black_box([<init_ref_ $point_name _scalars>]());
                let _ = core::hint::black_box(A * s);
            }

            #[no_mangle]
            pub extern "C" fn [<test_ $point_name _mul_contest>]() {
                let (A, _) = core::hint::black_box([<init_contest_ $point_name _points>]());
                let (s, _) = core::hint::black_box([<init_contest_ $point_name _scalars>]());
                let _ = core::hint::black_box(A * s);
            }

            #[no_mangle]
            pub extern "C" fn [<test_ $point_name _mul_by_generator_ref>]() {
                let (a, _) = core::hint::black_box([<init_ref_ $point_name _scalars>]());
                let _ = core::hint::black_box([<$typename PointRef>]::generator() * a);
            }

            #[no_mangle]
            pub extern "C" fn [<test_ $point_name _mul_by_generator_contest>]() {
                let (a, _) = core::hint::black_box([<init_contest_ $point_name _scalars>]());
                let _ = core::hint::black_box([<$typename Point>]::generator() * a);
            }

            #[no_mangle]
            pub extern "C" fn [<test_ $point_name _sub_ref>]() {
                let (A, B) = core::hint::black_box([<init_ref_ $point_name _points>]());
                let _ = core::hint::black_box(A - B);
            }

            #[no_mangle]
            pub extern "C" fn [<test_ $point_name _sub_contest>]() {
                let (A, B) = core::hint::black_box([<init_contest_ $point_name _points>]());
                let _ = core::hint::black_box(A - B);
            }

            #[no_mangle]
            pub extern "C" fn [<test_ $point_name _dbl_ref>]() {
                let (A, _) = core::hint::black_box([<init_ref_ $point_name _points>]());
                let _ = core::hint::black_box(A.double());
            }

            #[no_mangle]
            pub extern "C" fn [<test_ $point_name _dbl_contest>]() {
                let (A, _) = core::hint::black_box([<init_contest_ $point_name _points>]());
                let _ = core::hint::black_box(A.double());
            }

            #[no_mangle]
            pub extern "C" fn [<test_ $point_name _compression_ref>]() {
                let (A, _) = core::hint::black_box([<init_ref_ $point_name _points>]());
                let _ = core::hint::black_box(A.to_bytes());
            }

            #[no_mangle]
            pub extern "C" fn [<test_ $point_name _compression_contest>]() {
                let (A, _) = core::hint::black_box([<init_contest_ $point_name _points>]());
                let _ = core::hint::black_box(A.to_bytes());
            }

            #[no_mangle]
            pub extern "C" fn [<test_ $point_name _decompression_ref>]() {
                let (A, _) = core::hint::black_box([<init_ref_ $point_name _points>]());
                let _ = core::hint::black_box([<$typename PointRef>]::from_bytes(&A.to_bytes()).unwrap());
            }

            #[no_mangle]
            pub extern "C" fn [<test_ $point_name _decompression_contest>]() {
                let (A, _) = core::hint::black_box([<init_contest_ $point_name _points>]());
                let _ = core::hint::black_box([<$typename Point>]::from_bytes(&A.to_bytes()).unwrap());
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
define_cases!(helioselene_sqrt);
define_cases!(helioselene_pow);
define_cases!(helioselene_neg);

// Point wasm tests
define_point_tests!(helios, Helios);
define_point_tests!(selene, Selene);
