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
fn init_ref_scalars() -> (HelioseleneFieldRef, HelioseleneFieldRef) {
    let mut rng = unsafe { ChaCha20Rng::from_seed(RNG_SEED) };
    let a = HelioseleneFieldRef::random(&mut rng);
    let b = HelioseleneFieldRef::random(&mut rng);
    (a, b)
}

fn init_contest_scalars() -> (HelioseleneField, HelioseleneField) {
    let mut rng = unsafe { ChaCha20Rng::from_seed(RNG_SEED) };
    let a = HelioseleneField::random(&mut rng);
    let b = HelioseleneField::random(&mut rng);
    (a, b)
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
                let (a, b) = core::hint::black_box(init_ref_scalars());
                let _ = core::hint::black_box(a $op b);
            }

            #[no_mangle]
            pub extern "C" fn [<test_ $fn_name _contest>]() {
                let (a, b) = core::hint::black_box(init_contest_scalars());
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
                let (a, _) = core::hint::black_box(init_ref_scalars());
                let _ = core::hint::black_box(a.$method());
            }

            #[no_mangle]
            pub extern "C" fn [<test_ $fn_name _contest>]() {
                let (a, _) = core::hint::black_box(init_contest_scalars());
                let _ = core::hint::black_box(a.$method());
            }
        }
    };
}

#[no_mangle]
pub extern "C" fn test_helioselene_sqrt_ref() {
    let (a, _) = core::hint::black_box(init_ref_scalars());
    let _ = core::hint::black_box(a.square().sqrt().unwrap());
}

#[no_mangle]
pub extern "C" fn test_helioselene_sqrt_contest() {
    let (a, _) = core::hint::black_box(init_contest_scalars());
    let _ = core::hint::black_box(a.square().sqrt().unwrap());
}

#[no_mangle]
pub extern "C" fn test_helioselene_pow_ref() {
    let (a, b) = core::hint::black_box(init_ref_scalars());
    let _ = core::hint::black_box(a.pow(b));
}

#[no_mangle]
pub extern "C" fn test_helioselene_pow_contest() {
    let (a, b) = core::hint::black_box(init_contest_scalars());
    let _ = core::hint::black_box(a.pow(b));
}

#[no_mangle]
pub extern "C" fn test_helioselene_neg_ref() {
    let (a, _) = core::hint::black_box(init_ref_scalars());
    let _ = core::hint::black_box(-a);
}

#[no_mangle]
pub extern "C" fn test_helioselene_neg_contest() {
    let (a, _) = core::hint::black_box(init_contest_scalars());
    let _ = core::hint::black_box(-a);
}

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
