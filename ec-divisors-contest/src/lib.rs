use ec_divisors::{DivisorCurve as DivisorCurveRef, ScalarDecomposition as ScalarDecompositionRef};
use ec_divisors_contest_src::{DivisorCurve, ScalarDecomposition};

use ciphersuite::{
    group::{ff::Field, Group},
    Ciphersuite, Ed25519,
};
use dalek_ff_group::{EdwardsPoint, Scalar};

use zeroize::Zeroizing;

use rand_chacha::ChaCha20Rng;
use rand_core::SeedableRng;

pub fn init_ref(point: &EdwardsPoint, scalar: &Scalar) -> ScalarDecompositionRef<Scalar> {
    let scalar = ScalarDecompositionRef::new(*scalar).unwrap();
    let point = Zeroizing::new(*point * scalar.scalar());
    let (_, _) = <EdwardsPoint as DivisorCurveRef>::to_xy(*point).unwrap();
    scalar
}

pub fn init_contest(point: &EdwardsPoint, scalar: &Scalar) -> ScalarDecomposition<Scalar> {
    let scalar = ScalarDecomposition::new(*scalar).expect("failed scalar decompsition");
    let point = Zeroizing::new(*point * scalar.scalar());
    let (_, _) = <EdwardsPoint as DivisorCurve>::to_xy(*point).expect("zero scalar was decomposed");
    scalar
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
#[no_mangle]
pub extern "C" fn case_scalar_mul_divisor_ref1() {
    unsafe { RNG_SEED = [0xff; 32] };
}

#[no_mangle]
pub extern "C" fn case_scalar_mul_divisor_ref2() {
    unsafe { RNG_SEED = [0xde; 32] };
}

#[no_mangle]
pub extern "C" fn case_scalar_mul_divisor_contest1() {
    unsafe { RNG_SEED = [0xff; 32] };
}

#[no_mangle]
pub extern "C" fn case_scalar_mul_divisor_contest2() {
    unsafe { RNG_SEED = [0xde; 32] };
}

#[no_mangle]
pub extern "C" fn test_scalar_mul_divisor_ref() {
    // Makes sure reference impl is constant time
    let point = EdwardsPoint::generator();
    let mut rng = unsafe { ChaCha20Rng::from_seed(RNG_SEED) };
    let rand_scalar = <Ed25519 as Ciphersuite>::F::random(&mut rng);
    // FIXME: wasm-cycles fails because of the scalar decomposition in this line, even when using an equivalent RNG_SEED across cases
    let _ = core::hint::black_box(init_ref(&point, &rand_scalar));
    // FIXME: uncomment below
    // core::hint::black_box(scalar.scalar_mul_divisor(point));
}

#[no_mangle]
pub extern "C" fn test_scalar_mul_divisor_contest() {
    let point = EdwardsPoint::generator();
    let mut rng = unsafe { ChaCha20Rng::from_seed(RNG_SEED) };
    let rand_scalar = <Ed25519 as Ciphersuite>::F::random(&mut rng);
    // FIXME: wasm-cycles fails because of the scalar decomposition in this line, even when using an equivalent RNG_SEED across cases
    let _ = core::hint::black_box(init_contest(&point, &rand_scalar));
    // FIXME: uncomment below
    // core::hint::black_box(scalar.scalar_mul_divisor(point));
}
