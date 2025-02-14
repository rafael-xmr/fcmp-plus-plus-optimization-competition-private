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

use std::sync::LazyLock;

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

// https://forum.dfinity.org/t/module-imports-function-wbindgen-describe-from-wbindgen-placeholder-that-is-not-exported-by-the-runtime/11545/8
#[cfg(target_arch = "wasm32")]
pub fn custom_getrandom(_buf: &mut [u8]) -> Result<(), Error> {
    unimplemented!("custom_getrandom not implemented");
}

#[cfg(target_arch = "wasm32")]
register_custom_getrandom!(custom_getrandom);

struct EcDivisorsParamsRef {
    point: EdwardsPoint,
    scalar: ScalarDecompositionRef<Scalar>,
}

struct EcDivisorsParams {
    point: EdwardsPoint,
    scalar: ScalarDecomposition<Scalar>,
}

impl EcDivisorsParamsRef {
    pub fn new(rng_seed: [u8; 32]) -> Self {
        let point = EdwardsPoint::generator();
        let mut rng = ChaCha20Rng::from_seed(rng_seed);
        let rand_scalar = <Ed25519 as Ciphersuite>::F::random(&mut rng);
        let scalar = init_ref(&point, &rand_scalar);
        Self { point, scalar }
    }
}

impl EcDivisorsParams {
    pub fn new(rng_seed: [u8; 32]) -> Self {
        let point = EdwardsPoint::generator();
        let mut rng = ChaCha20Rng::from_seed(rng_seed);
        let rand_scalar = <Ed25519 as Ciphersuite>::F::random(&mut rng);
        let scalar = init_contest(&point, &rand_scalar);
        Self { point, scalar }
    }
}

static mut EC_DIVISORS_PARAMS: LazyLock<EcDivisorsParams> =
    LazyLock::new(|| EcDivisorsParams::new([0xff; 32]));
static mut EC_DIVISORS_PARAMS_REF: LazyLock<EcDivisorsParamsRef> =
    LazyLock::new(|| EcDivisorsParamsRef::new([0xff; 32]));

// Tests using different seed with for https://github.com/kayabaNerve/wasm-cycles
#[no_mangle]
pub extern "C" fn case_scalar_mul_divisor_ref1() {
    unsafe { EC_DIVISORS_PARAMS_REF = LazyLock::new(|| EcDivisorsParamsRef::new([0xff; 32])) };
    let _ = unsafe { EC_DIVISORS_PARAMS_REF.point };
}

#[no_mangle]
pub extern "C" fn case_scalar_mul_divisor_ref2() {
    unsafe { EC_DIVISORS_PARAMS_REF = LazyLock::new(|| EcDivisorsParamsRef::new([0xde; 32])) };
    let _ = unsafe { EC_DIVISORS_PARAMS_REF.point };
}

#[no_mangle]
pub extern "C" fn case_scalar_mul_divisor_contest1() {
    unsafe { EC_DIVISORS_PARAMS = LazyLock::new(|| EcDivisorsParams::new([0xff; 32])) };
    let _ = unsafe { EC_DIVISORS_PARAMS.point };
}

#[no_mangle]
pub extern "C" fn case_scalar_mul_divisor_contest2() {
    unsafe { EC_DIVISORS_PARAMS = LazyLock::new(|| EcDivisorsParams::new([0xde; 32])) };
    let _ = unsafe { EC_DIVISORS_PARAMS.point };
}

#[no_mangle]
pub extern "C" fn test_scalar_mul_divisor_ref() {
    #[allow(static_mut_refs)]
    core::hint::black_box(unsafe {
        EC_DIVISORS_PARAMS_REF
            .scalar
            .scalar_mul_divisor(EC_DIVISORS_PARAMS_REF.point)
    });
}

#[no_mangle]
pub extern "C" fn test_scalar_mul_divisor_contest() {
    #[allow(static_mut_refs)]
    core::hint::black_box(unsafe {
        EC_DIVISORS_PARAMS
            .scalar
            .scalar_mul_divisor(EC_DIVISORS_PARAMS.point)
    });
}
