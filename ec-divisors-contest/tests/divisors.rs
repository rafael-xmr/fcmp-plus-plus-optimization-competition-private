use ec_divisors::{
    DivisorCurve as DivisorCurveRef, Poly as PolyRef, ScalarDecomposition as ScalarDecompositionRef,
};
use ec_divisors_contest::{DivisorCurve, Poly, ScalarDecomposition};

use ciphersuite::{
    group::{ff::Field, Group},
    Ciphersuite, Ed25519,
};
use dalek_ff_group::{EdwardsPoint, FieldElement, Scalar};

use rand_core::OsRng;
use zeroize::Zeroizing;

#[allow(non_snake_case)]
fn scalar_mul_divisor_ref(
    A: &EdwardsPoint,
    scalar: &ScalarDecompositionRef<Scalar>,
) -> PolyRef<FieldElement> {
    scalar.scalar_mul_divisor(*A)
}

#[allow(non_snake_case)]
fn scalar_mul_divisor_contest(
    A: &EdwardsPoint,
    scalar: &ScalarDecomposition<Scalar>,
) -> Poly<FieldElement> {
    scalar.scalar_mul_divisor(*A)
}

#[allow(non_snake_case)]
fn init_ref(scalar: &Scalar) -> (EdwardsPoint, ScalarDecompositionRef<Scalar>) {
    let G = EdwardsPoint::generator();
    let scalar = ScalarDecompositionRef::new(*scalar).unwrap();
    let point = Zeroizing::new(G * scalar.scalar());
    let (_, _) = <EdwardsPoint as DivisorCurveRef>::to_xy(*point).unwrap();
    (G, scalar)
}

#[allow(non_snake_case)]
fn init_contest(scalar: &Scalar) -> (EdwardsPoint, ScalarDecomposition<Scalar>) {
    let G = EdwardsPoint::generator();
    let scalar = ScalarDecomposition::new(*scalar).expect("failed scalar decompsition");
    let point = Zeroizing::new(G * scalar.scalar());
    let (_, _) = <EdwardsPoint as DivisorCurve>::to_xy(*point).expect("zero scalar was decomposed");
    (G, scalar)
}

static N_ITERS: usize = 20;

#[test]
fn divisors_contest_test() {
    for i in 0..N_ITERS {
        println!("Testing with random scalar {} / {}", i + 1, N_ITERS);

        let rand_scalar = <Ed25519 as Ciphersuite>::F::random(&mut OsRng);

        // Get scalar decompositions
        let (point_ref, scalar_ref) = init_ref(&rand_scalar);
        let (point_contest, scalar_contest) = init_contest(&rand_scalar);

        // Get divisors
        let ref_res = scalar_mul_divisor_ref(&point_ref, &scalar_ref);
        let res = scalar_mul_divisor_contest(&point_contest, &scalar_contest);

        assert_eq!(ref_res.y_coefficients, res.y_coefficients);
        assert_eq!(ref_res.yx_coefficients, res.yx_coefficients);
        assert_eq!(ref_res.x_coefficients, res.x_coefficients);
        assert_eq!(ref_res.zero_coefficient, res.zero_coefficient);
    }
}
