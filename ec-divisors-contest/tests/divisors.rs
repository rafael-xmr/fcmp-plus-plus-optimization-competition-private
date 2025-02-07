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

fn scalar_mul_divisor_ref(
    generator: &EdwardsPoint,
    scalar: &ScalarDecompositionRef<Scalar>,
) -> PolyRef<FieldElement> {
    scalar.scalar_mul_divisor(*generator)
}

fn scalar_mul_divisor_contest(
    generator: &EdwardsPoint,
    scalar: &ScalarDecomposition<Scalar>,
) -> Poly<FieldElement> {
    scalar.scalar_mul_divisor(*generator)
}

fn init_ref(point: &EdwardsPoint, scalar: &Scalar) -> ScalarDecompositionRef<Scalar> {
    let scalar = ScalarDecompositionRef::new(*scalar).unwrap();
    let point = Zeroizing::new(*point * scalar.scalar());
    let (_, _) = <EdwardsPoint as DivisorCurveRef>::to_xy(*point).unwrap();
    scalar
}

fn init_contest(point: &EdwardsPoint, scalar: &Scalar) -> ScalarDecomposition<Scalar> {
    let scalar = ScalarDecomposition::new(*scalar).expect("failed scalar decompsition");
    let point = Zeroizing::new(*point * scalar.scalar());
    let (_, _) = <EdwardsPoint as DivisorCurve>::to_xy(*point).expect("zero scalar was decomposed");
    scalar
}

static N_ITERS: usize = 20;

#[test]
fn divisors_contest_test() {
    // Test that the implementation in ./src produces the same result as the reference implementation
    for i in 0..N_ITERS {
        println!("Testing with random scalar {} / {}", i + 1, N_ITERS);

        let point = EdwardsPoint::generator();
        let rand_scalar = <Ed25519 as Ciphersuite>::F::random(&mut OsRng);

        // Get scalar decompositions
        let scalar_ref = init_ref(&point, &rand_scalar);
        let scalar_contest = init_contest(&point, &rand_scalar);

        // Get divisors
        let ref_res = scalar_mul_divisor_ref(&point, &scalar_ref);
        let res = scalar_mul_divisor_contest(&point, &scalar_contest);

        assert_eq!(ref_res.y_coefficients, res.y_coefficients);
        assert_eq!(ref_res.yx_coefficients, res.yx_coefficients);
        assert_eq!(ref_res.x_coefficients, res.x_coefficients);
        assert_eq!(ref_res.zero_coefficient, res.zero_coefficient);
    }
}
