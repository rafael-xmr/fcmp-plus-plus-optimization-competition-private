use ec_divisors::{
    DivisorCurve as DivisorCurveRef, Poly as PolyRef, ScalarDecomposition as ScalarDecompositionRef,
};
use ec_divisors_contest_src::{DivisorCurve, Poly, ScalarDecomposition};

use ciphersuite::{
    group::{ff::Field, Group},
    Ciphersuite, Ed25519,
};
use dalek_ff_group::{EdwardsPoint, FieldElement, Scalar};

use rand_core::OsRng;
use zeroize::Zeroizing;

use criterion::{criterion_group, criterion_main, Criterion};

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

// Test that the implementation in ../ec-divisors-contest-src produces the same
// result as the reference implementation
pub fn test_scalar_mul_divisors() {
    static N_ITERS: usize = 20;

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

// Benchmark the reference implementation and the implementation in
// ../ec-divisors-contest-src
fn run_bench_scalar_mul_divisors(c: &mut Criterion) {
    let mut group = c.benchmark_group("ec-divisors");

    let point = EdwardsPoint::generator();
    let rand_scalar = <Ed25519 as Ciphersuite>::F::random(&mut OsRng);

    // Get scalar decompositions
    let scalar_ref = init_ref(&point, &rand_scalar);
    let scalar_contest = init_contest(&point, &rand_scalar);

    // Run the benchmark for the reference implementation
    group.bench_function("reference-impl", |b| {
        b.iter(|| scalar_mul_divisor_ref(&point, &scalar_ref))
    });

    // Run the benchmark for the contest implementation
    group.bench_function("contest-impl", |b| {
        b.iter(|| scalar_mul_divisor_contest(&point, &scalar_contest))
    });

    group.finish();
}

pub fn bench_scalar_mul_divisors() {
    let mut c = Criterion::default();
    run_bench_scalar_mul_divisors(&mut c);
}

criterion_group!(benches, run_bench_scalar_mul_divisors);
criterion_main!(benches);
