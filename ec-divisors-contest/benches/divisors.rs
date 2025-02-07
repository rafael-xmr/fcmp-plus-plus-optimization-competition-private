use ec_divisors::{DivisorCurve as DivisorCurveRef, ScalarDecomposition as ScalarDecompositionRef};
use ec_divisors_contest::{DivisorCurve, ScalarDecomposition};

use ciphersuite::{
    group::{ff::Field, Group},
    Ciphersuite, Ed25519,
};
use dalek_ff_group::{EdwardsPoint, Scalar};

use rand_core::OsRng;
use zeroize::Zeroizing;

use criterion::{criterion_group, criterion_main, Criterion};

fn scalar_mul_divisor_ref(generator: &EdwardsPoint, scalar: &ScalarDecompositionRef<Scalar>) {
    let _ = scalar.scalar_mul_divisor(*generator);
}

fn scalar_mul_divisor_contest(generator: &EdwardsPoint, scalar: &ScalarDecomposition<Scalar>) {
    let _ = scalar.scalar_mul_divisor(*generator);
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

fn bench_scalar_mul_divisors(c: &mut Criterion) {
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

criterion_group!(benches, bench_scalar_mul_divisors);
criterion_main!(benches);
