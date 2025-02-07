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

#[allow(non_snake_case)]
fn scalar_mul_divisor_ref(A: &EdwardsPoint, scalar: &ScalarDecompositionRef<Scalar>) {
    let _ = scalar.scalar_mul_divisor(*A);
}

#[allow(non_snake_case)]
fn scalar_mul_divisor_contest(A: &EdwardsPoint, scalar: &ScalarDecomposition<Scalar>) {
    let _ = scalar.scalar_mul_divisor(*A);
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

fn bench_scalar_mul_divisors(c: &mut Criterion) {
    let mut group = c.benchmark_group("ec-divisors");

    let rand_scalar = <Ed25519 as Ciphersuite>::F::random(&mut OsRng);

    // Get scalar decompositions
    let (point_ref, scalar_ref) = init_ref(&rand_scalar);
    let (point_contest, scalar_contest) = init_contest(&rand_scalar);

    // Run the benchmark for the reference implementation
    group.bench_function("reference-impl", |b| {
        b.iter(|| scalar_mul_divisor_ref(&point_ref, &scalar_ref))
    });

    // Run the benchmark for the contest implementation
    group.bench_function("contest-impl", |b| {
        b.iter(|| scalar_mul_divisor_contest(&point_contest, &scalar_contest))
    });

    group.finish();
}

criterion_group!(benches, bench_scalar_mul_divisors);
criterion_main!(benches);
