use ec_divisors_contest::{init_ref, init_contest};

use ciphersuite::{
    group::{ff::Field, Group},
    Ciphersuite, Ed25519,
};
use dalek_ff_group::EdwardsPoint;
use rand_core::OsRng;

use criterion::{criterion_group, criterion_main, Criterion};

// Benchmark the reference implementation and the implementation in
// ../ec-divisors-contest-src
fn bench_scalar_mul_divisors(c: &mut Criterion) {
    let mut group = c.benchmark_group("ec-divisors");

    let point = EdwardsPoint::generator();
    let rand_scalar = <Ed25519 as Ciphersuite>::F::random(&mut OsRng);

    // Get scalar decompositions
    let scalar_ref = init_ref(&point, &rand_scalar);
    let scalar_contest = init_contest(&point, &rand_scalar);

    // Run the benchmark for the reference implementation
    group.bench_function("reference-impl", |b| {
        b.iter(|| scalar_ref.scalar_mul_divisor(point))
    });

    // Run the benchmark for the contest implementation
    group.bench_function("contest-impl", |b| {
        b.iter(|| scalar_contest.scalar_mul_divisor(point))
    });

    group.finish();
}

criterion_group!(benches, bench_scalar_mul_divisors);
criterion_main!(benches);
