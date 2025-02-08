use helioselene::{
    group::ff::Field as FieldRef, HeliosPoint as HeliosPointRef,
    HelioseleneField as HelioseleneFieldRef, SelenePoint as SelenePointRef, Field25519 as Field25519Ref
};
use helioselene_contest_src::{
    group::{ff::PrimeField, Group, GroupEncoding},
    HeliosPoint, HelioseleneField, SelenePoint, Field25519,
};

use rand_core::OsRng;

use criterion::{criterion_group, criterion_main, Criterion};

fn test_gen_random_helios_scalar() -> (HelioseleneField, HelioseleneFieldRef) {
    let a_ref = HelioseleneFieldRef::random(&mut OsRng);
    let a = HelioseleneField::from_repr(a_ref.to_repr()).expect("Failed to read scalar");
    assert_eq!(a.to_repr(), a_ref.to_repr());
    (a, a_ref)
}

fn test_gen_random_selene_scalar() -> (Field25519, Field25519Ref) {
    let a_ref = Field25519Ref::random(&mut OsRng);
    let a = Field25519::from_repr(a_ref.to_repr()).expect("Failed to read scalar");
    assert_eq!(a.to_repr(), a_ref.to_repr());
    (a, a_ref)
}

#[allow(non_snake_case)]
fn test_gen_random_helios_point() -> (HeliosPoint, HeliosPointRef) {
    let A_ref = HeliosPointRef::random(&mut OsRng);
    let A = HeliosPoint::from_bytes(&A_ref.to_bytes()).expect("Failed to read helios point");
    assert_eq!(A.to_bytes(), A_ref.to_bytes());
    (A, A_ref)
}

#[allow(non_snake_case)]
fn test_gen_random_selene_point() -> (SelenePoint, SelenePointRef) {
    let A_ref = SelenePointRef::random(&mut OsRng);
    let A = SelenePoint::from_bytes(&A_ref.to_bytes()).expect("Failed to read selene point");
    assert_eq!(A.to_bytes(), A_ref.to_bytes());
    (A, A_ref)
}

fn test_field_ops(
    a: HelioseleneField,
    b: HelioseleneField,
    a_ref: HelioseleneFieldRef,
    b_ref: HelioseleneFieldRef,
) {
    // Add
    let res = a + b;
    let res_ref = a_ref + b_ref;
    assert_eq!(res.to_repr(), res_ref.to_repr());

    // Mul
    let res = a * b;
    let res_ref = a_ref * b_ref;
    assert_eq!(res.to_repr(), res_ref.to_repr());

    // Sub
    let res = a - b;
    let res_ref = a_ref - b_ref;
    assert_eq!(res.to_repr(), res_ref.to_repr());

    // Square
    let res = a.square();
    let res_ref = a_ref.square();
    assert_eq!(res.to_repr(), res_ref.to_repr());

    // Double
    let res = a.double();
    let res_ref = a_ref.double();
    assert_eq!(res.to_repr(), res_ref.to_repr());

    // Invert
    let res_ref = a_ref.invert().unwrap();
    let res = a.invert().expect("Failed to invert");
    assert_eq!(res.to_repr(), res_ref.to_repr());

    // Sqrt a square
    let res_ref = a_ref.square().sqrt().unwrap();
    let res = a.square().sqrt().expect("Failed to sqrt");
    assert_eq!(res.to_repr(), res_ref.to_repr());

    // Pow
    let res = a.pow(b);
    let res_ref = a_ref.pow(b_ref);
    assert_eq!(res.to_repr(), res_ref.to_repr());

    // Neg
    let res = -a;
    let res_ref = -a_ref;
    assert_eq!(res.to_repr(), res_ref.to_repr());

    // Odd
    let res = bool::from(a.is_odd());
    let res_ref = bool::from(a_ref.is_odd());
    assert_eq!(res, res_ref);

    // Even
    let res = bool::from(a.is_even());
    let res_ref = bool::from(a_ref.is_even());
    assert_eq!(res, res_ref);
}

#[allow(non_snake_case)]
fn do_helios_point_ops(
    A: HeliosPoint,
    B: HeliosPoint,
    A_ref: HeliosPointRef,
    B_ref: HeliosPointRef,
    s: HelioseleneField,
    s_ref: HelioseleneFieldRef,
) {
    // Add
    let res = A + B;
    let res_ref = A_ref + B_ref;
    assert_eq!(res.to_bytes(), res_ref.to_bytes());

    // Mul
    let res = A * s;
    let res_ref = A_ref * s_ref;
    assert_eq!(res.to_bytes(), res_ref.to_bytes());

    // Mul by generator
    let res = HeliosPoint::generator() * s;
    let res_ref = HeliosPointRef::generator() * s_ref;
    assert_eq!(res.to_bytes(), res_ref.to_bytes());

    // Sub
    let res = A - B;
    let res_ref = A_ref - B_ref;
    assert_eq!(res.to_bytes(), res_ref.to_bytes());

    // Double
    let res = A.double();
    let res_ref = A_ref.double();
    assert_eq!(res.to_bytes(), res_ref.to_bytes());

    // Neg
    let res = -A;
    let res_ref = -A_ref;
    assert_eq!(res.to_bytes(), res_ref.to_bytes());
}

#[allow(non_snake_case)]
fn do_selene_point_ops(
    A: SelenePoint,
    B: SelenePoint,
    A_ref: SelenePointRef,
    B_ref: SelenePointRef,
    s: Field25519,
    s_ref: Field25519Ref,
) {
    // Add
    let res = A + B;
    let res_ref = A_ref + B_ref;
    assert_eq!(res.to_bytes(), res_ref.to_bytes());

    // Mul
    let res = A * s;
    let res_ref = A_ref * s_ref;
    assert_eq!(res.to_bytes(), res_ref.to_bytes());

    // Mul by generator
    let res = SelenePoint::generator() * s;
    let res_ref = SelenePointRef::generator() * s_ref;
    assert_eq!(res.to_bytes(), res_ref.to_bytes());

    // Sub
    let res = A - B;
    let res_ref = A_ref - B_ref;
    assert_eq!(res.to_bytes(), res_ref.to_bytes());

    // Double
    let res = A.double();
    let res_ref = A_ref.double();
    assert_eq!(res.to_bytes(), res_ref.to_bytes());

    // Neg
    let res = -A;
    let res_ref = -A_ref;
    assert_eq!(res.to_bytes(), res_ref.to_bytes());
}

#[allow(non_snake_case)]
pub fn test_helioselene() {
    static N_ITERS: usize = 1000;

    // Test field implementation first
    ff_group_tests::prime_field::test_prime_field_bits::<_, HelioseleneField>(&mut OsRng);

    // Test that the implementation in ../helioselene-contest-src produces the
    // same results as the reference implementation
    for _ in 0..N_ITERS {
        let (a, a_ref) = test_gen_random_helios_scalar();
        let (b, b_ref) = test_gen_random_helios_scalar();
        test_field_ops(a, b, a_ref, b_ref);
    }

    // Now test point implementations

    // Helios
    ff_group_tests::group::test_prime_group_bits::<_, HeliosPoint>(&mut OsRng);
    for _ in 0..N_ITERS {
        let (A, A_ref) = test_gen_random_helios_point();
        let (B, B_ref) = test_gen_random_helios_point();
        let (s, s_ref) = test_gen_random_helios_scalar();
        do_helios_point_ops(A, B, A_ref, B_ref, s, s_ref);
    }
    // Selene
    ff_group_tests::group::test_prime_group_bits::<_, SelenePoint>(&mut OsRng);
    for _ in 0..N_ITERS {
        let (A, A_ref) = test_gen_random_selene_point();
        let (B, B_ref) = test_gen_random_selene_point();
        let (s, s_ref) = test_gen_random_selene_scalar();
        do_selene_point_ops(A, B, A_ref, B_ref, s, s_ref);
    }
}

macro_rules! repeat_op {
    ($op:expr, $count:expr) => {{
        for _ in 0..$count {
            let _ = $op;
        }
    }};
}

fn bench_field_ops(
    c: &mut Criterion,
    a: HelioseleneField,
    b: HelioseleneField,
    a_ref: HelioseleneFieldRef,
    b_ref: HelioseleneFieldRef,
) {
    let mut group = c.benchmark_group("helioselene-field-ops");

    // Add
    let n_iters = 10000;
    group.bench_function("field-add", |bn| {
        bn.iter(|| repeat_op!(a + b, n_iters))
    });
    group.bench_function("field-add-ref", |bn| {
        bn.iter(|| repeat_op!(a_ref + b_ref, n_iters))
    });

    // Mul
    let n_iters = 1000;
    group.bench_function("field-mul", |bn| {
        bn.iter(|| repeat_op!(a * b, n_iters))
    });
    group.bench_function("field-mul-ref", |bn| {
        bn.iter(|| repeat_op!(a_ref * b_ref, n_iters))
    });

    // Sub
    let n_iters = 10000;
    group.bench_function("field-sub", |bn| {
        bn.iter(|| repeat_op!(a - b, n_iters))
    });
    group.bench_function("field-sub-ref", |bn| {
        bn.iter(|| repeat_op!(a_ref - b_ref, n_iters))
    });

    // Square
    let n_iters = 10000;
    group.bench_function("field-sq", |bn| {
        bn.iter(|| repeat_op!(a.square(), n_iters))
    });
    group.bench_function("field-sq-ref", |bn| {
        bn.iter(|| repeat_op!(a_ref.square(), n_iters))
    });

    // Double
    let n_iters = 10000;
    group.bench_function("field-dbl", |bn| {
        bn.iter(|| repeat_op!(a.double(), n_iters))
    });
    group.bench_function("field-dbl-ref", |bn| {
        bn.iter(|| repeat_op!(a_ref.double(), n_iters))
    });

    // Invert
    let n_iters = 100;
    group.bench_function("field-inv", |bn| {
        bn.iter(|| repeat_op!(a.invert().unwrap(), n_iters))
    });
    group.bench_function("field-inv-ref", |bn| {
        bn.iter(|| repeat_op!(a_ref.invert().unwrap(), n_iters))
    });

    // Sqrt
    let n_iters = 100;
    group.bench_function("field-sqrt", |bn| {
        bn.iter(|| repeat_op!(a.square().sqrt().unwrap(), n_iters))
    });
    group.bench_function("field-sqrt-ref", |bn| {
        bn.iter(|| repeat_op!(a_ref.square().sqrt().unwrap(), n_iters))
    });

    // Pow
    let n_iters = 100;
    group.bench_function("field-pow", |bn| {
        bn.iter(|| repeat_op!(a.pow(b), n_iters))
    });
    group.bench_function("field-pow-ref", |bn| {
        bn.iter(|| repeat_op!(a_ref.pow(b_ref), n_iters))
    });

    group.finish();
}

fn run_bench_helioselene(c: &mut Criterion) {
    let (a, a_ref) = test_gen_random_helios_scalar();
    let (b, b_ref) = test_gen_random_helios_scalar();
    bench_field_ops(c, a, b, a_ref, b_ref);
}

pub fn bench_helioselene() {
    let mut c = Criterion::default();
    run_bench_helioselene(&mut c);
}

criterion_group!(benches, run_bench_helioselene);
criterion_main!(benches);
