use helioselene::{
    group::ff::Field as FieldRef, HeliosPoint as HeliosPointRef,
    HelioseleneField as HelioseleneFieldRef, SelenePoint as SelenePointRef, Field25519 as Field25519Ref
};
use helioselene_contest_src::{
    group::{ff::PrimeField, Group, GroupEncoding},
    HeliosPoint, HelioseleneField, SelenePoint, Field25519,
};

use rand_core::OsRng;

fn test_gen_random_helios_scalar() -> (HelioseleneField, HelioseleneFieldRef) {
    let a = HelioseleneField::random(&mut OsRng);
    let a_ref = HelioseleneFieldRef::from_repr(a.to_repr()).expect("Failed to read scalar");
    assert_eq!(a.to_repr(), a_ref.to_repr());
    (a, a_ref)
}

fn test_gen_random_helios_scalar_ref() -> (HelioseleneField, HelioseleneFieldRef) {
    let a_ref = HelioseleneFieldRef::random(&mut OsRng);
    let a = HelioseleneField::from_repr(a_ref.to_repr()).expect("Failed to read scalar");
    assert_eq!(a.to_repr(), a_ref.to_repr());
    (a, a_ref)
}

fn test_gen_random_selene_scalar() -> (Field25519, Field25519Ref) {
    let a = Field25519::random(&mut OsRng);
    let a_ref = Field25519Ref::from_repr(a.to_repr()).expect("Failed to read scalar");
    assert_eq!(a.to_repr(), a_ref.to_repr());
    (a, a_ref)
}

fn test_gen_random_selene_scalar_ref() -> (Field25519, Field25519Ref) {
    let a_ref = Field25519Ref::random(&mut OsRng);
    let a = Field25519::from_repr(a_ref.to_repr()).expect("Failed to read scalar");
    assert_eq!(a.to_repr(), a_ref.to_repr());
    (a, a_ref)
}

#[allow(non_snake_case)]
fn test_gen_random_helios_point() -> (HeliosPoint, HeliosPointRef) {
    let A = HeliosPoint::random(&mut OsRng);
    let A_ref = HeliosPointRef::from_bytes(&A.to_bytes()).expect("Failed to read helios point");
    assert_eq!(A.to_bytes(), A_ref.to_bytes());
    (A, A_ref)
}

#[allow(non_snake_case)]
fn test_gen_random_helios_point_ref() -> (HeliosPoint, HeliosPointRef) {
    let A_ref = HeliosPointRef::random(&mut OsRng);
    let A = HeliosPoint::from_bytes(&A_ref.to_bytes()).expect("Failed to read helios point");
    assert_eq!(A.to_bytes(), A_ref.to_bytes());
    (A, A_ref)
}

#[allow(non_snake_case)]
fn test_gen_random_selene_point() -> (SelenePoint, SelenePointRef) {
    let A = SelenePoint::random(&mut OsRng);
    let A_ref = SelenePointRef::from_bytes(&A.to_bytes()).expect("Failed to read selene point");
    assert_eq!(A.to_bytes(), A_ref.to_bytes());
    (A, A_ref)
}

#[allow(non_snake_case)]
fn test_gen_random_selene_point_ref() -> (SelenePoint, SelenePointRef) {
    let A_ref = SelenePointRef::random(&mut OsRng);
    let A = SelenePoint::from_bytes(&A_ref.to_bytes()).expect("Failed to read selene point");
    assert_eq!(A.to_bytes(), A_ref.to_bytes());
    (A, A_ref)
}

fn do_field_ops(
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

fn test_field_ops() {
    // 1. Generate randoms with the contest impl
    let (a, a_ref) = test_gen_random_helios_scalar();
    let (b, b_ref) = test_gen_random_helios_scalar();
    do_field_ops(a, b, a_ref, b_ref);

    // 2. Now test generating randoms with the reference impl
    let (a, a_ref) = test_gen_random_helios_scalar_ref();
    let (b, b_ref) = test_gen_random_helios_scalar_ref();
    do_field_ops(a, b, a_ref, b_ref);
}

#[allow(non_snake_case)]
fn test_helios_point_ops() {
    // 1. Generate randoms with the contest impl
    let (A, A_ref) = test_gen_random_helios_point();
    let (B, B_ref) = test_gen_random_helios_point();
    let (s, s_ref) = test_gen_random_helios_scalar();
    do_helios_point_ops(A, B, A_ref, B_ref, s, s_ref);

    // 2. Now test generating randoms with the reference impl
    let (A, A_ref) = test_gen_random_helios_point_ref();
    let (B, B_ref) = test_gen_random_helios_point_ref();
    let (s, s_ref) = test_gen_random_helios_scalar_ref();
    do_helios_point_ops(A, B, A_ref, B_ref, s, s_ref);
}

#[allow(non_snake_case)]
fn test_selene_point_ops() {
    // 1. Generate randoms with the contest impl
    let (A, A_ref) = test_gen_random_selene_point();
    let (B, B_ref) = test_gen_random_selene_point();
    let (s, s_ref) = test_gen_random_selene_scalar();
    do_selene_point_ops(A, B, A_ref, B_ref, s, s_ref);

    // 2. Now test generating randoms with the reference impl
    let (A, A_ref) = test_gen_random_selene_point_ref();
    let (B, B_ref) = test_gen_random_selene_point_ref();
    let (s, s_ref) = test_gen_random_selene_scalar_ref();
    do_selene_point_ops(A, B, A_ref, B_ref, s, s_ref);
}

pub fn test_helioselene() {
    static N_ITERS: usize = 100;

    // Test field implementation first
    ff_group_tests::prime_field::test_prime_field_bits::<_, HelioseleneField>(&mut OsRng);

    // Test that the implementation in ../helioselene-contest-src produces the
    // same results as the reference implementation
    for _ in 0..N_ITERS {
        test_field_ops();
    }

    // Now test point implementations

    // Helios
    ff_group_tests::group::test_prime_group_bits::<_, HeliosPoint>(&mut OsRng);
    for _ in 0..N_ITERS {
        test_helios_point_ops();
    }
    // Selene
    ff_group_tests::group::test_prime_group_bits::<_, SelenePoint>(&mut OsRng);
    for _ in 0..N_ITERS {
        test_selene_point_ops();
    }
}

pub fn bench_helioselene() {
    // let mut c = Criterion::default();
}

// criterion_group!(benches, run_bench_helioselene);
// criterion_main!(benches);
