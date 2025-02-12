#![allow(non_snake_case)]

use helioselene_contest::{
    test_gen_random_helios_point, test_gen_random_helios_scalar, test_gen_random_selene_point,
    test_gen_random_selene_scalar,
};

use helioselene::{
    group::ff::Field as FieldRef, Field25519 as Field25519Ref, HeliosPoint as HeliosPointRef,
    HelioseleneField as HelioseleneFieldRef, SelenePoint as SelenePointRef,
};
use helioselene_contest_src::{
    group::Group, Field25519, HeliosPoint, HelioseleneField, SelenePoint,
};

use criterion::{criterion_group, criterion_main, Criterion};

macro_rules! repeat_op {
    ($op:expr, $n_iters:expr) => {{
        for _ in 0..$n_iters {
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
    let n_iters = 1000000;
    group.bench_function("field-add", |bn| bn.iter(|| repeat_op!(a + b, n_iters)));
    group.bench_function("field-add-ref", |bn| {
        bn.iter(|| repeat_op!(a_ref + b_ref, n_iters))
    });

    // Mul
    let n_iters = 300000;
    group.bench_function("field-mul", |bn| bn.iter(|| repeat_op!(a * b, n_iters)));
    group.bench_function("field-mul-ref", |bn| {
        bn.iter(|| repeat_op!(a_ref * b_ref, n_iters))
    });

    // Sub
    let n_iters = 1000000;
    group.bench_function("field-sub", |bn| bn.iter(|| repeat_op!(a - b, n_iters)));
    group.bench_function("field-sub-ref", |bn| {
        bn.iter(|| repeat_op!(a_ref - b_ref, n_iters))
    });

    // Square
    let n_iters = 300000;
    group.bench_function("field-sq", |bn| bn.iter(|| repeat_op!(a.square(), n_iters)));
    group.bench_function("field-sq-ref", |bn| {
        bn.iter(|| repeat_op!(a_ref.square(), n_iters))
    });

    // Double
    let n_iters = 1000000;
    group.bench_function("field-dbl", |bn| {
        bn.iter(|| repeat_op!(a.double(), n_iters))
    });
    group.bench_function("field-dbl-ref", |bn| {
        bn.iter(|| repeat_op!(a_ref.double(), n_iters))
    });

    // Invert
    let n_iters = 1000;
    group.bench_function("field-inv", |bn| {
        bn.iter(|| repeat_op!(a.invert().unwrap(), n_iters))
    });
    group.bench_function("field-inv-ref", |bn| {
        bn.iter(|| repeat_op!(a_ref.invert().unwrap(), n_iters))
    });

    // Sqrt
    let n_iters = 500;
    group.bench_function("field-sqrt", |bn| {
        bn.iter(|| repeat_op!(a.square().sqrt().unwrap(), n_iters))
    });
    group.bench_function("field-sqrt-ref", |bn| {
        bn.iter(|| repeat_op!(a_ref.square().sqrt().unwrap(), n_iters))
    });

    // Pow
    let n_iters = 500;
    group.bench_function("field-pow", |bn| bn.iter(|| repeat_op!(a.pow(b), n_iters)));
    group.bench_function("field-pow-ref", |bn| {
        bn.iter(|| repeat_op!(a_ref.pow(b_ref), n_iters))
    });

    group.finish();
}

fn bench_helios_point_ops(
    c: &mut Criterion,
    A: HeliosPoint,
    B: HeliosPoint,
    A_ref: HeliosPointRef,
    B_ref: HeliosPointRef,
    s: HelioseleneField,
    s_ref: HelioseleneFieldRef,
) {
    let mut group = c.benchmark_group("helios-point-ops");

    // Add
    let n_iters = 10000;
    group.bench_function("helios-add", |bn| bn.iter(|| repeat_op!(A + B, n_iters)));
    group.bench_function("helios-add-ref", |bn| {
        bn.iter(|| repeat_op!(A_ref + B_ref, n_iters))
    });

    // Mul
    let n_iters = 50;
    group.bench_function("helios-mul", |bn| bn.iter(|| repeat_op!(A * s, n_iters)));
    group.bench_function("helios-mul-ref", |bn| {
        bn.iter(|| repeat_op!(A_ref * s_ref, n_iters))
    });

    // Mul by generator
    let n_iters = 50;
    group.bench_function("helios-mul-gen", |bn| {
        bn.iter(|| repeat_op!(HeliosPoint::generator() * s, n_iters))
    });
    group.bench_function("helios-mul-gen-ref", |bn| {
        bn.iter(|| repeat_op!(HeliosPointRef::generator() * s_ref, n_iters))
    });

    // Sub
    let n_iters = 10000;
    group.bench_function("helios-sub", |bn| bn.iter(|| repeat_op!(A - B, n_iters)));
    group.bench_function("helios-sub-ref", |bn| {
        bn.iter(|| repeat_op!(A_ref - B_ref, n_iters))
    });

    // Double
    let n_iters = 10000;
    group.bench_function("helios-dbl", |bn| {
        bn.iter(|| repeat_op!(A.double(), n_iters))
    });
    group.bench_function("helios-dbl-ref", |bn| {
        bn.iter(|| repeat_op!(A_ref.double(), n_iters))
    });

    group.finish();
}

fn bench_selene_point_ops(
    c: &mut Criterion,
    A: SelenePoint,
    B: SelenePoint,
    A_ref: SelenePointRef,
    B_ref: SelenePointRef,
    s: Field25519,
    s_ref: Field25519Ref,
) {
    let mut group = c.benchmark_group("selene-point-ops");

    // Add
    let n_iters = 10000;
    group.bench_function("selene-add", |bn| bn.iter(|| repeat_op!(A + B, n_iters)));
    group.bench_function("selene-add-ref", |bn| {
        bn.iter(|| repeat_op!(A_ref + B_ref, n_iters))
    });

    // Mul
    let n_iters = 50;
    group.bench_function("selene-mul", |bn| bn.iter(|| repeat_op!(A * s, n_iters)));
    group.bench_function("selene-mul-ref", |bn| {
        bn.iter(|| repeat_op!(A_ref * s_ref, n_iters))
    });

    // Mul by generator
    let n_iters = 50;
    group.bench_function("selene-mul-gen", |bn| {
        bn.iter(|| repeat_op!(SelenePoint::generator() * s, n_iters))
    });
    group.bench_function("selene-mul-gen-ref", |bn| {
        bn.iter(|| repeat_op!(SelenePointRef::generator() * s_ref, n_iters))
    });

    // Sub
    let n_iters = 10000;
    group.bench_function("selene-sub", |bn| bn.iter(|| repeat_op!(A - B, n_iters)));
    group.bench_function("selene-sub-ref", |bn| {
        bn.iter(|| repeat_op!(A_ref - B_ref, n_iters))
    });

    // Double
    let n_iters = 10000;
    group.bench_function("selene-dbl", |bn| {
        bn.iter(|| repeat_op!(A.double(), n_iters))
    });
    group.bench_function("selene-dbl-ref", |bn| {
        bn.iter(|| repeat_op!(A_ref.double(), n_iters))
    });

    group.finish();
}

fn bench_helioselene(c: &mut Criterion) {
    // HelioseleneField
    let (a, a_ref) = test_gen_random_helios_scalar();
    let (b, b_ref) = test_gen_random_helios_scalar();
    bench_field_ops(c, a, b, a_ref, b_ref);

    // HeliosPoint
    let (A, A_ref) = test_gen_random_helios_point();
    let (B, B_ref) = test_gen_random_helios_point();
    let (s, s_ref) = test_gen_random_helios_scalar();
    bench_helios_point_ops(c, A, B, A_ref, B_ref, s, s_ref);

    // SelenePoint
    let (A, A_ref) = test_gen_random_selene_point();
    let (B, B_ref) = test_gen_random_selene_point();
    let (s, s_ref) = test_gen_random_selene_scalar();
    bench_selene_point_ops(c, A, B, A_ref, B_ref, s, s_ref);
}

criterion_group!(benches, bench_helioselene);
criterion_main!(benches);
