use ec_divisors_contest::{init_ref, init_contest};

use ciphersuite::{
    group::{ff::Field, Group},
    Ciphersuite, Ed25519,
};
use dalek_ff_group::EdwardsPoint;
use rand_core::OsRng;

// Test that the implementation in ../ec-divisors-contest-src produces the same
// result as the reference implementation
#[test]
fn divisors_contest_test() {
    static N_ITERS: usize = 20;

    for i in 0..N_ITERS {
        println!("Testing with random scalar {} / {}", i + 1, N_ITERS);

        let point = EdwardsPoint::generator();
        let rand_scalar = <Ed25519 as Ciphersuite>::F::random(&mut OsRng);

        // Get scalar decompositions
        let scalar_ref = init_ref(&point, &rand_scalar);
        let scalar_contest = init_contest(&point, &rand_scalar);

        // Get divisors
        let ref_res = scalar_ref.scalar_mul_divisor(point);
        let res = scalar_contest.scalar_mul_divisor(point);

        assert_eq!(ref_res.y_coefficients, res.y_coefficients);
        assert_eq!(ref_res.yx_coefficients, res.yx_coefficients);
        assert_eq!(ref_res.x_coefficients, res.x_coefficients);
        assert_eq!(ref_res.zero_coefficient, res.zero_coefficient);
    }
}
