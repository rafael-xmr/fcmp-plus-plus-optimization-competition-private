use criterion::Criterion;
use ec_divisors_contest::{bench_scalar_mul_divisors, test_scalar_mul_divisors};

fn main() {
    println!("Running tests on the ec-divisors implementation");
    test_scalar_mul_divisors();
    println!("Tests passed!");

    println!("Running benchmark");
    let mut criterion = Criterion::default();
    bench_scalar_mul_divisors(&mut criterion);
}