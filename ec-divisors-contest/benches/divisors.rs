use criterion::Criterion;
use ec_divisors_contest::bench_scalar_mul_divisors;

fn main() {
    let mut criterion = Criterion::default();
    bench_scalar_mul_divisors(&mut criterion);
}
