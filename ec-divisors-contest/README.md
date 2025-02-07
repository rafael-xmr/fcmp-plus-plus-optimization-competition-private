Welcome, contestant!

The goal of this competition is to get the benchmark in `./benches/divisors.rs`
to run as fast as possible, using your own implementation of
ec-divisors-contest.

The reference implementation source code is provided in `./src`. You may modify
all code in `./src`. The tests in `./src/tests` are provided for your
convenience. You can alter those tests as you see fit. You do not have to pass
the tests in `./src/tests`.

You *must* pass the test provided in `./tests/divisors.rs`. You may *not* modify
`/tests/divisors.rs`.

You also may not modify `./benches`. The benchmark must run as is.

Please read ALL contest rules carefully at `../README.md`.

To run the benchmark, use the command:

```
cargo +1.69.0 bench --features ed25519
```

To run the tests, use the command:

```
cargo +1.69.0 test --release --test divisors --features ed25519 -- divisors_contest_test --exact --nocapture
```

Remember, your code must improve the benchmark by at least 20% in order to
qualify as a valid submission.

Good luck!

TODO: instructions for building and running on the target.
