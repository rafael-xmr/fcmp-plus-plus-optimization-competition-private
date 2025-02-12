## Overview

Welcome, contestant!

Please read ALL requirements *carefully* in [`../README.md`](../README.md) before reading this.
If you have any questions, do not hesitate to ask in IRC/Matrix #monero-dev,
or create an issue.

The goal of this competition is to get the benchmark in [`./benches/divisors.rs`](./benches/divisors.rs)
to run as fast as possible, using your own implementation of
ec-divisors-contest, fulfilling ALL requirements from [`../README.md`](../README.md).

The reference implementation source code is provided in
[`./ec-divisors-contest-src`](./ec-divisors-contest-src). You may modify all of
[`./ec-divisors-contest-src`](./ec-divisors-contest-src). The tests in
[`./ec-divisors-contest-src/tests`](./ec-divisors-contest-src/tests) are
provided for your convenience. You can alter those tests as you see fit. You do
*not* have to pass the tests in [`./ec-divisors-contest-src/tests`](./ec-divisors-contest-src/tests).

However, you *must* pass the test provided in [`./tests/divisors.rs`](./tests/divisors.rs).

You may *not* modify anything outside of [`./ec-divisors-contest-src`](./ec-divisors-contest-src).

You also may not modify [`./benches`](./benches). The benchmark must run as is (TODO: wasm target).

Again, please read ALL contest requirements carefully at [`../README.md`](../README.md).

## How to run the code

To run the benchmark, use the command:

```
cargo +1.69.0 bench
```

To run the tests, use the command:

```
cargo +1.69.0 test --release
```

Remember, your code must improve the benchmark by at least 20% in order to
qualify as a valid submission. It also must follow all requirements in
[`../README.md`](../README.md).

Good luck!

TODO: instructions for building and running on the target.
