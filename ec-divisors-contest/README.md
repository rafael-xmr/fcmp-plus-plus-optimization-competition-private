## Overview

Welcome, contestant!

Please read ALL requirements *carefully* in [`../README.md`](../README.md) before reading this.
If you have any questions, do not hesitate to ask in IRC/Matrix #monero-dev,
or create an issue.

The goal of this competition is to optimize the provided `ec-divisors`
implementation.

The reference implementation source code is provided in
[`./ec-divisors-contest-src`](./ec-divisors-contest-src). You may modify all of
[`./ec-divisors-contest-src`](./ec-divisors-contest-src). The tests in
[`./ec-divisors-contest-src/src/tests`](./ec-divisors-contest-src/tests) are
provided for your convenience. You can alter those tests as you see fit. You do
*not* have to pass the tests in [`./ec-divisors-contest-src/src/tests`](./ec-divisors-contest-src/src/tests).

However, you *must* pass the test provided in [`./tests/divisors.rs`](./tests/divisors.rs).

You may *not* modify anything outside of [`./ec-divisors-contest-src`](./ec-divisors-contest-src)
(except for adding/extending trait implementations if you wish).

Again, please read ALL contest requirements carefully at [`../README.md`](../README.md).

## How to run the code

First, make sure you have rust 1.69.0 installed.

```
rustup install 1.69.0
```

To run the tests:

```
cargo +1.69.0 test --release
```

To run the benchmark:

```
cargo +1.69.0 bench
```

To run the wasm cycle counter:

```
git clone https://github.com/j-berman/wasm-cycles
cd wasm-cycles
cargo +1.69.0 run --release -- ../fcmp-plus-plus-optimization-competition/ec-divisors-contest
```

Remember, your code must improve BOTH the benchmark and wasm cycle count by at
least 20% in order to qualify as a valid submission. It also must follow ALL
requirements in [`../README.md`](../README.md).

Good luck!
