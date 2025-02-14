## Overview

Welcome, contestant!

Please read ALL requirements *carefully* in [`../README.md`](../README.md) before reading this.
If you have any questions, do not hesitate to ask in IRC/Matrix #monero-dev,
or create an issue.

The goal of this competition is to optimize the provided `helioselene`
implementation.

The reference implementation source code is provided in
[`./helioselene-contest-src`](./helioselene-contest-src). You may modify all of
[`./helioselene-contest-src`](./helioselene-contest-src). The tests in
[`./helioselene-contest-src/src`](./helioselene-contest-src/src) are
provided for your convenience. You can alter those tests as you see fit. You do
*not* have to pass the tests in
[`./helioselene-contest-src/src`](./helioselene-contest-src/src).

However, you *must* pass the tests provided in
[`./tests/helioselene.rs`](./tests/helioselene.rs).

You may *not* modify anything outside of [`./helioselene-contest-src`](./helioselene-contest-src)
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
cargo +1.69.0 run --release -- ../fcmp-plus-plus-optimization-competition/helioselene-contest
```

TODO: determine how to weigh the different curve ops to arrive at "20% improvement."

Remember, your code must improve BOTH the benchmark and wasm cycle count by at
least 20% in order to qualify as a valid submission. It also must follow ALL
requirements in [`../README.md`](../README.md).

Good luck!
