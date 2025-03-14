## Overview

Welcome, contestant!

Please read ALL requirements *carefully* in [`../README.md`](../README.md) before reading this.
Please read this entire README carefully as well.
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

Caution: we use different versions of Rust in different circumstances. Please
be mindful of this.

First, make sure you have rust 1.69.0 and rust 1.84.1 installed.

```
rustup install 1.69.0
rustup install 1.84.1
```

Second, make sure you have the `wasm32v1-none` target installed.

```
rustup target add wasm32v1-none
```

To run the tests:

```
cargo +1.69.0 test --release
cargo +1.84.1 test --release
```

To run the benchmark, only use 1.84.1:

```
cargo +1.84.1 bench
```

If you have build conflict issues (as a result of switching compiler versions),
you may need to remove `target/` and Cargo.lock, then run again.

To run the wasm cycle counter:

```
git clone https://github.com/kayabaNerve/wasm-cycles
cd wasm-cycles
cargo +1.84.1 run --release -- ../fcmp-plus-plus-optimization-competition/helioselene-contest +1.84.1
```

Remember, your code must improve BOTH the benchmark and wasm cycle count by at
least 20% in order to qualify as a valid submission. It also must follow ALL
requirements in [`../README.md`](../README.md).

Good luck!

## How your helioselene score is calculated

The following operations are weighed as followed:

| Operation  | % Weight |
| ------------- | ------------- |
| Selene Point Add  | 30%  |
| Helios Point Add  | 15%  |
| helioselene Mul  | 15%  |
| helioselene Invert  | 10%  |
| Selene Point Decompression  | 7.5%  |
| Helios Point Decompression  | 7.5%  |
| helioselene Add  | 5%  |
| helioselene Sub  | 5%  |
| Selene Point Mul  | 2.5%  |
| Helios Point Mul  | 2.5%  |

- For example, if you improve Selene Point Add by 67% and improve nothing else,
your submission would qualify as a valid submission.
    - 67% * 30% = 20.1% overall improvement.
    - 20.1% > 20% minimum required improvement.

- If you improve Selene Point Add by 50%, Helios Point Add by 50%, and improve
nothing else, your submission would qualify as a valid submission.
    - 50% * 30% = 15% overall improvement from improving Selene Point Add.
    - 30% * 15% = 7.5% overall improvement from improving Helios Point Add.
    - 22.5% > 20% minimum required improvement.

- Some operations are used in others. For example, Selene Point Add is composed
of helioselene Mul, helioselene Add, and helioselene Sub. Thus, if you improve
helioselene Mul, then you would also improve Selene Point Add, and thus your
overall improvement score would benefit double jeopardy style.

The weights were determined based on their respective weights in functions
intended for use in Monero. You can see flamegraphs for the relevant functions
[verify](https://raw.githubusercontent.com/j-berman/fcmp-plus-plus/760b7784c3b77a7f43329317448fe5bcbc00dfd3/crypto/fcmps/flamegraph_verify.svg),
[hash_grow](https://raw.githubusercontent.com/j-berman/fcmp-plus-plus/760b7784c3b77a7f43329317448fe5bcbc00dfd3/crypto/fcmps/flamegraph_hash_grow.svg),
and [prove](https://raw.githubusercontent.com/j-berman/fcmp-plus-plus/760b7784c3b77a7f43329317448fe5bcbc00dfd3/crypto/fcmps/flamegraph_prove.svg).

- Hint: when looking at the images, if you cannot click into various sections of
the flamegraph, try downloading the files and re-opening the local file in a
browser. You can also use the "Search" functionality to highlight.
- The flamegraphs were constructed using [flamegraph](https://github.com/flamegraph-rs/flamegraph),
with the commands detailed [here](https://github.com/j-berman/fcmp-plus-plus/blob/760b7784c3b77a7f43329317448fe5bcbc00dfd3/crypto/fcmps/README.md#flamegraphs).
