# FCMP++ Optimization Competition

## This is a draft for a competition which will hopefully be ran. It is not
## final, not active, and not valid to submit for. No offerings of any kind are
## made to any reader.

The goal of this contest is to provide optimized implementations of
[`dalek-ff-group`'s `FieldElement`](https://github.com/kayabaNerve/fcmp-plus-plus/tree/develop/crypto/dalek-ff-group/src/field.rs),
[`helioselene`](https://github.com/kayabaNerve/fcmp-plus-plus/tree/develop/crypto/helioselene),
and
[`ec-divisors`](https://github.com/kayabaNerve/fcmp-plus-plus/tree/develop/crypto/divisors).

### Requirements

1) Submissions must be licensed under an approved license.

Please see the [list of approved licenses](./licenses). PRs are welcome and
will be reviewed on a case-by-case basis. Additional approvals are unlikely
however.

2) Submissions must compile with Rust stable 1.69.

Usage of nightly features is not allowed.

3) Submissions must support targets with alloc yet not std.

`wasm32-unknown-unknown` is the provided example of such a target. If the
submission builds and runs on it, it meets this criteria.

This requirement does prevent the usage of threads which are expected to be
used at a higher level by calling code.

4) Submissions must not have platform-specific code.

While various intrinsics would produce the best performance on their respective
targets, the point of this competition is to create baseline libraries usable
regardless of context.

5) Submissions must not include any unsafe code.

6) Dependencies must be pre-approved.

Please see the [list of approved dependencies](./dependencies). PRs are welcome
and will be reviewed on a case-by-case basis.

7) Submissions must not rely on tables built at compile-time.

8) Implementations must run in constant time.

Implementations will be reviewed for a variety of
[non-constant-time operations](https://bearssl.org/constanttime.html). All
branches and memory access must be constant with regards to the secrets
operated over. We do assume shifts and multiplications execute in constant
time.

Additionally, code will be run through
[`wasm-cycles`](https://github.com/kayabaNerve/wasm-cycles) to verify a
constant cycle count when compiled for `wasm32-unknown-unknown`. This is
incomprehensive to certain issues such as cache side-channel attacks, yet
represents an automated way to eliminate some types of non-constant-time code.

9) Submissions must not allocate more than 64 MB of RAM.

This will be evaluated by the amount of pages allocated when run with
`wasm-cycles`.

10) Submissions may build a cache and store it in a static.

The time to build the cache will be counted as part of the time for the
benchmark to execute however.

11) Submissions must pass the provided test suite and run with the provided
    benchmark.

Modifications to the test suite and benchmark are not allowed, except for
adding/extended trait implementations for elliptic curves tested with the
`ec-divisors` lib.

### Judging

Submissions have a joint score based on:

- Their benchmarks while running on a x64 sever
- Their cycle count from `wasm-cycles`

with a penalty applied based on the amount of WASM pages allocated. After
128 MB of pages, each additional 32 MB of RAM applies a 8% penalty.

### Target Areas

`dalek-ff-group` and `helioselene` uses
[`crypto-bigint`](https://github.com/RustCrypto/crypto-bigint) for its
arithmetic. Replacing their field arithmetics with tailored implementations
will likely provide significant savings. The prime used for the field
introduced by the Helios/Selene cycle is a Crandall prime with fast reduction
algorithms available accordingly.

`ec-divisors` performs polynomial multiplications/divisions which are quite
expensive without an FFT. While we can't assume it'll be used with curves which
are FFT friendly, it would be valid to define a trait to specify a FFT-friendly
multiplicative group to use with a curve (so long as such groups are feasible
to find for arbitrary curves). This would enable implementing
[ECFFT](https://arxiv.org/abs/2107.08473), reducing the computational
complexity of `ec-divisors`.
