# Halo2-PSE fork with cq-lookup argument

## Description

This repository contains the [halo2](https://github.com/zcash/halo2) PSE fork (using KZG as polynomial commitment), 
with the addition of cq-lookup argument [L. Eagen, D. Fiore, and 
A. Gabizon. "cq: Cached Quotients for Fast Lookups"](https://eprint.iacr.org/2022/1763.pdf). Compared with the halo2 (plookup) lookup already available
in the system, cq is suitable for the case that the lookup table
size is huge and cannot be decomposed like [Lasso](https://eprint.iacr.org/2023/1216).

The API interface resembles the halo2 (plookup), e.g., supporting
input expressions to aggregate input columns.
For technical details, an example file is available at [cq_lookup.rs](halo_proofs/examples/cq_lookup.rs). 

To integrate the cq protocol with halo2, we adopt 
the commit-and-prove approach mainly for saving engineering efforts.
The cq-lookup proof is done separately with a zk-version of the cq protocol,
and then it is "connected" using column commitments in halo2-pse proof.

The formal definition (derivation of cq) and its proof
is presented in [zk_cq.pdf](doc/zk_cq.pdf). It is possible to encode the
LHS of the Hab22 equation in the halo2 constraint system to further cut
down prover cost, which we leave to future work.

The implementation forks from 
the Halo2-PSE commit: 68b6006ac69a5eff21f8ae8a2fee9a55a8ee7ec4.
The logs of change can be found 
in [CHANGELOG_HALO2.txt](doc/CHANGELOG_HALO2.txt)

## To Run
cargo run --example cq_lookup

## Minimum Supported Rust Version
Requires Rust **1.73.0** 

## License

Licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or
   http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

## Acknowledgments
More details to come.
