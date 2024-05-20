# Halo2-PSE fork with cq-lookup argument

## Description

This repository contains the [halo2](https://github.com/zcash/halo2) fork, 
with the addition of cq-lookup argument (L. Eagen, D. Fiore, and 
A. Gabizon. "cq: Cached Quotients for Fast Lookups". https://eprint.iacr.org/2022/1763.pdf). Compared with the halo2 (plookup) lookup already available
in the system, cq is suitable for the case that the lookup table
size is huge and cannot be decomposed like Lasso (https://eprint.iacr.org/2023/1216).

The API interface retains the halo2 lookup features (input expressions etc.).
For technical details, an example file is available at [cq_lookup.rs] (./halo_proof/examples/cq_lookup.rs). 

To integrate the cq protocol, we use the commit-and-prove approach.
The lookup is done separately with a zk-version of the cq protocol.
The formal presentation and proof of the protocol is presented
in [zk_cq.pdf] (./doc/zk_cq.pdf). It is possible to encode the
left of the Hab22 equation in the halo2 constraints to further cut
down prover cost, which we leave to future work.

The implementation forms
off the PSE commit: 68b6006ac69a5eff21f8ae8a2fee9a55a8ee7ec4.
The logs of change can be found 
in [CHANGELOG_HALO2.txt] (./doc/CHANGELOG_HALO2.txt)

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
