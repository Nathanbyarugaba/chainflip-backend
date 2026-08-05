// Verus-verified ports of critical Chainflip state-chain arithmetic.
//
// Each module ports a function (or small cluster of functions) from the
// state-chain source tree and proves functional-correctness contracts and
// panic-freedom with the Verus SMT-based verifier. Module header comments map
// every ported item to its source location; ../conformance/ contains
// differential/property tests binding the ports back to the shipped code.
//
// Verify with:  ./verify.sh   (requires ../tools/get-tools.sh)

pub mod dca;
// pub mod mul_div;
pub mod network_fee;
