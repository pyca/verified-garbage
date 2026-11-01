module

public import VerifiedGarbage.Spec.Sm3.Contract

/-!
# SM3: the contracts of its internal functions

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.
-/

@[expose] public section

namespace VG.Proof.Sm3

open VG.Spec.Sm3

/-- `vg_sm3_compress(state: *mut [u32; 8], blocks: *const [u8; 64], n: usize, scratch: *mut [u64; 72])`.
`scratch` is working space: room for a block's whole message expansion
(`W_0 … W_67` and `W'_0 … W'_63`, 528 bytes) and six saved callee-saved
registers. The streaming functions pass theirs to it. -/
def compressSig : Sig where
  params := [("state", .array true .u32 8), ("blocks", .slice false (.array .u8 64) "n"),
    ("scratch", .array true .u64 72)]

/-- Updates the hash value at `state` with the `n` 64-byte blocks at
`blocks`. The hash value and the blocks are secret. -/
def compressContract {M : ISA} (A : Abi M) : Contract M :=
  compressSig.contract A (post := fun state blocks n _scratch m m' _ =>
    stateAt m' state = compressBlocks (stateAt m state) m blocks n.toNat)

end VG.Proof.Sm3
