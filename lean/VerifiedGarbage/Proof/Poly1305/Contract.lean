module

public import VerifiedGarbage.Spec.Poly1305.Contract

/-!
# Poly1305: the contracts of its internal functions

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.

`vg_poly1305_blocks` absorbs whole blocks into the state of a message of
whole blocks (`Repr`), for callers that pad their message themselves (e.g.
ChaCha20-Poly1305).
-/

@[expose] public section

namespace VG.Proof.Poly1305

open VG.Spec.Poly1305

/-- `vg_poly1305_blocks(state: *mut [u64; 16], blocks: *const [u8; 16], n: usize)`. -/
def blocksSig : Sig where
  params := [("state", .array true .u64 16), ("blocks", .slice false (.array .u8 16) "n")]

/-- If the state at `state` represents a message `msg` under a key, then
afterwards it represents `msg` followed by the `n` 16-byte blocks at
`blocks`, under the same key. -/
def blocksContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  blocksSig.contract A (post := fun state blocks n m m' _ =>
    ∀ key msg, Repr m state key msg → Repr m' state key (msg ++ bytesAt m blocks (16 * n.toNat)))
    (stack := stack)

/-- `vg_poly1305_finalize_scratch(state: *mut [u64; 16], count: u64, out: *mut [u8; 16], scratch: *mut [u64; 16])`:
`vg_poly1305_finalize` with its working space passed in `scratch`, for
functions that call it with theirs (ChaCha20-Poly1305's). -/
def finalizeScratchSig : Sig where
  params := [("state", .array true .u64 16), ("count", .int .u64 true),
    ("out", .array true .u8 16), ("scratch", .array true .u64 16)]

/-- `finalizePost`, whatever `scratch` is. -/
def finalizeScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  finalizeScratchSig.contract A
    (post := fun state count out _scratch => finalizePost A.ptrBits state count out)
    (stack := stack)

end VG.Proof.Poly1305
