module

public import VerifiedGarbage.Spec.Poly1305.Contract

/-!
# Poly1305: the contracts of its internal functions

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.
-/

@[expose] public section

namespace VG.Proof.Poly1305

open VG.Spec.Poly1305

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
