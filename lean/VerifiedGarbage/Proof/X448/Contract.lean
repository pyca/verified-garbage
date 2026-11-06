module

public import VerifiedGarbage.Spec.X448.Contract

/-!
# X448: the contract of `vg_x448`, an internal function

Not trusted: the contract that the proofs of `vg_x448` (and its variants),
which only verified code calls (`vg_x448_exchange`), are of, and that the
proofs of its callers compose. Only the callers' contracts, in
`Spec/X448/Contract.lean`, are trusted. Its arguments are those of
`vg_x448_exchange` (`Spec.X448.exchangeSig`), without the return value.
-/

@[expose] public section

namespace VG.Proof.X448

open VG.Spec.X448

/-- `vg_x448(out: *mut [u8; 56], scalar: *const [u8; 56], point: *const [u8; 56], scratch: *mut [u64; 1024])`.
`scratch` is working space. -/
def x448Sig : Sig where
  params := exchangeSig.params

/-- Writes `X448(k, u)` to `out`, for the 56-byte scalar `k` at `scalar`
and the 56-byte u-coordinate `u` at `point`, which may be all zero (RFC 7748
§6.2). -/
def x448Contract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  x448Sig.contract A (post := fun out scalar point _scratch m m' _ =>
    bytesAt m' out 56 = x448 (bytesAt m scalar 56) (bytesAt m point 56))
    (stack := stack)

end VG.Proof.X448
