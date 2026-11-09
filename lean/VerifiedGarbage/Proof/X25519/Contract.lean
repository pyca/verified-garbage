module

public import VerifiedGarbage.Spec.X25519.Contract

/-!
# X25519: the contract of `vg_x25519`, an internal function

Not trusted: the contract that the proofs of `vg_x25519` (and its variants),
which only verified code calls (`vg_x25519_exchange`), are of, and that the
proofs of its callers compose. Only the callers' contracts, in
`Spec/X25519/Contract.lean`, are trusted. Its arguments are those of
`vg_x25519_exchange` (`Spec.X25519.exchangeSig`), without the return value.
-/

@[expose] public section

namespace VG.Proof.X25519

open VG.Spec.X25519

/-- `vg_x25519(out: *mut [u8; 32], scalar: *const [u8; 32], point: *const [u8; 32], scratch: *mut [u64; 512])`.
`scratch` is working space. -/
def x25519Sig : Sig where
  params := exchangeSig.params

/-- Writes `X25519(k, u)` to `out`, for the 32-byte scalar `k` at `scalar`
and the 32-byte u-coordinate `u` at `point`, which may be all zero (RFC 7748
§6.1). -/
def x25519Contract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  x25519Sig.contract A (post := fun out scalar point _scratch m m' _ =>
    bytesAt m' out 32 = x25519 (bytesAt m scalar 32) (bytesAt m point 32))
    (stack := stack)

end VG.Proof.X25519
