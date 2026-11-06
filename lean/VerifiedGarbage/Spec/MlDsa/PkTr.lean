module

public import VerifiedGarbage.Spec.MlDsa.Contract

/-!
# ML-DSA: the public-key hash `tr`, on every target

**Trusted** (as every file in `Spec/`). `vg_mldsa*_verify_message_cached`
(`CachedVerify.lean`) requires its 64 bytes `tr` to be `pkTr pk`,
`H(pk, 64)` (FIPS 204 Algorithm 8, line 6), which depends on the public key
alone, so a public key used more than once keeps it. A key from
`vg_mldsa*_keygen` takes it from the private key (`KeyGenTr.lean`); a key
from bytes computes it with `vg_mldsa*_pk_tr`, whose contract is that it
writes `pkTr pk`, so that the precondition of the cached verification is
established by verified code, not by the caller.
-/

@[expose] public section

namespace VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- `vg_mldsa*_pk_tr(pk: *const [u8; pkLen], tr: *mut [u8; 64])`. -/
def pkTrSig (p : Params) : Sig where
  params := [("pk", .array false .u8 p.pkLen), ("tr", .array true .u8 64)]

/-- With the public key at `pk`: writes `tr = H(pk, 64)` (`pkTr`, Algorithm 8,
line 6) of the parameter set `p` to `tr`. Constant time: only the pointers
may affect timing, not the key or the digest. -/
def pkTrContract (p : Params) {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (pkTrSig p).contract A
    (post := fun pk tr m m' _ => bytesAt m' tr 64 = pkTr (bytesAt m pk p.pkLen))
    (writeArgs := true)
    (stack := stack)

/-- `vg_<module>_pk_tr` for the parameter set `p` named `name`. -/
def pkTrApi (p : Params) (module name : String) : Api where
  module := module
  name := s!"vg_{module}_pk_tr"
  sig := pkTrSig p
  writeArgs := true
  contracts := some fun A stack => pkTrContract p A stack
  summary := s!"{name} public-key hash: writes `tr = H(pk, 64)` (FIPS 204 Algorithm 8, \
    line 6), SHAKE256 of the public key `*pk` to 64 bytes, to `*tr`, the digest \
    `vg_{module}_verify_message_cached` takes.\n\n\
    Contract: `VG.Spec.MlDsa.pkTrContract`. Constant time: only the pointers may affect \
    timing, not the key or the digest."
  safety := []

/-- `vg_mldsa44_pk_tr` on every target. -/
def pkTr44Api : Api := pkTrApi mlDsa44 "mldsa44" "ML-DSA-44"
/-- `vg_mldsa65_pk_tr` on every target. -/
def pkTr65Api : Api := pkTrApi mlDsa65 "mldsa65" "ML-DSA-65"
/-- `vg_mldsa87_pk_tr` on every target. -/
def pkTr87Api : Api := pkTrApi mlDsa87 "mldsa87" "ML-DSA-87"

end VG.Spec.MlDsa
