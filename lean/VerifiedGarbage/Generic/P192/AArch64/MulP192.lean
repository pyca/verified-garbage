module

public import VerifiedGarbage.Proof.Ecdsa.AArch64.P192.MulVerified
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# P-192's point multiplication on AArch64

`vg_p192_mul` (`Spec/Weierstrass/Mul.lean`), which the signature, the
public key derivation, verification and ECDH call. A generic file (see
`TCB/Emit.lean`) over P-192's group law and inversions `h`, the variant
`Variants/P192/AArch64/Law.lean`: the ladder's proof takes the group law,
and the curve's facts (`p192_ok`) its inversions.
-/

@[expose] public section

namespace VG.Generic.P192.AArch64.MulP192

open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.P192.Mul

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInv Spec.P192.curve) : List Artifact :=
  [C.mulApi.artifact AArch64.target {
      code := p192.mulFn
      verified := mul_verified h.law h.inv }]

end VG.Generic.P192.AArch64.MulP192
