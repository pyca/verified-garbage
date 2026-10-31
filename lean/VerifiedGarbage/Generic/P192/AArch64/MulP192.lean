module

public import VerifiedGarbage.Proof.Ecdsa.AArch64.P192.MulVerified
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-! # P-192's point multiplication on AArch64 -/

@[expose] public section

namespace VG.Generic.P192.AArch64.MulP192

open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.P192.Mul

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInv Spec.P192.curve) : List Artifact :=
  [C.mulApi.artifact AArch64.target {
      code := p192.mulFn
      verified := mul_verified h.law h.inv }]

end VG.Generic.P192.AArch64.MulP192
