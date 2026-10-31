module

public import VerifiedGarbage.Proof.Ecdsa.X86_64.P192.MulVerified
public import VerifiedGarbage.Proof.Ecdsa.X86_64.P192.MulLit
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-! # P-192's point multiplication on x86-64 -/

@[expose] public section

namespace VG.Generic.P192.X86_64.MulP192

open VG.Impl.Ecdsa.X86_64 VG.Proof.Ecdsa.X86_64.P192.Mul

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInv Spec.P192.curve) : List Artifact :=
  [C.mulApi.artifact X86_64.target {
      code := p192.mulFn
      verified := mul_verified h.law h.inv }]

end VG.Generic.P192.X86_64.MulP192
