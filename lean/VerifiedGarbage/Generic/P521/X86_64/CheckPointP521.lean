module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvInterface
public import VerifiedGarbage.Proof.Ecdh.X86_64.P521.CheckVerified
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-! # P-521's check of a public point on x86-64 -/

@[expose] public section

namespace VG.Generic.P521.X86_64.CheckPointP521

open VG.Impl.Ecdsa.X86_64 VG.Proof.Ecdh.X86_64.P521.Check

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInvOrd Spec.P521.curve) : List Artifact :=
  [false, true].map fun adx =>
    C.checkApi.artifact X86_64.target {
      suffix := (if adx then "_adx" else "")
      code := code adx
      verified := verified h.inv adx
      features := if adx then ["bmi2", "adx"] else [] }

end VG.Generic.P521.X86_64.CheckPointP521
