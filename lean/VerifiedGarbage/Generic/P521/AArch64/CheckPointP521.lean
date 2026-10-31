module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
public import VerifiedGarbage.Proof.Ecdh.AArch64.P521.CheckVerified
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-! # P-521's check of a public point on AArch64 -/

@[expose] public section

namespace VG.Generic.P521.AArch64.CheckPointP521

open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64.P521.Check

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInvOrd Spec.P521.curve) : List Artifact := [
  C.checkApi.artifact AArch64.target {
    code := Impl.Ecdh.AArch64.Cfg.checkFn p521
    verified := verified h.inv }]

end VG.Generic.P521.AArch64.CheckPointP521
