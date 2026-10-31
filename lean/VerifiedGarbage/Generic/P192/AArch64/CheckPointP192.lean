module

public import VerifiedGarbage.Proof.Ecdh.AArch64.P192.CheckVerified
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-! # P-192's check of a public point on AArch64 -/

@[expose] public section

namespace VG.Generic.P192.AArch64.CheckPointP192

open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64.P192.Check

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInv Spec.P192.curve) : List Artifact := [
  C.checkApi.artifact AArch64.target {
    code := Impl.Ecdh.AArch64.Cfg.checkFn p192
    verified := verified h.inv }]

end VG.Generic.P192.AArch64.CheckPointP192
