module

public import VerifiedGarbage.Proof.Ecdh.AArch64.P384.CheckVerified
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface

/-! # P-384's check of a public point on AArch64 -/

@[expose] public section

namespace VG.Generic.P384.AArch64.CheckPointP384

open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64.P384.Check

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInvOrd Spec.P384.curve) : List Artifact := [
  C.checkApi.artifact AArch64.target {
    code := Impl.Ecdh.AArch64.Cfg.checkFn p384
    verified := verified h.inv }]

end VG.Generic.P384.AArch64.CheckPointP384
