module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
public import VerifiedGarbage.Proof.Ecdh.AArch64.P256.CheckVerified
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-! # P-256's check of a public point on AArch64 -/

@[expose] public section

namespace VG.Generic.P256.AArch64.CheckPointP256

open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64.P256.Check

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInvToMOrd Spec.P256.curve) : List Artifact := [
  C.checkApi.artifact AArch64.target {
    code := Impl.Ecdh.AArch64.Cfg.checkFn p256
    verified := verified h.inv }]

end VG.Generic.P256.AArch64.CheckPointP256
