module

public import VerifiedGarbage.Proof.Ecdh.AArch64.BrainpoolP512r1.CheckVerified
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-! # brainpoolP512r1's check of a public point on AArch64 -/

@[expose] public section

namespace VG.Generic.BrainpoolP512r1.AArch64.CheckPointBrainpoolP512r1

open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64.BrainpoolP512r1.Check

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInv Spec.BrainpoolP512r1.curve) : List Artifact := [
  C.checkApi.artifact AArch64.target {
    code := Impl.Ecdh.AArch64.Cfg.checkFn brainpoolp512r1
    verified := verified h.inv }]

end VG.Generic.BrainpoolP512r1.AArch64.CheckPointBrainpoolP512r1
