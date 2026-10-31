module

public import VerifiedGarbage.Proof.Ecdsa.AArch64.P224.PointOpsVerified
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-! # P-224's complete projective addition on AArch64 -/

@[expose] public section

namespace VG.Generic.P224.AArch64.PointOpsP224

open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.P224.PointOps

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInv Spec.P224.curve) : List Artifact := [
  C.projAddApi.artifact AArch64.target {
    code := projAddP224
    verified := verified h.law h.inv }]

end VG.Generic.P224.AArch64.PointOpsP224
