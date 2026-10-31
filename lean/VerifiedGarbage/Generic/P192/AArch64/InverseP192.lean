module

public import VerifiedGarbage.Proof.Ecdsa.AArch64.P192.InverseVerified
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-! # P-192's inversions modulo `p` and `n` on AArch64 -/

@[expose] public section

namespace VG.Generic.P192.AArch64.InverseP192

open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.P192.Inverse

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInv Spec.P192.curve) : List Artifact := [
  C.invPApi.artifact AArch64.target {
    code := p192.invFn p192.pPowI
    verified := p_verified h.inv },
  C.invNApi.artifact AArch64.target {
    code := p192.invFn p192.nPowI
    verified := n_verified h.inv }]

end VG.Generic.P192.AArch64.InverseP192
