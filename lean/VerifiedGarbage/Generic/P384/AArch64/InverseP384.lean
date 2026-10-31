module

public import VerifiedGarbage.Proof.Ecdsa.AArch64.P384.InverseVerified
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface

/-! # P-384's inversions modulo `p` and `n` on AArch64 -/

@[expose] public section

namespace VG.Generic.P384.AArch64.InverseP384

open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.P384.Inverse

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInvOrd Spec.P384.curve) : List Artifact := [
  C.invPApi.artifact AArch64.target {
    code := p384.invFn p384.pPowI
    verified := p_verified h.inv },
  C.invNApi.artifact AArch64.target {
    code := p384.invFn p384.nPowI
    verified := n_verified h.inv }]

end VG.Generic.P384.AArch64.InverseP384
