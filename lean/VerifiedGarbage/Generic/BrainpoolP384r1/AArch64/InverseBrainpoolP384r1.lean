module

public import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP384r1.InverseVerified
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-! # brainpoolP384r1's inversions modulo `p` and `n` on AArch64 -/

@[expose] public section

namespace VG.Generic.BrainpoolP384r1.AArch64.InverseBrainpoolP384r1

open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.BrainpoolP384r1.Inverse

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInv Spec.BrainpoolP384r1.curve) : List Artifact := [
  C.invPApi.artifact AArch64.target {
    code := brainpoolp384r1.invFn brainpoolp384r1.pPowI
    verified := p_verified h.inv },
  C.invNApi.artifact AArch64.target {
    code := brainpoolp384r1.invFn brainpoolp384r1.nPowI
    verified := n_verified h.inv }]

end VG.Generic.BrainpoolP384r1.AArch64.InverseBrainpoolP384r1
