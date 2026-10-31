module
import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.InverseCfgLit

public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvInterface
public import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.InverseVerified
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.InverseLit
public import VerifiedGarbage.Proof.Framework.Registration

/-! # P-521's inversions modulo `p` and `n` on x86-64 -/

@[expose] public section

namespace VG.Generic.P521.X86_64.InverseP521

open VG.Impl.Ecdsa.X86_64 VG.Proof.Ecdsa.X86_64.P521.Inverse

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInvOrd Spec.P521.curve) : List Artifact :=
  ([false, true].map fun adx =>
    C.invPApi.artifact X86_64.target {
      suffix := (if adx then "_adx" else "")
      code := (cfg adx).invFn (cfg adx).pPowI
      verified := p_verified h.inv adx
      features := if adx then ["bmi2", "adx"] else [] }) ++
  ([false].map fun adx =>
    C.invNApi.artifact X86_64.target {
      suffix := (if adx then "_adx" else "")
      code := (cfg adx).invFn (cfg adx).nPowI
      verified := n_verified h.inv adx
      features := [] })

end VG.Generic.P521.X86_64.InverseP521
