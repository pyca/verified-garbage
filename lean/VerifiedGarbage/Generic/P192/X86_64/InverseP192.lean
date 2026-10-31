module

public import VerifiedGarbage.Proof.Ecdsa.X86_64.P192.InverseVerified
public import VerifiedGarbage.Proof.Ecdsa.X86_64.P192.InverseLit
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-! # P-192's inversions modulo `p` and `n` on x86-64 -/

@[expose] public section

namespace VG.Generic.P192.X86_64.InverseP192

open VG.Impl.Ecdsa.X86_64 VG.Proof.Ecdsa.X86_64.P192.Inverse

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInv Spec.P192.curve) : List Artifact :=
  ([false].map fun adx =>
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
      features := if adx then ["bmi2", "adx"] else [] })

end VG.Generic.P192.X86_64.InverseP192
