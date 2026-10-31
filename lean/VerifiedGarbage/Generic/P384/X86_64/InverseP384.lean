module
import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.InverseCfgLit

public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvInterface
public import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.InverseVerified
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.InverseLit
public import VerifiedGarbage.Proof.Framework.Registration

/-! # P-384's inversions modulo `p` and `n` on x86-64 -/

@[expose] public section

namespace VG.Generic.P384.X86_64.InverseP384

open VG.Impl.Ecdsa.X86_64 VG.Proof.Ecdsa.X86_64.P384.Inverse

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInvOrd Spec.P384.curve) : List Artifact :=
  ([false, true].map fun adx =>
    C.invPApi.artifact X86_64.target {
      suffix := (if adx then "_adx" else "")
      code := (cfg adx).invFn (cfg adx).pPowI
      verified := p_verified h.inv adx
      features := if adx then ["bmi2", "adx"] else [] }) ++
  ([false, true].map fun adx =>
    C.invNApi.artifact X86_64.target {
      suffix := (if adx then "_adx" else "")
      code := (cfg adx).invFn (cfg adx).nPowI
      verified := n_verified h.inv adx
      features := if adx then ["bmi2", "adx"] else [] })

end VG.Generic.P384.X86_64.InverseP384
