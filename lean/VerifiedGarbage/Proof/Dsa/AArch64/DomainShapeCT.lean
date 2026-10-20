module
public import VerifiedGarbage.Proof.Dsa.AArch64.ShapeCTState
public import VerifiedGarbage.Proof.Dsa.AArch64.ShapeSizes
public import VerifiedGarbage.Proof.Dsa.AArch64.ShapeTail

import VerifiedGarbage.Proof.Dsa.AArch64.ShapeSizesCT
import VerifiedGarbage.Proof.Dsa.AArch64.ShapeTailCT

/-! # Constant time of the entire public DSA domain-shape check -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem domainShape_split {s t : State} {trace : List Leak}
    (h : Exec isa Checks.domainShape s trace t) :
    Exec isa (.seq shapeSizes (.block shapeTail)) s trace t := by
  exact h

theorem domainShape_ct : RelCT isa (Two ShapeContext) Checks.domainShape (fun _ _ => True) := by
  have hs : RelCT isa (Two ShapeContext) shapeSizes (Two ShapeTailPre) := by
    refine two_post shapeSizes_ct ?_
    intro p s h
    exact WP.mono (shapeSizes_ok h.scr h.x0 p.extentBound h.pPointer h.qPointer h.pLength h.qLength
      h.pSource h.qSource p.pPositive p.pBound p.qPositive p.qBound)
      fun t ⟨ha, hm, _, hf, hk⟩ => ⟨h.frame hf hk (by decide), _, _, ha, hm⟩
  have ht := RelCT.seq hs shapeTail_ct
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  exact ht _ _ _ _ _ _ hp (domainShape_split e₁) (domainShape_split e₂)

end VG.Proof.Dsa.AArch64
