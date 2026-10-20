module
public import VerifiedGarbage.Proof.Dsa.X86_64.ShapeCTState
public import VerifiedGarbage.Proof.Dsa.X86_64.ShapeSizes
public import VerifiedGarbage.Proof.Dsa.X86_64.ShapeTail

import VerifiedGarbage.Proof.Dsa.X86_64.ShapeSizesCT
import VerifiedGarbage.Proof.Dsa.X86_64.ShapeTailCT
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel

/-! # Constant time of the entire public DSA domain-shape check -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem domainShape_split {s t : State} {trace : List Leak}
    (h : Exec isa Checks.domainShape s trace t) :
    Exec isa (.seq shapeSizes (.block shapeTail)) s trace t := by
  unfold Checks.domainShape seqs at h
  cases h with | seq ha h =>
    cases h with | seq hb h =>
      cases h with | seq hc h =>
        cases h with | seq hd h =>
          cases h with | seq he h =>
            cases h with | seq hf hg =>
              simpa only [shapeSizes, seqs, widthChoice, shapeTail, oddCheck, oddCombine, shapeFinish,
                List.append_assoc, List.cons_append, List.nil_append] using
                (Exec.seq (Exec.seq ha (Exec.seq hb (Exec.seq hc (Exec.seq hd (Exec.seq he hf))))) hg)

theorem domainShape_ct : RelCT isa (Two ShapeContext) Checks.domainShape (fun _ _ => True) := by
  have hs : RelCT isa (Two ShapeContext) shapeSizes (Two ShapeTailPre) := by
    refine two_post shapeSizes_ct ?_
    intro p s h
    exact WP.mono (shapeSizes_ok h.scr h.rdi p.extentBound h.pPointer h.qPointer h.pLength h.qLength
      h.pSource h.qSource p.pPositive p.pBound p.qPositive p.qBound)
      fun t ⟨ha, hm, _, hf, hk⟩ => ⟨h.frame hf hk (by decide), _, _, ha, hm⟩
  have ht := RelCT.seq hs shapeTail_ct
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  exact ht _ _ _ _ _ _ hp (domainShape_split e₁) (domainShape_split e₂)

end VG.Proof.Dsa.X86_64
