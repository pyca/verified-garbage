import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourScalarLoopTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourFallback

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample
open VG.Impl.MlDsa.AArch64.Optimized.BoundedFour (vectorBody)

theorem fallback_relCT {σ τ : State} {η d : Nat} (hη : η=2∨η=4)
    {table p q : Addr} {L M : List Zq} {X Y : List Byte}
    (h : TranscriptPair σ τ η table p q L M X Y)
    (sx : ScalarLayout σ p q X) (sy : ScalarLayout τ p q Y) (hL : L.length≤256) :
    RelCT isa
      (fun s t=>LoopInv σ η table p q L X d s ∧ LoopInv τ η table p q M Y d t)
      (fallback η) (ScalarPairDone σ τ η p q L M X Y) := by
  unfold fallback
  refine RelCT.seq (R := fun s t=>ScalarInv σ η p q L X d s ∧ ScalarInv τ η p q M Y d t)
    ?_ (scalarPhase_relCT hη h sx sy hL)
  have hc : ∃hint,(taint.check (Taint.ofRegs []) (.block fallbackSetup) hint).isSome=true:=⟨_,by taint_decide⟩
  obtain ⟨_,hc⟩:=hc
  have ct : RelCT isa
      (fun s t=>LoopInv σ η table p q L X d s ∧ LoopInv τ η table p q M Y d t)
      (.block fallbackSetup) (fun _ _=>True) :=
    RelCT.taint (A := taint) _ (fun _ _ hh=>VG.Proof.MlKem.AArch64.agree_of
      (by rw [hh.1.keep.sp,hh.2.keep.sp]; exact h.sp)
      (fun _ hr=>False.elim (List.not_mem_nil hr))) hc
  exact (ct.wp (fun _ _ hh=>⟨fallbackSetup_inv hh.1,fallbackSetup_inv hh.2⟩)).mono
    (fun _ _ hh=>hh) (fun _ _ hh=>hh.2)

/-- All vector lookups, scalar stores, and both adaptive parser exits are
fixed by the standard bounded-sampler rejection transcript. -/
theorem parsedPhase_relCT {σ τ : State} {η d : Nat} (hη : η=2∨η=4)
    {table p q : Addr} {L M : List Zq} {X Y : List Byte}
    (h : TranscriptPair σ τ η table p q L M X Y)
    (sx : ScalarLayout σ p q X) (sy : ScalarLayout τ p q Y) (hL : L.length≤256) :
    RelCT isa
      (fun s t=>LoopInv σ η table p q L X d s ∧ LoopInv τ η table p q M Y d t)
      (.seq (.ite (.zero .x .x8) (.block [])
        (.loop (.block (vectorBody true η)) (.nonzero .x .x8))) (fallback η))
      (ScalarPairDone σ τ η p q L M X Y) := by
  refine RelCT.seq (vectorPhase_relCT hη h) ?_
  apply RelCT.mono (RelCT.exists_ (fun j=>fallback_relCT (d := j) hη h sx sy hL))
  · intro s t hh
    obtain ⟨j,hs,ht,_⟩:=hh
    exact ⟨j,hs,ht⟩
  · intro _ _ hh; exact hh

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
