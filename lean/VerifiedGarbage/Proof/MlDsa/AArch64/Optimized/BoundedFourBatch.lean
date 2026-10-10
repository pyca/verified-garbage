import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourBatchState

/-! ## From `BoundedFourBatchStep.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample
open VG.Proof.MlKem.AArch64

def updateBatch (η i : Nat) (L : Nat→List Zq) (X : Nat→List Byte) : Nat→List Zq :=
 fun j=>if j=i then rbFold η (L i) (X i) else L j

theorem batchStep_ok {σ s : State} {b p : Addr} {η i off : Nat} (he : η=2∨η=4)
    (hi : i<4) (ho : off≤272) {L : Nat→List Zq} {X : Nat→List Byte}
    (hy : BatchLayout σ b p off X) (hs : BatchInv σ s b p L) :
    WP isa (Impl.MlDsa.AArch64.Optimized.BoundedFour.parse true η i off) s fun t=>
      BatchInv σ t b p (updateBatch η i L X) := by
  refine WP.mono (parse_ok he hi ho (hs.fields.bound i hi) (hy.length i hi)
    ((hy.vector i hi).frame hs.keep hs.frame (hy.streamsApart i hi))
    ((hy.scalar i hi).frame hs.keep hs.frame (hy.streamsApart i hi))
    hs.table (hs.fields.stored i hi)
    (by rw [hs.base]; rfl) (by rw [hs.output]; rfl) (by rw [hs.base]; rfl)
    (by rw [hs.base]) (hs.fields.count i hi)
    (by rw [hs.keep.rd,hs.keep.wr]; exact hy.countRead i hi)
    (by rw [hs.keep.wr]; exact hy.countWrite i hi) (hy.outputCount i hi i hi))
    fun t ⟨ht,hf,hstore,hcount⟩=>?_
  have hwide:=parseFrame_batch hi hf
  refine ⟨(hs.keep.trans ht).mono (by decide),hs.frame.trans hwide,?_,?_,
    hs.table.frame hwide hy.tableApart,?_⟩
  · rw [ht.gpr .x19 (by decide)]; exact hs.base
  · rw [ht.gpr .x21 (by decide)]; exact hs.output
  constructor
  · intro j hj
    unfold updateBatch
    split
    · exact rbFold_length_le (hs.fields.bound i hi) _
    · exact hs.fields.bound j hj
  · intro j hj
    by_cases heq : j=i
    · subst j
      simpa only [updateBatch,ite_true] using hstore
    · simp only [updateBatch,heq,ite_false]
      refine stored_frame hf ?_ (hs.fields.stored j hj) (hs.fields.bound j hj)
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl
      · exact outputs_apart p hj hi heq
      · exact hy.outputCount j hj i hi
  · intro j hj
    by_cases heq : j=i
    · subst j
      simpa only [updateBatch,ite_true] using hcount
    · simp only [updateBatch,heq,ite_false]
      rw [hf.readW (Region.contains_self (countAt b j) 8) (fun r hr=>?_) (by decide)]
      · exact hs.fields.count j hj
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl|rfl
        · exact (hy.outputCount i hi j hj).symm
        · exact counts_apart b hj hi heq

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourBatch.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample

theorem BatchInv.congr {σ s : State} {b p : Addr} {L L' : Nat→List Zq}
    (h : BatchInv σ s b p L) (he : ∀i<4,L i=L' i) : BatchInv σ s b p L' := by
  refine {h with fields := ⟨?_,?_,?_⟩}
  · intro i hi; rw [←he i hi]; exact h.fields.bound i hi
  · intro i hi; rw [←he i hi]; exact h.fields.stored i hi
  · intro i hi; rw [←he i hi]; exact h.fields.count i hi

theorem updateBatch_four (η : Nat) (L : Nat→List Zq) (X : Nat→List Byte) {i : Nat} (hi : i<4) :
    updateBatch η 3 (updateBatch η 2 (updateBatch η 1 (updateBatch η 0 L X) X) X) X i=
      rbFold η (L i) (X i) := by
  rcases (show i=0∨i=1∨i=2∨i=3 by omega) with rfl|rfl|rfl|rfl <;>
    simp only [updateBatch,Nat.reduceEqDiff,ite_true,ite_false]

theorem batch_ok {σ s : State} {b p : Addr} {η off : Nat} (he : η=2∨η=4)
    (ho : off≤272) {L : Nat→List Zq} {X : Nat→List Byte}
    (hy : BatchLayout σ b p off X) (hs : BatchInv σ s b p L) :
    WP isa (Impl.MlDsa.AArch64.Optimized.BoundedFour.batch true η off) s fun t=>
      BatchInv σ t b p (fun i=>rbFold η (L i) (X i)) := by
  unfold Impl.MlDsa.AArch64.Optimized.BoundedFour.batch
  refine WP.seq (WP.mono (batchStep_ok he (by decide : 0<4) ho hy hs) fun a ha=>?_)
  refine WP.seq (WP.mono (batchStep_ok he (by decide : 1<4) ho hy ha) fun b hb=>?_)
  refine WP.seq (WP.mono (batchStep_ok he (by decide : 2<4) ho hy hb) fun c hc=>?_)
  refine WP.mono (batchStep_ok he (by decide : 3<4) ho hy hc) fun t ht=>?_
  exact ht.congr (fun i hi=>updateBatch_four η L X hi)

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end
