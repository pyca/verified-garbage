import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourBatchState

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
