import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourBatchStep

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
