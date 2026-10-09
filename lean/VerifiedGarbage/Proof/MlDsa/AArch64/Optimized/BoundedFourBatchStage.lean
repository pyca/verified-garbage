import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourSqueezeStage
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourBatch

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Sample
open VG.Proof.MlKem.AArch64
open VG.Proof.Sha3.AArch64.Neon

theorem batchStage_ok {η : Nat} (hη : η=2∨η=4) {σ s : State} (hp : SamplerPre σ)
    {A : Nat→Spec.Sha3.State} {L : Nat→List Zq} (hs : SamplerRun σ s A L)
    {off : Nat} (ho : off≤272) {X : Nat→List Byte}
    (hl : BatchLayout s (samplerScratch σ) (samplerOut σ) off X) :
    WP isa (Impl.MlDsa.AArch64.Optimized.BoundedFour.batch true η off) s fun t=>
      SamplerRun σ t A (fun i=>rbFold η (L i) (X i)) := by
  have hi : BatchInv s s (samplerScratch σ) (samplerOut σ) L :=
    ⟨Keep.refl _ _,Frame.refl _ _,hs.env.x19,hs.env.x21,hs.table,hs.fields⟩
  refine WP.mono (batch_ok hη ho hl hi) fun t ht=>?_
  have hcount : (⟨samplerScratch σ+7904#64,32⟩ : Region).Sub (samplerWorkspace σ) :=
    Offset.sub_base _ (d := 7904) (n := 32) (k := 8192) (by decide)
  have hout : (ResidentRej.saveR σ).Disjoint (samplerOutput σ) :=
    (hp.output_work.sub_right (Offset.sub_base _ (d := 7968) (n := 144) (k := 8192) (by decide))).symm
  have hsave : (ResidentRej.saveR σ).Disjoint (⟨samplerScratch σ+7904#64,32⟩ : Region) :=
    Offset.disjoint _ (d := 7968) (e := 7904) (n := 144) (k := 32) (by decide) (by decide) (by decide)
  have hpair (p : Nat) (hpn : p<2) :
      (pairR (ResidentRej.stateP σ p)).Disjoint (samplerOutput σ) :=
    (hp.output_work.sub_right (Offset.sub_base _ (d := 400*p) (n := 400) (k := 8192) (by omega))).symm
  have pairKeep (p : Nat) (hpn : p<2) (a b : Spec.Sha3.State)
      (hh : PairAt s.mem (ResidentRej.stateP σ p) a b) :
      PairAt t.mem (ResidentRej.stateP σ p) a b := by
    intro i hii
    rw [ht.frame.read (pair_contains _ hii) (fun r hr=>by
      rcases (show r=samplerOutput σ∨r=⟨samplerScratch σ+7904#64,32⟩ by simpa [batchWrites,samplerOutput] using hr) with rfl|rfl
      · exact hpair p hpn
      · exact Offset.disjoint _ (d := 400*p) (e := 7904) (n := 400) (k := 32) (by omega) (by omega) (by decide)) (by decide)]
    exact hh i hii
  refine ⟨?_,?_,?_,ht.table,ht.fields⟩
  · exact hs.env.frameStep ht.frame (fun r hr=>by
      rcases (show r=samplerOutput σ∨r=⟨samplerScratch σ+7904#64,32⟩ by simpa [batchWrites,samplerOutput] using hr) with rfl|rfl
      · exact ⟨ResidentRej.aR 4 σ,by simp,fun _ h=>h⟩
      · exact ⟨ResidentRej.scrR σ,by simp,hcount⟩)
      (fun r hr=>by
        rcases (show r=samplerOutput σ∨r=⟨samplerScratch σ+7904#64,32⟩ by simpa [batchWrites,samplerOutput] using hr) with rfl|rfl
        · exact hout
        · exact hsave)
      ht.keep.rd ht.keep.wr ht.keep.sp (fun r hr=>ht.keep.get r (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl|rfl|rfl|rfl <;> decide))
  · have he : ResidentRej.stateP σ 0=samplerScratch σ := by change samplerScratch σ+0#64=_; exact BitVec.add_zero _
    have h0:=hs.pair0
    rw [←he] at h0 ⊢
    exact pairKeep 0 (by decide) _ _ h0
  · exact pairKeep 1 (by decide) _ _ hs.pair1

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
