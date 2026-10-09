import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedSpecFrame

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa

structure ZEntryFrame (s : State) (m : Mem) : Prop where
  products : pairedProductsReduced m (s.gpr .x0) (s.gpr .x1)
  data : ∀j<2,Reduced m (pairPolyPtr (s.gpr .x2) j)
  sum : ∀j<2,add (polyAt m (pairPolyPtr (s.gpr .x2) j)) (pairedProduct m (s.gpr .x0) (s.gpr .x1) j)=
    add (polyAt s.mem (pairPolyPtr (s.gpr .x2) j)) (pairedProduct s.mem (s.gpr .x0) (s.gpr .x1) j)

theorem zEntry_frame {s : State} {m : Mem} (h : ZSpecPre s)
    (hf : Frame [⟨s.gpr .x4+BitVec.ofNat 64 2048,128⟩] s.mem m) : ZEntryFrame s m := by
  have hc : ∀r∈[⟨s.gpr .x4+BitVec.ofNat 64 2048,128⟩],(⟨s.gpr .x0,1024⟩:Region).Disjoint r := by
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.commonWork.sub_right (Offset.sub_base _ (by decide))
  have hs : ∀r∈[⟨s.gpr .x4+BitVec.ofNat 64 2048,128⟩],(⟨s.gpr .x1,2048⟩:Region).Disjoint r := by
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.secretWork.sub_right (Offset.sub_base _ (by decide))
  have ho : ∀r∈[⟨s.gpr .x4+BitVec.ofNat 64 2048,128⟩],(⟨s.gpr .x2,2048⟩:Region).Disjoint r := by
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.dataWork.sub_right (Offset.sub_base _ (by decide))
  refine ⟨pairedProductsReduced_frame hf hc hs h.products,?_,?_⟩
  · intro j hj
    apply VG.Proof.MlDsa.Verify.reduced_frame hf _ (h.data j hj)
    intro r hr
    exact (ho r hr).sub_left (Offset.sub_base _ (by omega))
  · intro j hj
    rw [pairedProduct_frame hf hc hs hj,VG.Proof.MlDsa.Verify.polyAt_frame hf]
    intro r hr
    exact (ho r hr).sub_left (Offset.sub_base _ (by omega))

end VG.Proof.MlDsa.AArch64.Optimized.Paired
