import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentProArgs

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Impl.MlDsa.AArch64.Optimized.ResidentMask (pro)

structure ProPost (s t : State) : Prop where
  keep : RegKeep [.x8,.x19,.x20,.x21,.x22] s t
  saved : Saved s (s.gpr .x4) t.mem
  frame : Frame [⟨s.gpr .x4+7968,144⟩,⟨s.gpr .x4+7904,4⟩] s.mem t.mem
  base : t.gpr .x19=s.gpr .x4
  seed : t.gpr .x20=s.gpr .x0
  out1 : t.gpr .x21=s.gpr .x2
  out2 : t.gpr .x22=s.gpr .x3
  gamma : t.mem.readW (s.gpr .x4+7904) 32=(s.gpr .x1).setWidth 32

/-- Establish the resident sampler frame and retain both independent output
pointers while saving the ordinary caller ABI in the scratch tail. -/
theorem pro_ok (s : State) (hw : (Region.mk (s.gpr .x4) 8192)∈s.wr) :
    WP isa (.block pro) s (ProPost s) := by
  unfold pro
  rw [WP.block_append_iff]
  refine WP.mono (save_ok s (fun i hi => ⟨_,hw,Offset.contains_base _ (by omega) (by omega)⟩)
    (fun i hi => ⟨_,hw,Offset.contains_base _ (by omega) (by omega)⟩)) ?_
  intro a ⟨ha,has,haf⟩
  have a4 := ha.gpr .x4 (by decide)
  have a1 := ha.gpr .x1 (by decide)
  refine WP.mono (proArgs_ok a (by
    rw [ha.wr,a4]
    exact ⟨_,hw,Offset.contains_base _ (by decide) (by decide)⟩)) ?_
  intro t ⟨ht,hm,hbase,hseed,ho1,ho2⟩
  rw [a4,a1] at hm
  have hgamma : Frame [⟨s.gpr .x4+7904,4⟩] a.mem t.mem := by
    rw [hm]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨(ha.trans ht).mono (by simp),?_,?_,hbase.trans a4,
    hseed.trans (ha.gpr .x0 (by decide)),ho1.trans (ha.gpr .x2 (by decide)),
    ho2.trans (ha.gpr .x3 (by decide)),?_⟩
  · exact has.keep hgamma (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      exact Offset.disjoint _ (Or.inr (by decide)) (by decide) (by decide))
  · exact (haf.mono (by intro r hr; simp only [List.mem_singleton] at hr; subst r; simp)).trans
      (hgamma.mono (by intro r hr; simp only [List.mem_singleton] at hr; subst r; simp))
  · rw [hm,Mem.readW_writeW_self32]

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
