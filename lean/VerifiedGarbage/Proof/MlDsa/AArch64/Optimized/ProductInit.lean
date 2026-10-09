import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductFirstLoop

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep wp_scalar wp_vop)

def productInit : List Instr :=
  VG.Impl.MlDsa.AArch64.Arith.movW .x10 4236238847 ++ [.vop (.dup .s4 .v30 .x10)] ++ firstInit

theorem productConst_ok (s : State) :
    WP isa (.block (VG.Impl.MlDsa.AArch64.Arith.movW .x10 4236238847 ++
      ([.vop (.dup .s4 .v30 .x10)] : List Instr))) s fun t =>
    Keep [.x10] s t ∧ t.mem=s.mem ∧ t.v .v30=HighPack.repeatedWord 4236238847 := by
  refine wp_scalar (by rfl) (VG.Proof.MlDsa.AArch64.Arith.movW_ok .x10 _ s)
    fun a ⟨⟨ha,hm⟩,hk⟩ hv => ?_
  refine wp_vop (d := .v30) rfl fun t ht => WP.block_nil_iff.mpr ?_
  refine ⟨?_,by rw [ht.mem,hm],?_⟩
  · refine ⟨by intro r hr; rw [ht.gpr,hk.gpr r hr],by rw [ht.rd,hk.rd],
      by rw [ht.wr,hk.wr],by rw [ht.sp,hk.sp],?_⟩
    intro r hr
    rw [ht.other r (by intro he; subst r; simp [preservedV] at hr),hv]
  · rw [ht.v,ha]
    change ofVWords _ _ _ _ = HighPack.repeatedWord _
    simp only [BitVec.setWidth_setWidth_of_le _ (by decide : 32≤64),BitVec.setWidth_eq,HighPack.repeatedWord]
    rfl

theorem productInit_ok (s : State) : WP isa (.block productInit) s fun t =>
    Keep [.x3,.x4,.x5,.x6,.x7,.x9,.x10,.x11] s t ∧ t.mem=s.mem ∧
    t.gpr .x11=8 ∧ ProductConstants t := by
  unfold productInit
  rw [WP.block_append_iff]
  refine WP.mono (productConst_ok s) fun a ⟨hka,hma,h30⟩ => ?_
  unfold firstInit
  rw [WP.block_append_iff]
  refine WP.mono (HighPack.vc_ok a .v31 8380417) fun b hb => ?_
  refine WP.mono (firstSetup_ok b) fun t ⟨⟨⟨h11,hm⟩,hk⟩,hv⟩ => ?_
  refine ⟨((hka.trans (constKeep_keep hb.1 (by decide))).trans hk).mono,
    hm.trans (hb.1.mem.trans hma),h11,?_⟩
  exact ⟨by rw [hv,hb.2]; rfl,by rw [hv,hb.1.vec .v30 (by decide),h30]; rfl⟩

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
