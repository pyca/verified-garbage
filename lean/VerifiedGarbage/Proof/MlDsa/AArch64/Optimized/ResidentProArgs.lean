import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentSaved

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlKem.AArch64 (wp_strw wp_mov)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentMask (proArgs)

theorem proArgs_ok (s : State) (hw : InRegions s.wr (s.gpr .x4+7904) 4) :
    WP isa (.block proArgs) s fun t => RegKeep [.x19,.x20,.x21,.x22] s t ∧
      t.mem=s.mem.writeW (s.gpr .x4+7904) ((s.gpr .x1).setWidth 32) ∧
      t.gpr .x19=s.gpr .x4 ∧ t.gpr .x20=s.gpr .x0 ∧
      t.gpr .x21=s.gpr .x2 ∧ t.gpr .x22=s.gpr .x3 := by
  unfold proArgs
  refine wp_strw ⟨by decide,by decide⟩ rfl hw fun a ha => ?_
  refine wp_mov fun b hb eb => wp_mov fun c hc ec => wp_mov fun f hf ef =>
    wp_mov fun t ht et => WP.block_nil_iff.mpr ⟨?_,?_,?_,?_,?_,?_⟩
  · have h0 : RegKeep [] s a := ⟨fun r _ => congrFun ha.gpr r,ha.rd,ha.wr,ha.sp⟩
    exact (h0.trans (RegKeep.only (((hb.trans hc).trans hf).trans ht))).mono (by simp)
  · rw [ht.mem,hf.mem,hc.mem,hb.mem,ha.mem]
    rfl
  · rw [ht.get .x19,hf.get .x19,hc.get .x19,eb,ha.gpr]
  · rw [ht.get .x20,hf.get .x20,ec,hb.get .x0,ha.gpr]
  · rw [ht.get .x21,ef,hc.get .x2,hb.get .x2,ha.gpr]
  · rw [et,hf.get .x3,hc.get .x3,hb.get .x3,ha.gpr]

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
