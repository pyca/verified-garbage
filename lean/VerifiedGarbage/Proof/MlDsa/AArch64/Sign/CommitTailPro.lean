import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailSaveG

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3.AArch64 (wp_mov)
open VG.Impl.MlDsa.AArch64.Sign.CommitTail
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)

structure Saved (s : State) (m : Mem) : Prop where
  vec : ∀i<8,m.read (s.gpr .x3+BitVec.ofNat 64 (16*i)) 16=s.v (vreg (8+i))
  regs : ∀i<4,m.readW (s.gpr .x3+BitVec.ofNat 64 (128+8*i)) 64=s.gpr saved[i]!

/-- Establishes the private work pointer and preserves the helper's complete
nonvolatile register state inside the first 160 workspace bytes. -/
theorem pro_ok {s : State}
    (hv : ∀i<8, InRegions s.wr (s.gpr .x3+BitVec.ofNat 64 (16*i)) 16)
    (hg : ∀i<4, InRegions s.wr (s.gpr .x3+BitVec.ofNat 64 (128+8*i)) 8) :
    WP isa (.block pro) s fun t =>
      RegKeep [.x19,.x20,.x21] s t ∧ t.v=s.v ∧ Saved s t.mem ∧
      Frame [⟨s.gpr .x3,160⟩] s.mem t.mem ∧
      t.gpr .x19=s.gpr .x3 ∧ t.gpr .x20=s.gpr .x6 ∧ t.gpr .x21=s.gpr .x2 := by
  unfold pro
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (saveV_ok hv) fun a ⟨ha,hva,hfa,hsa⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (saveG_ok (fun i hi => by rw [ha.wr,ha.gpr .x3 (by simp)]; exact hg i hi))
    fun b ⟨hb,hvb,hfb,hsb⟩ => ?_
  rw [ha.gpr .x3 (by simp)] at hfb hsb
  have hsaved : Saved s b.mem := by
    refine ⟨?_,?_⟩
    · intro i hi
      rw [hfb.read (r:=⟨s.gpr .x3,128⟩) (Offset.contains_base _ (by omega) (by omega))
        (by
          intro r hr
          rcases List.mem_singleton.mp hr with rfl
          exact (Offset.disjoint_base (s.gpr .x3) (d:=128) (n:=32) (k:=128) (by decide) (by decide)).symm) (by decide)]
      exact hsa i hi
    · intro i hi
      rw [hsb i hi,ha.gpr _ (by simp)]
  have hf : Frame [⟨s.gpr .x3,160⟩] s.mem b.mem := by
    apply Frame.trans
    · exact hfa.sub (by
        intro r hr
        rcases List.mem_singleton.mp hr with rfl
        exact ⟨⟨s.gpr .x3,160⟩,by simp,by
          simpa using Offset.sub_base (s.gpr .x3) (d:=0) (n:=128) (k:=160) (by decide)⟩)
    · exact hfb.sub (by
        intro r hr
        rcases List.mem_singleton.mp hr with rfl
        exact ⟨⟨s.gpr .x3,160⟩,by simp,
          Offset.sub_base (s.gpr .x3) (d:=128) (n:=32) (k:=160) (by decide)⟩)
  refine wp_mov fun c hc => wp_mov fun d hd => wp_mov fun t ht => WP.block_nil_iff.mpr ?_
  refine ⟨(((((ha.trans hb).trans (RegKeep.upd hc)).trans (RegKeep.upd hd)).trans
    (RegKeep.upd ht))).mono (by simp),ht.vec.trans (hd.vec.trans (hc.vec.trans (hvb.trans hva))),?_,?_,?_,?_,?_⟩
  · rw [ht.mem,hd.mem,hc.mem]; exact hsaved
  · rw [ht.mem,hd.mem,hc.mem]; exact hf
  · rw [ht.other .x19 (by decide),hd.other .x19 (by decide),hc.gpr,
      hb.gpr .x3 (by simp),ha.gpr .x3 (by simp)]
  · rw [ht.other .x20 (by decide),hd.gpr,hc.other .x6 (by decide),
      hb.gpr .x6 (by simp),ha.gpr .x6 (by simp)]
  · rw [ht.gpr,hd.other .x2 (by decide),hc.other .x2 (by decide),
      hb.gpr .x2 (by simp),ha.gpr .x2 (by simp)]

end VG.Proof.MlDsa.AArch64.Sign.CommitTail
