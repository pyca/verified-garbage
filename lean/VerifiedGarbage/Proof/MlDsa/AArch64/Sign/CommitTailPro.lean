import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailOutput

/-! ## From `CommitTailSaveV.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlKem.AArch64 (wp_strq)
open VG.Impl.MlDsa.AArch64.Sign.CommitTail
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)

/-- The selected prologue preserves all 128 bits of each callee-saved vector. -/
theorem saveV_ok {s : State}
    (hout : ∀i<8, InRegions s.wr (s.gpr .x3+BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block save) s fun t => RegKeep [] s t ∧ t.v=s.v ∧
      Frame [⟨s.gpr .x3,128⟩] s.mem t.mem ∧
      ∀i<8,t.mem.read (s.gpr .x3+BitVec.ofNat 64 (16*i)) 16=s.v (vreg (8+i)) := by
  unfold save
  rw [List.map_eq_flatMap]
  refine wp_range_flatMap (M:=isa)
    (fun k t => RegKeep [] s t ∧ t.v=s.v ∧ Frame [⟨s.gpr .x3,128⟩] s.mem t.mem ∧
      ∀i<k,t.mem.read (s.gpr .x3+BitVec.ofNat 64 (16*i)) 16=s.v (vreg (8+i)))
    (fun k t hk ht => ?_) 8 (Nat.le_refl _) s
    ⟨RegKeep.refl _ _,rfl,Frame.refl _ _,fun _ h => by omega⟩
  refine wp_strq ⟨by omega,by omega⟩ (by rw [ht.1.gpr .x3 (by simp)])
    (by rw [ht.1.wr]; exact hout k hk) fun u hu => WP.block_nil_iff.mpr ?_
  have hm : u.mem=t.mem.write (s.gpr .x3+BitVec.ofNat 64 (16*k)) 16 (s.v (vreg (8+k))) := by
    rw [hu.mem,ht.2.1]
  refine ⟨(ht.1.trans (RegKeep.vmem hu)).mono (by simp),hu.v.trans ht.2.1,?_,?_⟩
  · rw [hm]
    exact ht.2.2.1.write (r:=⟨s.gpr .x3,128⟩) (by simp) _
      (Offset.contains_base _ (by omega) (by omega))
  · intro i hi
    rw [hm]
    by_cases he : i=k
    · subst i; exact read_write16 _ _ _
    · rw [Mem.read_write_sep (Offset.sep (s.gpr .x3) (d:=16*i) (n:=16) (e:=16*k) (k:=16)
        (by omega) (by omega) (by omega)) (by decide)]
      exact ht.2.2.2 i (by omega)

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

/-! ## From `CommitTailSaveG.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3.AArch64 (wp_str)
open VG.Impl.MlDsa.AArch64.Sign.CommitTail

/-- Saves precisely the nonvolatile scalar registers used by this helper. -/
theorem saveG_ok {s : State}
    (hout : ∀i<4, InRegions s.wr (s.gpr .x3+BitVec.ofNat 64 (128+8*i)) 8) :
    WP isa (.block ((List.range 4).map fun i => .str .x saved[i]! .x3 (128+8*i))) s fun t =>
      RegKeep [] s t ∧ t.v=s.v ∧ Frame [⟨s.gpr .x3+128,32⟩] s.mem t.mem ∧
      ∀i<4,t.mem.readW (s.gpr .x3+BitVec.ofNat 64 (128+8*i)) 64=s.gpr saved[i]! := by
  rw [List.map_eq_flatMap]
  refine wp_range_flatMap (M:=isa)
    (fun k t => RegKeep [] s t ∧ t.v=s.v ∧ Frame [⟨s.gpr .x3+128,32⟩] s.mem t.mem ∧
      ∀i<k,t.mem.readW (s.gpr .x3+BitVec.ofNat 64 (128+8*i)) 64=s.gpr saved[i]!)
    (fun k t hk ht => ?_) 4 (Nat.le_refl _) s
    ⟨RegKeep.refl _ _,rfl,Frame.refl _ _,fun _ h => by omega⟩
  refine wp_str ⟨by omega,by omega⟩ (by rw [ht.1.gpr .x3 (by simp)])
    (by rw [ht.1.wr]; exact hout k hk) fun u hu => WP.block_nil_iff.mpr ?_
  have hm : u.mem=t.mem.writeW (s.gpr .x3+BitVec.ofNat 64 (128+8*k)) (s.gpr saved[k]!) := by
    rw [hu.mem,ht.1.gpr _ (by simp)]
  refine ⟨(ht.1.trans (RegKeep.mupd hu)).mono (by simp),hu.vec.trans ht.2.1,?_,?_⟩
  · rw [hm]
    exact ht.2.2.1.writeW (r:=⟨s.gpr .x3+128,32⟩) (by simp) _
      (Offset.contains (s.gpr .x3) (d:=128+8*k) (e:=128) (n:=8) (k:=32)
        (by omega) (by omega) (by decide))
  · intro i hi
    rw [hm]
    by_cases he : i=k
    · subst i; rw [Mem.readW_writeW_self64]
    · rw [Mem.readW_writeW_sep (Offset.sep (s.gpr .x3) (d:=128+8*i) (n:=8) (e:=128+8*k) (k:=8)
        (by omega) (by omega) (by omega)) (by decide)]
      exact ht.2.2.2 i (by omega)

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

/-! ## From `CommitTailPro.lean` -/

section

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

end
