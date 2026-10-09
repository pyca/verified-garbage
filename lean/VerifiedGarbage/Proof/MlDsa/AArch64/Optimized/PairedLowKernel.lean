import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedKernel

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.Paired
open VG.Proof.MlKem.AArch64 (Keep)

theorem pairedLowKernel_ok (g : Nat) (hg : VG.Proof.MlDsa.AArch64.Round.IsG g) {s₀ s : State}
    {gr : List Reg} {vr : List VReg}
    (hf : CallFrame gr vr s₀ s) (hs : Saved s.mem (s.gpr .x0) s₀.v)
    (ha : KernelAccess s) (ht : PairedTable.Words s.mem (s.gpr .x1))
    (hdw : (⟨s.gpr .x1,4096⟩:Region).Disjoint ⟨s.gpr .x0,2048⟩)
    (hdd : (⟨s.gpr .x1,4096⟩:Region).Disjoint ⟨s.gpr .x15,2048⟩)
    (hsd : (⟨s.gpr .x0+BitVec.ofNat 64 2048,128⟩:Region).Disjoint ⟨s.gpr .x15,2048⟩)
    (hda : (⟨s.gpr .x1,4096⟩:Region).Disjoint ⟨s.gpr .x16,2048⟩)
    (hsa : (⟨s.gpr .x0+BitVec.ofNat 64 2048,128⟩:Region).Disjoint ⟨s.gpr .x16,2048⟩)
    (haw : ∀off,off+16≤2048 → InRegions s.wr (s.gpr .x16+BitVec.ofNat 64 off) 16) :
    WP isa (kernelPaired g) s fun t =>
      ∃u,Prepared s u ∧ LowSetup g s u ∧
        Keep (gr++kernelRegs) s₀ t ∧
        let d := lowPassData g (s.gpr .x0) (s.gpr .x15) (s.gpr .x16) (lowConstantsAt u) (dataAt u) 8
        t.mem=d.mem ∧ t.gpr .x0=dataReturn .r0 d := by
  apply lowKernel_wp
  refine WP.seq (WP.mono (firstKernel_access_ok ha ht hdw) fun b ⟨hb,hq,h0,h1,_,_,hm⟩ => ?_)
  have hq' : ∀e<4,vword (b.v .v31) e=8380417#32 := by
    intro e he
    rw [hq.qv]
    exact HighPack.repeatedWord_lane 8380417 he
  refine WP.seq (WP.mono (lowMiddle_ok g hg b hq') fun u ⟨hu,hum,hu0,hu2,hu12,hc⟩ => ?_)
  have huf := ((hf.trans (CallFrame.ofKeepWide hb)).trans hu)
  have hu2' : u.gpr .x2=s.gpr .x0 := by rw [hu2,h0]; bv_omega
  have hu1 : u.gpr .x1=s.gpr .x1+BitVec.ofNat 64 3840 := by
    rw [hu.gpr .x1 (by decide),h1]
    rfl
  have hu15 : u.gpr .x15=s.gpr .x15 :=
    (hu.gpr .x15 (by decide)).trans (hb.get .x15 (by decide))
  have hu16 : u.gpr .x16=s.gpr .x16 :=
    (hu.gpr .x16 (by decide)).trans (hb.get .x16 (by decide))
  have huframe : Frame [⟨s.gpr .x0,2048⟩] s.mem u.mem := by
    rw [hum,hm]; exact firstPass_frame (by decide)
  have htu : PairedTable.Words u.mem (s.gpr .x1) :=
    tableWords_frame ht huframe (by simpa only [List.mem_singleton,forall_eq] using hdw)
  have hsu : Saved u.mem (s.gpr .x0) s₀.v := hs.workFrame huframe
  have hac : LowSetup g s u := by
    refine ⟨hc.ready,hc.flags,hc.scale,?_,?_⟩
    · simpa only [hb.get .x8 (by decide)] using hc.lower
    · simpa only [hb.get .x8 (by decide)] using hc.width
  refine WP.mono (lowKernel_ok g hg huf hsu hu2' ?_ ?_ ?_ htu ?_ ?_ hu1 hu12 hc.ready ?_ ?_ ?_)
    fun t ⟨hkeep,htm,htv⟩ => ?_
  · simpa only [hu15] using hsd
  · intro p hp
    simp only [hu.rd,hu.wr,hb.rd,hb.wr,BitVec.add_assoc,←BitVec.ofNat_add]
    apply ha.workRead
    obtain ⟨i,rfl⟩ := (extraSlots_mem _ _).mp hp
    omega
  · simpa only [hu16] using hsa
  · simpa only [hu15] using hdd
  · simpa only [hu16] using hda
  · simpa only [hu.rd,hu.wr,hb.rd,hb.wr] using ha.table
  · intro i hi p j
    simp only [hu.rd,hu.wr,hb.rd,hb.wr,hu2',BitVec.add_assoc,←BitVec.ofNat_add]
    exact ha.workRead _ (by omega)
  · intro v hv i
    simp only [hu.rd,hu.wr,hb.rd,hb.wr,hu15,hu16,BitVec.add_assoc,←BitVec.ofNat_add]
    have hi0 : lowOff i≤1792 := by unfold lowOff; omega
    refine ⟨ha.dataRead _ (by omega),ha.dataRead _ (by omega),ha.dataWrite _ (by omega),
      ha.dataWrite _ (by omega),haw _ (by omega),haw _ (by omega)⟩
  · refine ⟨u,⟨hum.trans hm,hu2',hu15,hu16⟩,hac,?_,?_,?_⟩
    · refine hkeep.mono ?_
      intro r hr
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,middleRegs,finalGprs,
        kernelRegs] at hr ⊢
      grind
    · simpa only [hu15,hu16] using htm
    · simpa only [hu15,hu16] using htv

end VG.Proof.MlDsa.AArch64.Optimized.Paired
