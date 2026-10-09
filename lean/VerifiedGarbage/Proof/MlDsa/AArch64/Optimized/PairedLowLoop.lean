import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFinalLoop

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Round

theorem ready_lowFrame {g : Nat} {s t : State} (h : LowReady g s)
    (hf : CallFrame finalGprs lowRunRegs s t) : LowReady g t := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [hf.vec .v31 (by decide)]; exact h.q
  · rw [hf.vec .v8 (by decide)]; exact h.bias
  · rw [hf.vec .v11 (by decide)]; exact h.c11
  · rw [hf.vec .v12 (by decide)]; exact h.c12
  · rw [hf.vec .v13 (by decide)]; exact h.c13
  · rw [hf.vec .v14 (by decide)]; exact h.c14

theorem lowConstantsAt_callFrame {s t : State} (hf : CallFrame finalGprs lowRunRegs s t) :
    lowConstantsAt t=lowConstantsAt s := by
  unfold lowConstantsAt
  rw [hf.vec .v15 (by decide),hf.vec .v9 (by decide),hf.vec .v10 (by decide)]

theorem lowLoop_ok {g : Nat} (hg : IsG g) {s : State} {table : Addr}
    (ht : PairedTable.Words s.mem table)
    (hd : (⟨table,4096⟩:Region).Disjoint ⟨s.gpr .x15,2048⟩)
    (hda : (⟨table,4096⟩:Region).Disjoint ⟨s.gpr .x16,2048⟩)
    (hx : s.gpr .x1=table+BitVec.ofNat 64 3840)
    (hcount : s.gpr .x12=8) (hc : LowReady g s)
    (hrt : ∀off,off+16≤4096 → InRegions (s.rd++s.wr) (table+BitVec.ofNat 64 off) 16)
    (hr : ∀u<8,∀p:Fin 2,∀j:Fin 8,InRegions (s.rd++s.wr)
      ((s.gpr .x2+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (1024*p.val+128*j.val)) 16)
    (hw : ∀u<8,∀i:LowIndex,
      InRegions (s.rd++s.wr) ((s.gpr .x15+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (lowOff i)) 16 ∧
      InRegions (s.rd++s.wr) ((s.gpr .x15+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (lowOff i+128)) 16 ∧
      InRegions s.wr ((s.gpr .x15+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (lowOff i)) 16 ∧
      InRegions s.wr ((s.gpr .x15+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (lowOff i+128)) 16 ∧
      InRegions s.wr ((s.gpr .x16+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (lowOff i)) 16 ∧
      InRegions s.wr ((s.gpr .x16+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (lowOff i+128)) 16) :
    WP isa (.loop (.block (finalLowCode g++finalAdvance)) (.nonzero .x .x12)) s fun t =>
      CallFrame finalGprs lowRunRegs s t ∧
      t.gpr .x2=s.gpr .x2+128 ∧ t.gpr .x15=s.gpr .x15+128 ∧ t.gpr .x16=s.gpr .x16+128 ∧
      dataAt t=lowPassData g (s.gpr .x2) (s.gpr .x15) (s.gpr .x16) (lowConstantsAt s) (dataAt s) 8 := by
  let I := fun u t => CallFrame finalGprs lowRunRegs s t ∧
    t.gpr .x2=s.gpr .x2+BitVec.ofNat 64 (16*u) ∧
    t.gpr .x15=s.gpr .x15+BitVec.ofNat 64 (16*u) ∧
    t.gpr .x16=s.gpr .x16+BitVec.ofNat 64 (16*u) ∧
    dataAt t=lowPassData g (s.gpr .x2) (s.gpr .x15) (s.gpr .x16) (lowConstantsAt s) (dataAt s) u
  apply VG.Proof.MlDsa.AArch64.Arith.wp_countdown (N:=8) (by decide) (by decide) I ?_ ?_ hcount
  · intro u hu t hi _
    rcases hi with ⟨hf,h2,h15,h16,hdata⟩
    have hm := congrArg CheckData.mem hdata
    have fm : Frame [⟨s.gpr .x15,2048⟩,⟨s.gpr .x16,2048⟩] s.mem t.mem := by
      change Frame _ _ (dataAt t).mem
      rw [hdata]; exact lowPass_frame _ _ _ _ _ _ (by omega)
    have ht' := tableWords_frame ht fm (by intro r hr; rcases List.mem_cons.mp hr with rfl | hr; exact hd; have he := List.mem_singleton.mp hr; subst r; exact hda)
    have rt : ∀off,off+16≤4096 → InRegions (t.rd++t.wr) (table+BitVec.ofNat 64 off) 16 := by
      simpa only [hf.rd,hf.wr] using hrt
    have hx' : t.gpr .x1=table+BitVec.ofNat 64 3840 := by rw [hf.gpr .x1 (by decide),hx]
    refine finalLow_ok hg ?_ (final_tableReady ht' rt hx') (scale_tableReady ht' rt hx')
      (ready_lowFrame hc hf) ?_ fun a ha had => ?_
    · simpa only [hf.rd,hf.wr,h2] using hr u hu
    · simpa only [hf.rd,hf.wr,h15,h16] using hw u hu
    · refine WP.mono (finalAdvance_ok a) fun b ⟨⟨⟨hb2,hb15,hb16,hb12,hbm⟩,hbk⟩,hbv⟩ => ?_
      have hab := (CallFrame.ofStep ha).trans (CallFrame.ofKeep hbk hbv)
      have hsb : CallFrame finalGprs lowRunRegs s b := (hf.trans hab).mono (by simp [finalGprs]) (by simp)
      refine ⟨⟨hsb,?_,?_,?_,?_⟩,?_⟩
      · rw [hb2,ha.gpr,h2,show 16*(u+1)=16*u+16 by omega,BitVec.ofNat_add,BitVec.add_assoc]; rfl
      · rw [hb15,ha.gpr,h15,show 16*(u+1)=16*u+16 by omega,BitVec.ofNat_add,BitVec.add_assoc]; rfl
      · rw [hb16,ha.gpr,h16,show 16*(u+1)=16*u+16 by omega,BitVec.ofNat_add,BitVec.add_assoc]; rfl
      · have hba : dataAt b=dataAt a := by unfold dataAt; rw [hbm,hbv]
        rw [hba,had]
        unfold finalLowData rawPairAt
        rw [h2,h15,h16,lowConstantsAt_callFrame hf,hdata]
        simp only [lowPassData]
        exact congrArg (fun mm => lowRun g (fun p => Inverse.rawFinalValues (readPair mm
          (s.gpr .x2+BitVec.ofNat 64 (16*u)) 128 p)) _ _ _ _ allLow) hm
      · rw [hb12,ha.gpr]; rfl
  · exact ⟨⟨fun _ _ => rfl,rfl,rfl,rfl,fun _ _ => rfl⟩,by simp,by simp,by simp,rfl⟩

end VG.Proof.MlDsa.AArch64.Optimized.Paired
