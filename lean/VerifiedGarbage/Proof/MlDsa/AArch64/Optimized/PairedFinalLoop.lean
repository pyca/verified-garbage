import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFinalMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFinalRoots
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFirstLoop

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

def finalGprs : List Reg := [.x2,.x12,.x15,.x16]

theorem ready_finalFrame {hint : Bool} {s t : State} (h : CheckReady hint s)
    (hf : CallFrame finalGprs finalCheckRegs s t) : CheckReady hint t := by
  refine ⟨?_,?_,?_,?_⟩
  · rw [hf.vec .v31 (by decide)]; exact h.q
  · rw [hf.vec .v8 (by decide)]; exact h.bias
  · rw [hf.vec .v12 (by decide),hf.vec .v11 (by decide)]; exact h.neg
  · rw [hf.vec .v13 (by decide)]; exact h.zero

theorem constantsAt_finalFrame {s t : State} (hf : CallFrame finalGprs finalCheckRegs s t) :
    constantsAt t=constantsAt s := by
  unfold constantsAt
  rw [hf.vec .v11 (by decide),hf.vec .v9 (by decide),hf.vec .v10 (by decide)]

theorem finalLoop_ok (hint : Bool) {s : State} {table : Addr}
    (ht : PairedTable.Words s.mem table)
    (hd : (⟨table,4096⟩:Region).Disjoint ⟨s.gpr .x15,2048⟩)
    (hx : s.gpr .x1=table+BitVec.ofNat 64 3840)
    (hcount : s.gpr .x12=8) (hc : CheckReady hint s)
    (hrt : ∀off,off+16≤4096 → InRegions (s.rd++s.wr) (table+BitVec.ofNat 64 off) 16)
    (hr : ∀u<8,∀p:Fin 2,∀j:Fin 8,InRegions (s.rd++s.wr)
      ((s.gpr .x2+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (1024*p.val+128*j.val)) 16)
    (hw : ∀u<8,∀p:Fin 2,∀j:Fin 8,
      InRegions (s.rd++s.wr) ((s.gpr .x15+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (1024*p.val+128*j.val)) 16 ∧
      (hint=true → InRegions (s.rd++s.wr) ((s.gpr .x16+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (1024*p.val+128*j.val)) 16) ∧
      InRegions s.wr ((s.gpr .x15+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (1024*p.val+128*j.val)) 16) :
    WP isa (.loop (.block (finalCheckCode hint++finalAdvance)) (.nonzero .x .x12)) s fun t =>
      CallFrame finalGprs finalCheckRegs s t ∧
      t.gpr .x2=s.gpr .x2+128 ∧ t.gpr .x15=s.gpr .x15+128 ∧ t.gpr .x16=s.gpr .x16+128 ∧
      dataAt t=finalPassData hint (s.gpr .x2) (s.gpr .x15) (s.gpr .x16) (constantsAt s) (dataAt s) 8 := by
  let I := fun u t => CallFrame finalGprs finalCheckRegs s t ∧
    t.gpr .x2=s.gpr .x2+BitVec.ofNat 64 (16*u) ∧
    t.gpr .x15=s.gpr .x15+BitVec.ofNat 64 (16*u) ∧
    t.gpr .x16=s.gpr .x16+BitVec.ofNat 64 (16*u) ∧
    dataAt t=finalPassData hint (s.gpr .x2) (s.gpr .x15) (s.gpr .x16) (constantsAt s) (dataAt s) u
  apply VG.Proof.MlDsa.AArch64.Arith.wp_countdown (N:=8) (by decide) (by decide) I ?_ ?_ hcount
  · intro u hu t hi _
    rcases hi with ⟨hf,h2,h15,h16,hdata⟩
    have hm := congrArg CheckData.mem hdata
    have fm : Frame [⟨s.gpr .x15,2048⟩] s.mem t.mem := by
      change Frame _ _ (dataAt t).mem
      rw [hdata]; exact finalPass_frame _ _ _ _ _ _ (by omega)
    have ht' := tableWords_frame ht fm (by simpa only [List.mem_singleton,forall_eq] using hd)
    have rt : ∀off,off+16≤4096 → InRegions (t.rd++t.wr) (table+BitVec.ofNat 64 off) 16 := by
      simpa only [hf.rd,hf.wr] using hrt
    have hx' : t.gpr .x1=table+BitVec.ofNat 64 3840 := by rw [hf.gpr .x1 (by decide),hx]
    refine finalCheck_ok hint ?_ (final_tableReady ht' rt hx') (scale_tableReady ht' rt hx')
      (ready_finalFrame hc hf) ?_ fun a ha had => ?_
    · simpa only [hf.rd,hf.wr,h2] using hr u hu
    · simpa only [hf.rd,hf.wr,h15,h16] using hw u hu
    · refine WP.mono (finalAdvance_ok a) fun b ⟨⟨⟨hb2,hb15,hb16,hb12,hbm⟩,hbk⟩,hbv⟩ => ?_
      have hab := (CallFrame.ofStep ha).trans (CallFrame.ofKeep hbk hbv)
      have hsb : CallFrame finalGprs finalCheckRegs s b := (hf.trans hab).mono (by simp [finalGprs]) (by simp)
      refine ⟨⟨hsb,?_,?_,?_,?_⟩,?_⟩
      · rw [hb2,ha.gpr,h2,show 16*(u+1)=16*u+16 by omega,BitVec.ofNat_add,BitVec.add_assoc]; rfl
      · rw [hb15,ha.gpr,h15,show 16*(u+1)=16*u+16 by omega,BitVec.ofNat_add,BitVec.add_assoc]; rfl
      · rw [hb16,ha.gpr,h16,show 16*(u+1)=16*u+16 by omega,BitVec.ofNat_add,BitVec.add_assoc]; rfl
      · have hba : dataAt b=dataAt a := by unfold dataAt; rw [hbm,hbv]
        rw [hba,had]
        unfold finalCheckData rawPairAt
        rw [h2,h15,h16,constantsAt_finalFrame hf,hdata]
        simp only [finalPassData]
        exact congrArg (fun mm => checkRun hint (fun p => Inverse.rawFinalValues (readPair mm
          (s.gpr .x2+BitVec.ofNat 64 (16*u)) 128 p)) _ _ _ _ allChecks) hm
      · rw [hb12,ha.gpr]; rfl
  · exact ⟨⟨fun _ _ => rfl,rfl,rfl,rfl,fun _ _ => rfl⟩,by simp,by simp,by simp,rfl⟩

end VG.Proof.MlDsa.AArch64.Optimized.Paired
