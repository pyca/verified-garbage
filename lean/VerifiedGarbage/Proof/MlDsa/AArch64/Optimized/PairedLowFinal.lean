import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowRun
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFinalCheck

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Proof.MlDsa.AArch64.Round

def allLow : List LowIndex := (List.finRange 2).flatMap fun p => (List.finRange 4).map fun j => (p,j)
def finalLowCode (g : Nat) : List Instr := finalLoads++finalArithmetic++lowRunCode g allLow

def finalLowData (g : Nat) (s : State) : CheckData :=
  lowRun g (rawPairAt s) (s.gpr .x15) (s.gpr .x16) (lowConstantsAt s) (dataAt s) allLow

theorem lowReady_arithmetic {g : Nat} {s t : State} (h : LowReady g s)
    (hf : VChg stageRunRegs s t) : LowReady g t :=
  h.frame ((StepFrame.ofChg hf).mono (by intro r hr; exact List.mem_append_left _ hr))

theorem lowConstantsAt_arithmetic {s t : State} (hf : VChg stageRunRegs s t) : lowConstantsAt t=lowConstantsAt s :=
  lowConstantsAt_frame ((StepFrame.ofChg hf).mono (by intro r hr; exact List.mem_append_left _ hr))

theorem finalLow_ok {g : Nat} (hg : IsG g) {s : State} {rest : List Instr} {Q : State → Prop}
    (hr : ∀p:Fin 2,∀j:Fin 8,InRegions (s.rd++s.wr)
      (s.gpr .x2+BitVec.ofNat 64 (1024*p.val+128*j.val)) 16)
    (ht : ∀i:Fin 7,RootReady s (32*i.val) (Inverse.finalZ i.val))
    (hs : RootReady s 224 (fun _ => 16382)) (hc : LowReady g s)
    (hw : ∀i:LowIndex,
      InRegions (s.rd++s.wr) (s.gpr .x15+BitVec.ofNat 64 (lowOff i)) 16 ∧
      InRegions (s.rd++s.wr) (s.gpr .x15+BitVec.ofNat 64 (lowOff i+128)) 16 ∧
      InRegions s.wr (s.gpr .x15+BitVec.ofNat 64 (lowOff i)) 16 ∧
      InRegions s.wr (s.gpr .x15+BitVec.ofNat 64 (lowOff i+128)) 16 ∧
      InRegions s.wr (s.gpr .x16+BitVec.ofNat 64 (lowOff i)) 16 ∧
      InRegions s.wr (s.gpr .x16+BitVec.ofNat 64 (lowOff i+128)) 16)
    (k : ∀t,StepFrame lowRunRegs s t → dataAt t=finalLowData g s →
      WP isa (.block rest) t Q) : WP isa (.block (finalLowCode g++rest)) s Q := by
  simp only [finalLowCode,List.append_assoc]
  refine finalLoadArithmetic_ok hr ht hs hc.q fun a ha va => ?_
  refine lowRun_ok hg allLow (by decide) (va.lowPending allLow) (lowReady_arithmetic hc ha) ?_ fun t hf hd => ?_
  · simpa only [ha.rd,ha.wr,ha.gpr] using hw
  · refine k t (((StepFrame.ofChg ha).trans hf).mono (by simp [lowRunRegs])) ?_
    unfold finalLowData rawPairAt
    simpa only [ha.gpr,lowConstantsAt_arithmetic ha,dataAt_arithmetic ha] using hd

end VG.Proof.MlDsa.AArch64.Optimized.Paired
