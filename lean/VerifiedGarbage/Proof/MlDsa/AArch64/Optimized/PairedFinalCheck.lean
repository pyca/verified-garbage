import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedCheckRun

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)

def allChecks : List (Fin 2 × Fin 8) := (List.finRange 2).flatMap fun p => (List.finRange 8).map fun j => (p,j)
def finalCheckCode (hint : Bool) : List Instr := finalLoads++finalArithmetic++checkRunCode hint allChecks

def rawPairAt (s : State) : Values := fun p => Inverse.rawFinalValues (readPair s.mem (s.gpr .x2) 128 p)
def finalCheckData (hint : Bool) (s : State) : CheckData :=
  checkRun hint (rawPairAt s) (s.gpr .x15) (s.gpr .x16) (constantsAt s) (dataAt s) allChecks

def finalCheckRegs : List VReg := stageRunRegs++checkRegs

theorem checkReady_arithmetic {hint : Bool} {s t : State} (h : CheckReady hint s)
    (hf : VChg stageRunRegs s t) : CheckReady hint t := by
  refine ⟨?_,?_,?_,?_⟩
  · rw [hf.get .v31 (by decide)]; exact h.q
  · rw [hf.get .v8 (by decide)]; exact h.bias
  · rw [hf.get .v12 (by decide),hf.get .v11 (by decide)]; exact h.neg
  · rw [hf.get .v13 (by decide)]; exact h.zero

theorem constantsAt_arithmetic {s t : State} (hf : VChg stageRunRegs s t) : constantsAt t=constantsAt s := by
  unfold constantsAt
  rw [hf.get .v11 (by decide),hf.get .v9 (by decide),hf.get .v10 (by decide)]

theorem dataAt_arithmetic {s t : State} (hf : VChg stageRunRegs s t) : dataAt t=dataAt s := by
  unfold dataAt
  rw [hf.mem,hf.get .v30 (by decide),hf.get .v14 (by decide)]

theorem finalCheck_ok (hint : Bool) {s : State} {rest : List Instr} {Q : State → Prop}
    (hr : ∀p:Fin 2,∀j:Fin 8,InRegions (s.rd++s.wr)
      (s.gpr .x2+BitVec.ofNat 64 (1024*p.val+128*j.val)) 16)
    (ht : ∀i:Fin 7,RootReady s (32*i.val) (Inverse.finalZ i.val))
    (hs : RootReady s 224 (fun _ => 16382)) (hc : CheckReady hint s)
    (hw : ∀p:Fin 2,∀j:Fin 8,
      InRegions (s.rd++s.wr) (s.gpr .x15+BitVec.ofNat 64 (1024*p.val+128*j.val)) 16 ∧
      (hint=true → InRegions (s.rd++s.wr) (s.gpr .x16+BitVec.ofNat 64 (1024*p.val+128*j.val)) 16) ∧
      InRegions s.wr (s.gpr .x15+BitVec.ofNat 64 (1024*p.val+128*j.val)) 16)
    (k : ∀t,StepFrame finalCheckRegs s t → dataAt t=finalCheckData hint s →
      WP isa (.block rest) t Q) :
    WP isa (.block (finalCheckCode hint++rest)) s Q := by
  simp only [finalCheckCode,List.append_assoc]
  refine finalLoadArithmetic_ok hr ht hs hc.q fun a ha va => ?_
  refine checkRun_ok hint allChecks va (checkReady_arithmetic hc ha) ?_ fun t hct hd => ?_
  · simpa only [ha.rd,ha.wr,ha.gpr] using hw
  · refine k t ((StepFrame.ofChg ha).trans hct) ?_
    unfold finalCheckData rawPairAt
    simpa only [ha.gpr,constantsAt_arithmetic ha,dataAt_arithmetic ha] using hd

end VG.Proof.MlDsa.AArch64.Optimized.Paired
