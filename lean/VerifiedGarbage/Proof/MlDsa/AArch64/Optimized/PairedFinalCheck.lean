module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedCheckModel
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedPartition

import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Optimized/PairedCheckStep.lean`, which only this module imported.
section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Optimized.Response (laneVector laneVector_word)

def checkRegs : List VReg := [.v14,.v24,.v25,.v26,.v27,.v28,.v30]
def checkCode (hint : Bool) (raw : VReg) (off : Nat) : List Instr :=
  if hint then hintLane raw off else zLane raw off

theorem checkData_ext {a b : CheckData} (hm : a.mem=b.mem) (hf : a.flags=b.flags) (hc : a.count=b.count) : a=b := by
  cases a; cases b; cases hm; cases hf; cases hc; rfl

theorem checkStep_ok (hint : Bool) (raw : VReg) (hne : raw≠.v27)
    {s : State} {off : Nat} (ho : off%16=0 ∧ off<65536)
    (hl : InRegions (s.rd++s.wr) (s.gpr .x15+BitVec.ofNat 64 off) 16)
    (hh : hint=true → InRegions (s.rd++s.wr) (s.gpr .x16+BitVec.ofNat 64 off) 16)
    (hw : InRegions s.wr (s.gpr .x15+BitVec.ofNat 64 off) 16)
    (hq : ∀e<4,vword (s.v .v31) e=8380417#32)
    (hc : ∀e<4,vword (s.v .v8) e=4194304#32)
    (hn : hint=true → ∀e<4,vword (s.v .v12) e= -vword (s.v .v11) e)
    (hz : hint=true → ∀e<4,vword (s.v .v13) e=0)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀t,StepFrame checkRegs s t → dataAt t=checkStep hint (s.v raw)
      (s.gpr .x15+BitVec.ofNat 64 off) (s.gpr .x16+BitVec.ofNat 64 off) (constantsAt s) (dataAt s) →
      WP isa (.block rest) t Q) : WP isa (.block (checkCode hint raw off++rest)) s Q := by
  cases hint with
  | false =>
    refine zLane_ok raw hne ho hl hw hq hc fun t ht hm hf => k t ((StepFrame.ofKeep ht).mono (by decide)) ?_
    apply checkData_ext
    · exact hm
    · apply vec_ext
      intro e he
      simpa only [checkStep,dataAt,constantsAt,Bool.false_eq_true,ite_false,laneVector_word _ he,zInput] using hf e he
    · exact ht.vec .v14 (by decide)
  | true =>
    refine hintLane_ok raw ho hl (hh rfl) hw hq hc (hn rfl) (hz rfl) fun t ht hm hcount hf => k t (ht.mono (by decide)) ?_
    apply checkData_ext
    · exact hm
    · apply vec_ext
      intro e he
      simpa only [checkStep,dataAt,constantsAt,ite_true,laneVector_word _ he] using hf e he
    · apply vec_ext
      intro e he
      simpa only [checkStep,dataAt,constantsAt,ite_true,laneVector_word _ he,hintOutput] using hcount e he

end VG.Proof.MlDsa.AArch64.Optimized.Paired
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Optimized/PairedCheckRun.lean`, which only this module imported.
section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

structure CheckReady (hint : Bool) (s : State) : Prop where
  q : ∀e<4,vword (s.v .v31) e=8380417#32
  bias : ∀e<4,vword (s.v .v8) e=4194304#32
  neg : hint=true → ∀e<4,vword (s.v .v12) e= -vword (s.v .v11) e
  zero : hint=true → ∀e<4,vword (s.v .v13) e=0

theorem CheckReady.frame {hint : Bool} {s t : State} (h : CheckReady hint s)
    (hf : StepFrame checkRegs s t) : CheckReady hint t := by
  refine ⟨?_,?_,?_,?_⟩
  · rw [hf.vec .v31 (by decide)]; exact h.q
  · rw [hf.vec .v8 (by decide)]; exact h.bias
  · rw [hf.vec .v12 (by decide),hf.vec .v11 (by decide)]; exact h.neg
  · rw [hf.vec .v13 (by decide)]; exact h.zero

theorem constantsAt_frame {s t : State} (hf : StepFrame checkRegs s t) : constantsAt t=constantsAt s := by
  unfold constantsAt
  rw [hf.vec .v11 (by decide),hf.vec .v9 (by decide),hf.vec .v10 (by decide)]

theorem Banks.checkFrame {s t : State} {v : Values} (h : Banks s v) (hf : StepFrame checkRegs s t) : Banks t v := by
  intro p j
  rw [hf.vec _ ((show ∀p:Fin 2,∀j:Fin 8,(bankRegs p)[j.val]∉checkRegs by decide) p j)]
  exact h p j

def checkRunCode (hint : Bool) (js : List (Fin 2 × Fin 8)) : List Instr :=
  js.flatMap fun (p,j) => checkCode hint (bankRegs p)[j.val] (1024*p.val+128*j.val)

theorem checkRun_ok (hint : Bool) (js : List (Fin 2 × Fin 8))
    {s : State} {rest : List Instr} {Q : State → Prop} {v : Values}
    (hv : Banks s v) (hc : CheckReady hint s)
    (hr : ∀p:Fin 2,∀j:Fin 8,
      InRegions (s.rd++s.wr) (s.gpr .x15+BitVec.ofNat 64 (1024*p.val+128*j.val)) 16 ∧
      (hint=true → InRegions (s.rd++s.wr) (s.gpr .x16+BitVec.ofNat 64 (1024*p.val+128*j.val)) 16) ∧
      InRegions s.wr (s.gpr .x15+BitVec.ofNat 64 (1024*p.val+128*j.val)) 16)
    (k : ∀t,StepFrame checkRegs s t →
      dataAt t=checkRun hint v (s.gpr .x15) (s.gpr .x16) (constantsAt s) (dataAt s) js →
      WP isa (.block rest) t Q) :
    WP isa (.block (checkRunCode hint js++rest)) s Q := by
  induction js generalizing s with
  | nil => exact k s ⟨rfl,rfl,rfl,rfl,fun _ _ => rfl⟩ rfl
  | cons op js ih =>
    simp only [checkRunCode,List.flatMap_cons,List.append_assoc]
    have hn : (bankRegs op.1)[op.2.val]≠.v27 :=
      (show ∀p:Fin 2,∀j:Fin 8,(bankRegs p)[j.val]≠.v27 by decide) op.1 op.2
    refine checkStep_ok hint _ hn (by constructor <;> omega)
      (hr op.1 op.2).1 (hr op.1 op.2).2.1 (hr op.1 op.2).2.2
      hc.q hc.bias hc.neg hc.zero fun a ha hda => ?_
    refine ih (hv.checkFrame ha) (hc.frame ha) ?_ fun t ht hdt => ?_
    · simpa only [ha.rd,ha.wr,ha.gpr] using hr
    · refine k t ((ha.trans ht).mono (by simp)) ?_
      rw [hdt,ha.gpr,constantsAt_frame ha,hda,hv op.1 op.2]
      rfl

end VG.Proof.MlDsa.AArch64.Optimized.Paired
end

end

@[expose] public section

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
