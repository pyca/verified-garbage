import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedCheckModel

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
