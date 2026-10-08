import VerifiedGarbage.Proof.P256.Linear.WeakWords
import VerifiedGarbage.Proof.Mont.AArch64.Ops
import VerifiedGarbage.Proof.Ed25519.AArch64.SqrRows

namespace VG.Proof.P256.Linear.Weak
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64

def regs (s : State) : W4 := (s.gpr .x5,s.gpr .x6,s.gpr .x7,s.gpr .x8)
def addCode : List Instr :=
  [.adds .x .x5 .x5 .x9,.adcs .x .x6 .x6 .x10,.adcs .x .x7 .x7 .x11,.adcs .x .x8 .x8 .x12]

theorem addCode_ok (s : State) : WP isa (.block addCode) s fun t =>
    regs t=(addWords (regs s) (s.gpr .x9,s.gpr .x10,s.gpr .x11,s.gpr .x12)).1 ∧
    t.c=(addWords (regs s) (s.gpr .x9,s.gpr .x10,s.gpr .x11,s.gpr .x12)).2 ∧ Keeps [.x5,.x6,.x7,.x8] s t := by
  apply WP.of_runBlock
  simp only [regs,addCode,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,Size.bits,
    RegUpd.gpr_addWithCarry,RegUpd.c_addWithCarry,BitVec.setWidth_eq,
    ite_false,reduceCtorEq,Option.some.injEq,exists_eq_left']
  refine ⟨rfl,rfl,?_,rfl,rfl,rfl,rfl⟩
  reg_keeps

def reduceCode : List Instr :=
  [.movz .x .x17 0 0,.movz .x .x16 1 0,.sub .x .x13 .x17 .x16,
   .csel .x .x3 .x13 .x17,.subs .x .x5 .x5 .x3,
   .lsl .x .x1 .x3 32,.lsr .x .x1 .x1 32,.sbcs .x .x6 .x6 .x1,
   .sbcs .x .x7 .x7 .x17,.lsl .x .x2 .x3 32,.sub .x .x2 .x2 .x3,
   .sbc .x .x8 .x8 .x2]

theorem reduceCode_ok (s : State) : WP isa (.block reduceCode) s fun t =>
    regs t=weakWords (regs s) s.c ∧ Keeps [.x1,.x2,.x3,.x5,.x6,.x7,.x8,.x13,.x16,.x17] s t := by
  apply WP.of_runBlock
  cases hc : s.c <;>
    simp only [regs,reduceCode,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,Size.bits,
      RegUpd.gpr_write,RegUpd.c_write,RegUpd.gpr_addWithCarry,RegUpd.c_addWithCarry,
      BitVec.setWidth_eq,show 16*0<64 by decide,show 32<64 by decide,
      ite_true,ite_false,reduceCtorEq,hc,Option.some.injEq,exists_eq_left']
  all_goals
    refine ⟨?_,?_,rfl,rfl,rfl,rfl⟩
    · simp only [weakWords,subWords,modulusWords,addCarry,carryOut]
      rfl
    · reg_keeps
end VG.Proof.P256.Linear.Weak
