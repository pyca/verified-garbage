import VerifiedGarbage.Proof.P256.Linear.FortyOneValue
import VerifiedGarbage.Proof.P256.Linear.WeakCore

namespace VG.Proof.P256.Linear.FortyOne
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64
open Weak (W4 value addWords subWords)

def input (s : State) : W4 := (s.gpr .x1,s.gpr .x2,s.gpr .x3,s.gpr .x4)
def other (s : State) : W4 := (s.gpr .x9,s.gpr .x10,s.gpr .x11,s.gpr .x12)
def output (s : State) : W4 := (s.gpr .x14,s.gpr .x1,s.gpr .x2,s.gpr .x3)

def prefixCode : List Instr :=
  [.movz .x .x17 0 0,.lsl .x .x14 .x1 2,.subs .x .x14 .x14 .x9,
   .extr .x .x1 .x2 .x1 62,.sbcs .x .x1 .x1 .x10,
   .extr .x .x2 .x3 .x2 62,.sbcs .x .x2 .x2 .x11,
   .extr .x .x3 .x4 .x3 62,.sbcs .x .x3 .x3 .x12,
   .lsr .x .x4 .x4 62,.sbc .x .x4 .x4 .x17]

theorem prefix_ok (s : State) : WP isa (.block prefixCode) s fun t =>
    output t=(subWords (shift2 (input s)).1 (other s)).1 ∧
    t.gpr .x4=highWord (shift2 (input s)).2 (subWords (shift2 (input s)).1 (other s)).2 ∧
    t.gpr .x17=0 ∧ Keeps [.x1,.x2,.x3,.x4,.x14,.x17] s t := by
  apply WP.of_runBlock
  simp only [prefixCode,input,other,output,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,Size.bits,
    RegUpd.gpr_write,RegUpd.c_write,RegUpd.gpr_addWithCarry,RegUpd.c_addWithCarry,
    BitVec.setWidth_eq,show 16*0<64 by decide,show 2<64 by decide,show 62<64 by decide,
    ite_true,ite_false,reduceCtorEq,Option.some.injEq,exists_eq_left']
  refine ⟨rfl,rfl,rfl,?_,rfl,rfl,rfl,rfl⟩
  reg_keeps

def reduce : List Instr :=
  [.movz .x .x16 1 0,.add .x .x5 .x4 .x16,.lsl .x .x8 .x5 32,
   .subs .x .x6 .x17 .x8,.sbcs .x .x7 .x17 .x17,.sbc .x .x8 .x8 .x5,
   .adds .x .x14 .x14 .x5,.adcs .x .x1 .x1 .x6,.adcs .x .x2 .x2 .x7,.adcs .x .x3 .x3 .x8]

theorem reduce_ok (s : State) (hz : s.gpr .x17=0) : WP isa (.block reduce) s fun t =>
    output t=(addWords (output s) (correction (s.gpr .x4+1))).1 ∧
    t.c=(addWords (output s) (correction (s.gpr .x4+1))).2 ∧
    Keeps [.x1,.x2,.x3,.x5,.x6,.x7,.x8,.x14,.x16] s t := by
  apply WP.of_runBlock
  simp only [reduce,output,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,Size.bits,
    RegUpd.gpr_write,RegUpd.gpr_addWithCarry,RegUpd.c_addWithCarry,
    BitVec.setWidth_eq,show 16*0<64 by decide,show 32<64 by decide,hz,
    ite_true,ite_false,reduceCtorEq,Option.some.injEq,exists_eq_left']
  refine ⟨rfl,rfl,?_,rfl,rfl,rfl,rfl⟩
  reg_keeps

def back : List Instr :=
  [.sbc .x .x5 .x17 .x17,.adds .x .x14 .x14 .x5,
   .lsl .x .x6 .x5 32,.lsr .x .x6 .x6 32,.adcs .x .x1 .x1 .x6,
   .adcs .x .x2 .x2 .x17,.sub .x .x7 .x17 .x6,.adc .x .x3 .x3 .x7]

theorem back_ok (s : State) (hz : s.gpr .x17=0) : WP isa (.block back) s fun t =>
    output t=addBack (output s) s.c ∧ Keeps [.x1,.x2,.x3,.x5,.x6,.x7,.x14] s t := by
  apply WP.of_runBlock
  cases hc : s.c <;>
    simp only [back,output,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,Size.bits,
      RegUpd.gpr_write,RegUpd.c_write,RegUpd.gpr_addWithCarry,RegUpd.c_addWithCarry,
      BitVec.setWidth_eq,show 32<64 by decide,hz,hc,
      ite_true,ite_false,reduceCtorEq,Option.some.injEq,exists_eq_left']
  all_goals
    refine ⟨?_,?_,rfl,rfl,rfl,rfl⟩
    · simp only [addBack,addWords,Weak.modulusWords,addCarry,carryOut]
      rfl
    · reg_keeps
end VG.Proof.P256.Linear.FortyOne
