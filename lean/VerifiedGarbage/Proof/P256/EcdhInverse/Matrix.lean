import VerifiedGarbage.Proof.Ed25519.AArch64.SqrRows
import VerifiedGarbage.Proof.P256.EcdhInverse.MachineExtract

/-! Fixed matrix multiplication blocks in the packed divstep batch. -/
namespace VG.Proof.P256.EcdhInverse.Matrix
open VG VG.AArch64 VG.Proof.Ed25519.AArch64

def first : List Instr :=
  [.mul .x .x2 .x12 .x8,.mul .x .x3 .x12 .x9,
   .mul .x .x6 .x14 .x8,.mul .x .x7 .x14 .x9,
   .madd .x .x8 .x13 .x10 .x2,.madd .x .x9 .x13 .x11 .x3,
   .madd .x .x16 .x15 .x10 .x6,.madd .x .x17 .x15 .x11 .x7]

theorem first_ok (s : State) : WP isa (.block first) s fun t =>
    t.gpr .x8=s.gpr .x12*s.gpr .x8+s.gpr .x13*s.gpr .x10 ∧
    t.gpr .x9=s.gpr .x12*s.gpr .x9+s.gpr .x13*s.gpr .x11 ∧
    t.gpr .x16=s.gpr .x14*s.gpr .x8+s.gpr .x15*s.gpr .x10 ∧
    t.gpr .x17=s.gpr .x14*s.gpr .x9+s.gpr .x15*s.gpr .x11 ∧
    t.nf=s.nf ∧ t.zf=s.zf ∧ t.c=s.c ∧ t.vf=s.vf ∧
    Keeps [.x2,.x3,.x6,.x7,.x8,.x9,.x16,.x17] s t := by
  apply WP.of_runBlock
  simp only [first,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,
    RegUpd.gpr_write,BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false,Option.some.injEq,exists_eq_left']
  refine ⟨True.intro,True.intro,True.intro,True.intro,rfl,rfl,rfl,rfl,?_,rfl,rfl,rfl,rfl⟩
  reg_keeps

def final : List Instr :=
  [.mul .x .x2 .x12 .x8,.sub .x .x2 .x27 .x2,
   .mul .x .x3 .x12 .x9,.sub .x .x3 .x27 .x3,
   .mul .x .x4 .x14 .x8,.sub .x .x4 .x27 .x4,
   .mul .x .x5 .x14 .x9,.sub .x .x5 .x27 .x5,
   .mul .x .x26 .x13 .x16,.sub .x .x10 .x2 .x26,
   .mul .x .x26 .x13 .x17,.sub .x .x11 .x3 .x26,
   .mul .x .x26 .x15 .x16,.sub .x .x12 .x4 .x26,
   .mul .x .x26 .x15 .x17,.sub .x .x13 .x5 .x26]

theorem final_ok (s : State) (h27 : s.gpr .x27=0) : WP isa (.block final) s fun t =>
    t.gpr .x10= -(s.gpr .x12*s.gpr .x8)-s.gpr .x13*s.gpr .x16 ∧
    t.gpr .x11= -(s.gpr .x12*s.gpr .x9)-s.gpr .x13*s.gpr .x17 ∧
    t.gpr .x12= -(s.gpr .x14*s.gpr .x8)-s.gpr .x15*s.gpr .x16 ∧
    t.gpr .x13= -(s.gpr .x14*s.gpr .x9)-s.gpr .x15*s.gpr .x17 ∧
    Keeps [.x2,.x3,.x4,.x5,.x10,.x11,.x12,.x13,.x26] s t := by
  apply WP.of_runBlock
  simp only [final,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,
    RegUpd.gpr_write,BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false,Option.some.injEq,exists_eq_left',h27,zero_sub]
  refine ⟨True.intro,True.intro,True.intro,True.intro,?_,rfl,rfl,rfl,rfl⟩
  reg_keeps

def moves : List Instr :=
  [.logic .orr .x .x4 .x10 .x10,.logic .orr .x .x5 .x11 .x11,
   .logic .orr .x .x6 .x12 .x12,.logic .orr .x .x7 .x13 .x13]

theorem moves_ok (s : State) : WP isa (.block moves) s fun t =>
    t.gpr .x4=s.gpr .x10 ∧ t.gpr .x5=s.gpr .x11 ∧
    t.gpr .x6=s.gpr .x12 ∧ t.gpr .x7=s.gpr .x13 ∧ Keeps [.x4,.x5,.x6,.x7] s t := by
  apply WP.of_runBlock
  simp only [moves,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,
    RegUpd.gpr_write,BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false,
    BitVec.or_self,Option.some.injEq,exists_eq_left']
  refine ⟨True.intro,True.intro,True.intro,True.intro,?_,rfl,rfl,rfl,rfl⟩
  reg_keeps
end VG.Proof.P256.EcdhInverse.Matrix
