module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.CmsChainMath
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
public import VerifiedGarbage.Proof.Mont.AArch64.Words
import VerifiedGarbage.Proof.Framework.Block

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64

def cmsIn0 : Nat → Reg | 0 => .x8 | 1 => .x10 | _ => .x12
def cmsIn1 : Nat → Reg | 0 => .x9 | 1 => .x11 | _ => .x13
def cmsOut0 : Nat → Reg | 0 => .x5 | 1 => .x7 | _ => .x9
def cmsOut1 : Nat → Reg | 0 => .x6 | 1 => .x8 | _ => .x10
def cmsHigh : Nat → Reg | 0 => .x7 | 1 => .x9 | _ => .x11

def cmsPairCode (i : Nat) : List Instr := [
  .mul .x (cmsOut0 i) .x1 (cmsIn0 i),
  .mul .x (cmsOut1 i) .x1 (cmsIn1 i),
  .umulh (cmsIn0 i) .x1 (cmsIn0 i),
  .adcs .x (cmsOut0 i) (cmsOut0 i) (cmsHigh i),
  .umulh (cmsIn1 i) .x1 (cmsIn1 i),
  .adcs .x (cmsOut1 i) (cmsOut1 i) (cmsIn0 i)]

def cmsPairClob (i : Nat) : List Reg := [cmsOut0 i,cmsOut1 i,cmsIn0 i,cmsIn1 i]

theorem cms_pair_ok (s : State) (i : Nat) (hi : i<3) :
    WP isa (.block (cmsPairCode i)) s fun t =>
      t.gpr (cmsOut0 i)=addCarry (s.gpr .x1*s.gpr (cmsIn0 i)) (s.gpr (cmsHigh i)) s.c ∧
      t.gpr (cmsOut1 i)=addCarry (s.gpr .x1*s.gpr (cmsIn1 i)) (mulHi (s.gpr .x1) (s.gpr (cmsIn0 i)))
        (carryOut (s.gpr .x1*s.gpr (cmsIn0 i)) (s.gpr (cmsHigh i)) s.c) ∧
      t.gpr (cmsIn1 i)=mulHi (s.gpr .x1) (s.gpr (cmsIn1 i)) ∧
      t.c=carryOut (s.gpr .x1*s.gpr (cmsIn1 i)) (mulHi (s.gpr .x1) (s.gpr (cmsIn0 i)))
        (carryOut (s.gpr .x1*s.gpr (cmsIn0 i)) (s.gpr (cmsHigh i)) s.c) ∧ Keeps (cmsPairClob i) s t := by
  have hc : i=0 ∨ i=1 ∨ i=2 := by omega_arith
  rcases hc with rfl|rfl|rfl <;> apply WP.of_runBlock <;>
    simp only [cmsPairCode,cmsIn0,cmsIn1,cmsOut0,cmsOut1,cmsHigh,runBlock_cons,runStep_some,runBlock_nil,
      reduceExec,read_x,RegUpd.gpr_write,RegUpd.gpr_addWithCarry,RegUpd.c_write,RegUpd.c_addWithCarry,
      BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false,Option.some.injEq,exists_eq_left']
  all_goals
    refine ⟨by rfl,by rfl,True.intro,by rfl,⟨?_,?_,?_,?_,?_⟩⟩
    · dsimp only [cmsPairClob,cmsIn0,cmsIn1,cmsOut0,cmsOut1]
      reg_keeps
    · simp only [RegUpd.mem_write,RegUpd.mem_addWithCarry]
    · simp only [RegUpd.rd_write,RegUpd.rd_addWithCarry]
    · simp only [RegUpd.wr_write,RegUpd.wr_addWithCarry]
    · simp only [RegUpd.sp_write,RegUpd.sp_addWithCarry]

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64

theorem cms_pair_value (s : State) (i : Nat) (hi : i<3) :
    WP isa (.block (cmsPairCode i)) s fun t =>
      regsVal t [cmsOut0 i,cmsOut1 i]+2^128*((t.gpr (cmsIn1 i)).toNat+t.c.toNat)=
        (s.gpr (cmsHigh i)).toNat+s.c.toNat+
        (s.gpr .x1).toNat*((s.gpr (cmsIn0 i)).toNat+2^64*(s.gpr (cmsIn1 i)).toNat) ∧
      Keeps (cmsPairClob i) s t := by
  refine WP.mono (cms_pair_ok s i hi) fun t ⟨a0,a1,hh,cc,k⟩ => ?_
  refine ⟨?_,k⟩
  simp only [regsVal,Nat.mul_zero,Nat.add_zero,a0,a1,hh,cc,Nat.mul_add]
  rw [Nat.mul_left_comm (s.gpr .x1).toNat (2^64)]
  have m0 := mul_lo_hi (s.gpr .x1) (s.gpr (cmsIn0 i))
  have m1 := mul_lo_hi (s.gpr .x1) (s.gpr (cmsIn1 i))
  have e0 := addCarry_value (s.gpr .x1*s.gpr (cmsIn0 i)) (s.gpr (cmsHigh i)) s.c
  have e1 := addCarry_value (s.gpr .x1*s.gpr (cmsIn1 i)) (mulHi (s.gpr .x1) (s.gpr (cmsIn0 i)))
    (carryOut (s.gpr .x1*s.gpr (cmsIn0 i)) (s.gpr (cmsHigh i)) s.c)
  omega_using [m0,m1,e0,e1]

end VG.Proof.Mont.AArch64.P521Field
