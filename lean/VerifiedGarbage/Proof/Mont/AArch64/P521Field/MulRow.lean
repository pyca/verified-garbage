module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.MulFirst
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.RowMath
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-! Each product row runs a low-word carry chain and a high-word chain. -/

-- separate module: isolates short instruction proofs from integer row arithmetic
@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Impl.Mont.AArch64
open VG.Impl.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.Word64
open VG.Proof.Ed25519.AArch64
open VG.Proof.Mont.AArch64.P521Square (value addWords)

def row1In : List Reg := [.x16,.x17,.x19,.x20,.x21,.x22,.x23,.x24,.x25]
def row1High : List Reg := [.x17,.x19,.x20,.x21,.x22,.x23,.x24,.x25,.x26]

def row1LowCode : List Instr := [
  .mul .x .x14 .x4 .x5,
  .adds .x .x16 .x16 .x14,
  .mul .x .x14 .x4 .x6,
  .adcs .x .x17 .x17 .x14,
  .mul .x .x14 .x4 .x7,
  .adcs .x .x19 .x19 .x14,
  .mul .x .x14 .x4 .x8,
  .adcs .x .x20 .x20 .x14,
  .mul .x .x14 .x4 .x9,
  .adcs .x .x21 .x21 .x14,
  .mul .x .x14 .x4 .x10,
  .adcs .x .x22 .x22 .x14,
  .mul .x .x14 .x4 .x11,
  .adcs .x .x23 .x23 .x14,
  .mul .x .x14 .x4 .x12,
  .adcs .x .x24 .x24 .x14,
  .mul .x .x14 .x4 .x13,
  .adcs .x .x25 .x25 .x14,
  .movz .x .x26 1 0,
  .cselc .x .x26 .x26 .x2 .hs]

def row1HighCode : List Instr := [
  .umulh .x14 .x4 .x5,
  .adds .x .x17 .x17 .x14,
  .umulh .x14 .x4 .x6,
  .adcs .x .x19 .x19 .x14,
  .umulh .x14 .x4 .x7,
  .adcs .x .x20 .x20 .x14,
  .umulh .x14 .x4 .x8,
  .adcs .x .x21 .x21 .x14,
  .umulh .x14 .x4 .x9,
  .adcs .x .x22 .x22 .x14,
  .umulh .x14 .x4 .x10,
  .adcs .x .x23 .x23 .x14,
  .umulh .x14 .x4 .x11,
  .adcs .x .x24 .x24 .x14,
  .umulh .x14 .x4 .x12,
  .adcs .x .x25 .x25 .x14,
  .umulh .x14 .x4 .x13,
  .adc .x .x26 .x26 .x14]

theorem row1_eq : (mulFnBlocks.flatten.drop 55).take 38 = row1LowCode++row1HighCode := by decide

theorem carry_select (c : Bool) :
    (if c then (BitVec.setWidth 64 (1 : BitVec 16) <<< 0) else (0 : Word)) =
      BitVec.ofNat 64 c.toNat := by cases c <;> rfl

theorem row1_low_words (s : State) (hz : s.gpr .x2=0) :
    WP isa (.block row1LowCode) s fun t =>
      row1In.map t.gpr = (addWords (row1In.map s.gpr) (bRegs.map (s.gpr .x4 * s.gpr ·)) false).1 ∧
      t.gpr .x26 = BitVec.ofNat 64 (addWords (row1In.map s.gpr) (bRegs.map (s.gpr .x4 * s.gpr ·)) false).2.toNat ∧
      Keeps (.x14::.x26::row1In) s t := by
  apply WP.of_runBlock
  simp only [row1LowCode,runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,Size.bits,
    CondCode.holds,RegUpd.gpr_write,RegUpd.gpr_addWithCarry,RegUpd.c_addWithCarry,RegUpd.c_write,
    BitVec.setWidth_eq,ite_true,ite_false,reduceCtorEq,Nat.reduceMul,Nat.reduceLT,Option.some.injEq,exists_eq_left']
  refine ⟨?_,?_,⟨?_,by simp only [RegUpd.mem_write,RegUpd.mem_addWithCarry],
    by simp only [RegUpd.rd_write,RegUpd.rd_addWithCarry],
    by simp only [RegUpd.wr_write,RegUpd.wr_addWithCarry],
    by simp only [RegUpd.sp_write,RegUpd.sp_addWithCarry]⟩⟩
  · simp only [row1In,bRegs,List.map_cons,List.map_nil,addWords,
      RegUpd.gpr_write,RegUpd.gpr_addWithCarry,BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false]
    rfl
  · simp only [row1In,bRegs,List.map_cons,List.map_nil,addWords,hz]
    exact carry_select _
  · dsimp only [row1In]
    reg_keeps

theorem row1_high_words (s : State) :
    WP isa (.block row1HighCode) s fun t =>
      row1High.map t.gpr = (addWords (row1High.map s.gpr) (bRegs.map (mulHi (s.gpr .x4) ∘ s.gpr)) false).1 ∧
      Keeps (.x14::row1High) s t := by
  apply WP.of_runBlock
  simp only [row1HighCode,runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,Size.bits,
    RegUpd.gpr_write,RegUpd.gpr_addWithCarry,RegUpd.c_addWithCarry,RegUpd.c_write,
    BitVec.setWidth_eq,ite_true,ite_false,reduceCtorEq,Option.some.injEq,exists_eq_left']
  refine ⟨?_,⟨?_,by simp only [RegUpd.mem_write,RegUpd.mem_addWithCarry],
    by simp only [RegUpd.rd_write,RegUpd.rd_addWithCarry],
    by simp only [RegUpd.wr_write,RegUpd.wr_addWithCarry],
    by simp only [RegUpd.sp_write,RegUpd.sp_addWithCarry]⟩⟩
  · simp only [row1High,bRegs,List.map_cons,List.map_nil,addWords,Function.comp_apply,
      RegUpd.gpr_write,RegUpd.gpr_addWithCarry,BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false]
    rfl
  · dsimp only [row1High]
    reg_keeps

def row1Out : List Reg := .x16::row1High

theorem row1_words (s : State) (hz : s.gpr .x2=0) :
    WP isa (.block (row1LowCode++row1HighCode)) s fun t =>
      row1Out.map t.gpr = (rowCarry (s.gpr .x4) (row1In.map s.gpr) (bRegs.map s.gpr)).1 ∧
      Keeps (.x14::row1Out) s t := by
  rw [WP.block_append_iff]
  refine WP.mono (row1_low_words s hz) fun u ⟨lo,carry,klo⟩ => ?_
  refine WP.mono (row1_high_words u) fun t ⟨hi,khi⟩ => ?_
  have a : u.gpr .x4=s.gpr .x4 := klo.gpr _ (by decide)
  have bs : bRegs.map u.gpr=bRegs.map s.gpr := List.map_congr_left fun r hr =>
    klo.gpr r ((show ∀r∈bRegs,r∉(.x14::.x26::row1In) from by decide) r hr)
  have hiIn : row1High.map u.gpr =
      (addWords (row1In.map s.gpr) (bRegs.map (s.gpr .x4 * s.gpr ·)) false).1.tail ++
        [BitVec.ofNat 64 (addWords (row1In.map s.gpr) (bRegs.map (s.gpr .x4 * s.gpr ·)) false).2.toNat] := by
    have hr : row1High=row1In.tail++[.x26] := rfl
    rw [hr,List.map_append,List.map_tail,lo]
    simp only [List.map_cons,List.map_nil,carry]
  have head := congrArg (fun xs : List Word => xs.headD 0) lo
  change u.gpr .x16=_ at head
  have hh : t.gpr .x16=u.gpr .x16 := khi.gpr _ (by decide)
  have hi' : row1High.map t.gpr =
      (addWords ((addWords (row1In.map s.gpr) (bRegs.map (s.gpr .x4 * s.gpr ·)) false).1.tail ++
        [BitVec.ofNat 64 (addWords (row1In.map s.gpr) (bRegs.map (s.gpr .x4 * s.gpr ·)) false).2.toNat])
        ((bRegs.map s.gpr).map (mulHi (s.gpr .x4))) false).1 := by
    rw [hi,hiIn,a,←List.map_map,bs]
  refine ⟨?_,(klo.mono (by decide)).trans (khi.mono (by decide))⟩
  simp only [row1Out,List.map_cons,hh,head,hi',rowCarry,List.map_map,Function.comp_def]

theorem row1_value (s : State) (hz : s.gpr .x2=0) :
    WP isa (.block (row1LowCode++row1HighCode)) s fun t =>
      regsVal t row1Out = regsVal s row1In + (s.gpr .x4).toNat*regsVal s bRegs ∧
      Keeps (.x14::row1Out) s t := by
  refine WP.mono (row1_words s hz) fun t ⟨h,k⟩ => ?_
  have e := congrArg value h
  rw [value_map_gpr,row_value _ _ _ (by simp only [List.length_map]; decide)
    (by simp only [List.length_map]; decide),value_map_gpr,value_map_gpr] at e
  exact ⟨e,k⟩

end VG.Proof.Mont.AArch64.P521Field
