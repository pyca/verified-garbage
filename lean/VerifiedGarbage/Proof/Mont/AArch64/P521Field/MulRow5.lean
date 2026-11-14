module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.MulRow
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

def row5In : List Reg := [.x21,.x22,.x23,.x24,.x25,.x26,.x15,.x16,.x17]
def row5High : List Reg := [.x22,.x23,.x24,.x25,.x26,.x15,.x16,.x17,.x19]

def row5LowCode : List Instr := [
  .mul .x .x14 .x4 .x5,
  .adds .x .x21 .x21 .x14,
  .mul .x .x14 .x4 .x6,
  .adcs .x .x22 .x22 .x14,
  .mul .x .x14 .x4 .x7,
  .adcs .x .x23 .x23 .x14,
  .mul .x .x14 .x4 .x8,
  .adcs .x .x24 .x24 .x14,
  .mul .x .x14 .x4 .x9,
  .adcs .x .x25 .x25 .x14,
  .mul .x .x14 .x4 .x10,
  .adcs .x .x26 .x26 .x14,
  .mul .x .x14 .x4 .x11,
  .adcs .x .x15 .x15 .x14,
  .mul .x .x14 .x4 .x12,
  .adcs .x .x16 .x16 .x14,
  .mul .x .x14 .x4 .x13,
  .adcs .x .x17 .x17 .x14,
  .movz .x .x19 1 0,
  .cselc .x .x19 .x19 .x2 .hs]

def row5HighCode : List Instr := [
  .umulh .x14 .x4 .x5,
  .adds .x .x22 .x22 .x14,
  .umulh .x14 .x4 .x6,
  .adcs .x .x23 .x23 .x14,
  .umulh .x14 .x4 .x7,
  .adcs .x .x24 .x24 .x14,
  .umulh .x14 .x4 .x8,
  .adcs .x .x25 .x25 .x14,
  .umulh .x14 .x4 .x9,
  .adcs .x .x26 .x26 .x14,
  .umulh .x14 .x4 .x10,
  .adcs .x .x15 .x15 .x14,
  .umulh .x14 .x4 .x11,
  .adcs .x .x16 .x16 .x14,
  .umulh .x14 .x4 .x12,
  .adcs .x .x17 .x17 .x14,
  .umulh .x14 .x4 .x13,
  .adc .x .x19 .x19 .x14]

theorem row5_eq : (mulFnBlocks.flatten.drop 215).take 38 = row5LowCode++row5HighCode := by decide

theorem row5_low_words (s : State) (hz : s.gpr .x2=0) :
    WP isa (.block row5LowCode) s fun t =>
      row5In.map t.gpr = (addWords (row5In.map s.gpr) (bRegs.map (s.gpr .x4 * s.gpr ·)) false).1 ∧
      t.gpr .x19 = BitVec.ofNat 64 (addWords (row5In.map s.gpr) (bRegs.map (s.gpr .x4 * s.gpr ·)) false).2.toNat ∧
      Keeps (.x14::.x19::row5In) s t := by
  apply WP.of_runBlock
  simp only [row5LowCode,runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,Size.bits,
    CondCode.holds,RegUpd.gpr_write,RegUpd.gpr_addWithCarry,RegUpd.c_addWithCarry,RegUpd.c_write,
    BitVec.setWidth_eq,ite_true,ite_false,reduceCtorEq,Nat.reduceMul,Nat.reduceLT,Option.some.injEq,exists_eq_left']
  refine ⟨?_,?_,⟨?_,by simp only [RegUpd.mem_write,RegUpd.mem_addWithCarry],
    by simp only [RegUpd.rd_write,RegUpd.rd_addWithCarry],
    by simp only [RegUpd.wr_write,RegUpd.wr_addWithCarry],
    by simp only [RegUpd.sp_write,RegUpd.sp_addWithCarry]⟩⟩
  · simp only [row5In,bRegs,List.map_cons,List.map_nil,addWords,
      RegUpd.gpr_write,RegUpd.gpr_addWithCarry,BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false]
    rfl
  · simp only [row5In,bRegs,List.map_cons,List.map_nil,addWords,hz]
    exact carry_select _
  · dsimp only [row5In]
    reg_keeps

theorem row5_high_words (s : State) :
    WP isa (.block row5HighCode) s fun t =>
      row5High.map t.gpr = (addWords (row5High.map s.gpr) (bRegs.map (mulHi (s.gpr .x4) ∘ s.gpr)) false).1 ∧
      Keeps (.x14::row5High) s t := by
  apply WP.of_runBlock
  simp only [row5HighCode,runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,Size.bits,
    RegUpd.gpr_write,RegUpd.gpr_addWithCarry,RegUpd.c_addWithCarry,RegUpd.c_write,
    BitVec.setWidth_eq,ite_true,ite_false,reduceCtorEq,Option.some.injEq,exists_eq_left']
  refine ⟨?_,⟨?_,by simp only [RegUpd.mem_write,RegUpd.mem_addWithCarry],
    by simp only [RegUpd.rd_write,RegUpd.rd_addWithCarry],
    by simp only [RegUpd.wr_write,RegUpd.wr_addWithCarry],
    by simp only [RegUpd.sp_write,RegUpd.sp_addWithCarry]⟩⟩
  · simp only [row5High,bRegs,List.map_cons,List.map_nil,addWords,Function.comp_apply,
      RegUpd.gpr_write,RegUpd.gpr_addWithCarry,BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false]
    rfl
  · dsimp only [row5High]
    reg_keeps

def row5Out : List Reg := .x21::row5High

theorem row5_words (s : State) (hz : s.gpr .x2=0) :
    WP isa (.block (row5LowCode++row5HighCode)) s fun t =>
      row5Out.map t.gpr = (rowCarry (s.gpr .x4) (row5In.map s.gpr) (bRegs.map s.gpr)).1 ∧
      Keeps (.x14::row5Out) s t := by
  rw [WP.block_append_iff]
  refine WP.mono (row5_low_words s hz) fun u ⟨lo,carry,klo⟩ => ?_
  refine WP.mono (row5_high_words u) fun t ⟨hi,khi⟩ => ?_
  have a : u.gpr .x4=s.gpr .x4 := klo.gpr _ (by decide)
  have bs : bRegs.map u.gpr=bRegs.map s.gpr := List.map_congr_left fun r hr =>
    klo.gpr r ((show ∀r∈bRegs,r∉(.x14::.x19::row5In) from by decide) r hr)
  have hiIn : row5High.map u.gpr =
      (addWords (row5In.map s.gpr) (bRegs.map (s.gpr .x4 * s.gpr ·)) false).1.tail ++
        [BitVec.ofNat 64 (addWords (row5In.map s.gpr) (bRegs.map (s.gpr .x4 * s.gpr ·)) false).2.toNat] := by
    have hr : row5High=row5In.tail++[.x19] := rfl
    rw [hr,List.map_append,List.map_tail,lo]
    simp only [List.map_cons,List.map_nil,carry]
  have head := congrArg (fun xs : List Word => xs.headD 0) lo
  change u.gpr .x21=_ at head
  have hh : t.gpr .x21=u.gpr .x21 := khi.gpr _ (by decide)
  have hi' : row5High.map t.gpr =
      (addWords ((addWords (row5In.map s.gpr) (bRegs.map (s.gpr .x4 * s.gpr ·)) false).1.tail ++
        [BitVec.ofNat 64 (addWords (row5In.map s.gpr) (bRegs.map (s.gpr .x4 * s.gpr ·)) false).2.toNat])
        ((bRegs.map s.gpr).map (mulHi (s.gpr .x4))) false).1 := by
    rw [hi,hiIn,a,←List.map_map,bs]
  refine ⟨?_,(klo.mono (by decide)).trans (khi.mono (by decide))⟩
  simp only [row5Out,List.map_cons,hh,head,hi',rowCarry,List.map_map,Function.comp_def]

theorem row5_value (s : State) (hz : s.gpr .x2=0) :
    WP isa (.block (row5LowCode++row5HighCode)) s fun t =>
      regsVal t row5Out = regsVal s row5In + (s.gpr .x4).toNat*regsVal s bRegs ∧
      Keeps (.x14::row5Out) s t := by
  refine WP.mono (row5_words s hz) fun t ⟨h,k⟩ => ?_
  have e := congrArg value h
  rw [value_map_gpr,row_value _ _ _ (by simp only [List.length_map]; decide)
    (by simp only [List.length_map]; decide),value_map_gpr,value_map_gpr] at e
  exact ⟨e,k⟩

end VG.Proof.Mont.AArch64.P521Field
