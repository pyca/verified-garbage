module

-- separate module: The nine-limb row carry/value replay at PointMulRow1 (pointMulRow1_low_words) costs 1.12s of proof versus 0.50s of imports; PointMulProduct composition edits reuse this checked computation.

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.MulRow
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-! Inline point multiplication row 1, retaining the measured GP allocation. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Impl.Mont.AArch64
open VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64
open VG.Proof.Mont.AArch64.P521Square (value addWords)

def pointMulRow1In : List Reg := [.x16,.x17,.x19,.x20,.x21,.x22,.x23,.x24,.x1]
def pointMulRow1High : List Reg := [.x17,.x19,.x20,.x21,.x22,.x23,.x24,.x1,.x0]

def pointMulRow1LowCode : List Instr := [
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
  .adcs .x .x1 .x1 .x14,
  .movz .x .x0 1 0,
  .cselc .x .x0 .x0 .x2 .hs]

def pointMulRow1HighCode : List Instr := [
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
  .adcs .x .x1 .x1 .x14,
  .umulh .x14 .x4 .x13,
  .adc .x .x0 .x0 .x14]


theorem pointMulRow1_low_words (s : State) (hz : s.gpr .x2=0) :
    WP isa (.block pointMulRow1LowCode) s fun t =>
      pointMulRow1In.map t.gpr = (addWords (pointMulRow1In.map s.gpr) (bRegs.map (s.gpr .x4 * s.gpr ·)) false).1 ∧
      t.gpr .x0 = BitVec.ofNat 64 (addWords (pointMulRow1In.map s.gpr) (bRegs.map (s.gpr .x4 * s.gpr ·)) false).2.toNat ∧
      Keeps (.x14::.x0::pointMulRow1In) s t := by
  apply WP.of_runBlock
  simp only [pointMulRow1LowCode,runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,Size.bits,
    CondCode.holds,RegUpd.gpr_write,RegUpd.gpr_addWithCarry,RegUpd.c_addWithCarry,RegUpd.c_write,
    BitVec.setWidth_eq,ite_true,ite_false,reduceCtorEq,Nat.reduceMul,Nat.reduceLT,Option.some.injEq,exists_eq_left']
  refine ⟨?_,?_,⟨?_,by simp only [RegUpd.mem_write,RegUpd.mem_addWithCarry],
    by simp only [RegUpd.rd_write,RegUpd.rd_addWithCarry],
    by simp only [RegUpd.wr_write,RegUpd.wr_addWithCarry],
    by simp only [RegUpd.sp_write,RegUpd.sp_addWithCarry]⟩⟩
  · simp only [pointMulRow1In,bRegs,List.map_cons,List.map_nil,addWords,
      RegUpd.gpr_write,RegUpd.gpr_addWithCarry,BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false]
    rfl
  · simp only [pointMulRow1In,bRegs,List.map_cons,List.map_nil,addWords,hz]
    exact carry_select _
  · dsimp only [pointMulRow1In]
    reg_keeps

theorem pointMulRow1_high_words (s : State) :
    WP isa (.block pointMulRow1HighCode) s fun t =>
      pointMulRow1High.map t.gpr = (addWords (pointMulRow1High.map s.gpr) (bRegs.map (mulHi (s.gpr .x4) ∘ s.gpr)) false).1 ∧
      Keeps (.x14::pointMulRow1High) s t := by
  apply WP.of_runBlock
  simp only [pointMulRow1HighCode,runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,Size.bits,
    RegUpd.gpr_write,RegUpd.gpr_addWithCarry,RegUpd.c_addWithCarry,RegUpd.c_write,
    BitVec.setWidth_eq,ite_true,ite_false,reduceCtorEq,Option.some.injEq,exists_eq_left']
  refine ⟨?_,⟨?_,by simp only [RegUpd.mem_write,RegUpd.mem_addWithCarry],
    by simp only [RegUpd.rd_write,RegUpd.rd_addWithCarry],
    by simp only [RegUpd.wr_write,RegUpd.wr_addWithCarry],
    by simp only [RegUpd.sp_write,RegUpd.sp_addWithCarry]⟩⟩
  · simp only [pointMulRow1High,bRegs,List.map_cons,List.map_nil,addWords,Function.comp_apply,
      RegUpd.gpr_write,RegUpd.gpr_addWithCarry,BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false]
    rfl
  · dsimp only [pointMulRow1High]
    reg_keeps

def pointMulRow1Out : List Reg := .x16::pointMulRow1High

theorem pointMulRow1_words (s : State) (hz : s.gpr .x2=0) :
    WP isa (.block (pointMulRow1LowCode++pointMulRow1HighCode)) s fun t =>
      pointMulRow1Out.map t.gpr = (rowCarry (s.gpr .x4) (pointMulRow1In.map s.gpr) (bRegs.map s.gpr)).1 ∧
      Keeps (.x14::pointMulRow1Out) s t := by
  rw [WP.block_append_iff]
  refine WP.mono (pointMulRow1_low_words s hz) fun u ⟨lo,carry,klo⟩ => ?_
  refine WP.mono (pointMulRow1_high_words u) fun t ⟨hi,khi⟩ => ?_
  have a : u.gpr .x4=s.gpr .x4 := klo.gpr _ (by decide)
  have bs : bRegs.map u.gpr=bRegs.map s.gpr := List.map_congr_left fun r hr =>
    klo.gpr r ((show ∀r∈bRegs,r∉(.x14::.x0::pointMulRow1In) from by decide) r hr)
  have hiIn : pointMulRow1High.map u.gpr =
      (addWords (pointMulRow1In.map s.gpr) (bRegs.map (s.gpr .x4 * s.gpr ·)) false).1.tail ++
        [BitVec.ofNat 64 (addWords (pointMulRow1In.map s.gpr) (bRegs.map (s.gpr .x4 * s.gpr ·)) false).2.toNat] := by
    have hr : pointMulRow1High=pointMulRow1In.tail++[.x0] := rfl
    rw [hr,List.map_append,List.map_tail,lo]
    simp only [List.map_cons,List.map_nil,carry]
  have head := congrArg (fun xs : List Word => xs.headD 0) lo
  change u.gpr .x16=_ at head
  have hh : t.gpr .x16=u.gpr .x16 := khi.gpr _ (by decide)
  have hi' : pointMulRow1High.map t.gpr =
      (addWords ((addWords (pointMulRow1In.map s.gpr) (bRegs.map (s.gpr .x4 * s.gpr ·)) false).1.tail ++
        [BitVec.ofNat 64 (addWords (pointMulRow1In.map s.gpr) (bRegs.map (s.gpr .x4 * s.gpr ·)) false).2.toNat])
        ((bRegs.map s.gpr).map (mulHi (s.gpr .x4))) false).1 := by
    rw [hi,hiIn,a,←List.map_map,bs]
  refine ⟨?_,(klo.mono (by decide)).trans (khi.mono (by decide))⟩
  simp only [pointMulRow1Out,List.map_cons,hh,head,hi',rowCarry,List.map_map,Function.comp_def]

theorem pointMulRow1_value (s : State) (hz : s.gpr .x2=0) :
    WP isa (.block (pointMulRow1LowCode++pointMulRow1HighCode)) s fun t =>
      regsVal t pointMulRow1Out = regsVal s pointMulRow1In + (s.gpr .x4).toNat*regsVal s bRegs ∧
      Keeps (.x14::pointMulRow1Out) s t := by
  refine WP.mono (pointMulRow1_words s hz) fun t ⟨h,k⟩ => ?_
  have e := congrArg value h
  rw [value_map_gpr,row_value _ _ _ (by simp only [List.length_map]; decide)
    (by simp only [List.length_map]; decide),value_map_gpr,value_map_gpr] at e
  exact ⟨e,k⟩

end VG.Proof.Mont.AArch64.P521Field
