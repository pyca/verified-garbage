module

-- separate module: The second nine-limb multiplication-row carry/value replay costs 0.92s of proof versus 0.48s of imports; PointMulProduct composition edits reuse that row certificate.

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.MulRow2
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-! Inline point multiplication row 2, retaining the measured GP allocation. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Impl.Mont.AArch64
open VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64
open VG.Proof.Mont.AArch64.P521Square (value addWords)

def pointMulRow2In : List Reg := [.x17,.x19,.x20,.x21,.x22,.x23,.x24,.x1,.x0]
def pointMulRow2High : List Reg := [.x19,.x20,.x21,.x22,.x23,.x24,.x1,.x0,.x15]

def pointMulRow2LowCode : List Instr := [
  .mul .x .x14 .x3 .x5,
  .adds .x .x17 .x17 .x14,
  .mul .x .x14 .x3 .x6,
  .adcs .x .x19 .x19 .x14,
  .mul .x .x14 .x3 .x7,
  .adcs .x .x20 .x20 .x14,
  .mul .x .x14 .x3 .x8,
  .adcs .x .x21 .x21 .x14,
  .mul .x .x14 .x3 .x9,
  .adcs .x .x22 .x22 .x14,
  .mul .x .x14 .x3 .x10,
  .adcs .x .x23 .x23 .x14,
  .mul .x .x14 .x3 .x11,
  .adcs .x .x24 .x24 .x14,
  .mul .x .x14 .x3 .x12,
  .adcs .x .x1 .x1 .x14,
  .mul .x .x14 .x3 .x13,
  .adcs .x .x0 .x0 .x14,
  .movz .x .x15 1 0,
  .cselc .x .x15 .x15 .x2 .hs]

def pointMulRow2HighCode : List Instr := [
  .umulh .x14 .x3 .x5,
  .adds .x .x19 .x19 .x14,
  .umulh .x14 .x3 .x6,
  .adcs .x .x20 .x20 .x14,
  .umulh .x14 .x3 .x7,
  .adcs .x .x21 .x21 .x14,
  .umulh .x14 .x3 .x8,
  .adcs .x .x22 .x22 .x14,
  .umulh .x14 .x3 .x9,
  .adcs .x .x23 .x23 .x14,
  .umulh .x14 .x3 .x10,
  .adcs .x .x24 .x24 .x14,
  .umulh .x14 .x3 .x11,
  .adcs .x .x1 .x1 .x14,
  .umulh .x14 .x3 .x12,
  .adcs .x .x0 .x0 .x14,
  .umulh .x14 .x3 .x13,
  .adc .x .x15 .x15 .x14]


theorem pointMulRow2_low_words (s : State) (hz : s.gpr .x2=0) :
    WP isa (.block pointMulRow2LowCode) s fun t =>
      pointMulRow2In.map t.gpr = (addWords (pointMulRow2In.map s.gpr) (bRegs.map (s.gpr .x3 * s.gpr ·)) false).1 ∧
      t.gpr .x15 = BitVec.ofNat 64 (addWords (pointMulRow2In.map s.gpr) (bRegs.map (s.gpr .x3 * s.gpr ·)) false).2.toNat ∧
      Keeps (.x14::.x15::pointMulRow2In) s t := by
  apply WP.of_runBlock
  simp only [pointMulRow2LowCode,runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,Size.bits,
    CondCode.holds,RegUpd.gpr_write,RegUpd.gpr_addWithCarry,RegUpd.c_addWithCarry,RegUpd.c_write,
    BitVec.setWidth_eq,ite_true,ite_false,reduceCtorEq,Nat.reduceMul,Nat.reduceLT,Option.some.injEq,exists_eq_left']
  refine ⟨?_,?_,⟨?_,by simp only [RegUpd.mem_write,RegUpd.mem_addWithCarry],
    by simp only [RegUpd.rd_write,RegUpd.rd_addWithCarry],
    by simp only [RegUpd.wr_write,RegUpd.wr_addWithCarry],
    by simp only [RegUpd.sp_write,RegUpd.sp_addWithCarry]⟩⟩
  · simp only [pointMulRow2In,bRegs,List.map_cons,List.map_nil,addWords,
      RegUpd.gpr_write,RegUpd.gpr_addWithCarry,BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false]
    rfl
  · simp only [pointMulRow2In,bRegs,List.map_cons,List.map_nil,addWords,hz]
    exact carry_select _
  · dsimp only [pointMulRow2In]
    reg_keeps

theorem pointMulRow2_high_words (s : State) :
    WP isa (.block pointMulRow2HighCode) s fun t =>
      pointMulRow2High.map t.gpr = (addWords (pointMulRow2High.map s.gpr) (bRegs.map (mulHi (s.gpr .x3) ∘ s.gpr)) false).1 ∧
      Keeps (.x14::pointMulRow2High) s t := by
  apply WP.of_runBlock
  simp only [pointMulRow2HighCode,runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,Size.bits,
    RegUpd.gpr_write,RegUpd.gpr_addWithCarry,RegUpd.c_addWithCarry,RegUpd.c_write,
    BitVec.setWidth_eq,ite_true,ite_false,reduceCtorEq,Option.some.injEq,exists_eq_left']
  refine ⟨?_,⟨?_,by simp only [RegUpd.mem_write,RegUpd.mem_addWithCarry],
    by simp only [RegUpd.rd_write,RegUpd.rd_addWithCarry],
    by simp only [RegUpd.wr_write,RegUpd.wr_addWithCarry],
    by simp only [RegUpd.sp_write,RegUpd.sp_addWithCarry]⟩⟩
  · simp only [pointMulRow2High,bRegs,List.map_cons,List.map_nil,addWords,Function.comp_apply,
      RegUpd.gpr_write,RegUpd.gpr_addWithCarry,BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false]
    rfl
  · dsimp only [pointMulRow2High]
    reg_keeps

def pointMulRow2Out : List Reg := .x17::pointMulRow2High

theorem pointMulRow2_words (s : State) (hz : s.gpr .x2=0) :
    WP isa (.block (pointMulRow2LowCode++pointMulRow2HighCode)) s fun t =>
      pointMulRow2Out.map t.gpr = (rowCarry (s.gpr .x3) (pointMulRow2In.map s.gpr) (bRegs.map s.gpr)).1 ∧
      Keeps (.x14::pointMulRow2Out) s t := by
  rw [WP.block_append_iff]
  refine WP.mono (pointMulRow2_low_words s hz) fun u ⟨lo,carry,klo⟩ => ?_
  refine WP.mono (pointMulRow2_high_words u) fun t ⟨hi,khi⟩ => ?_
  have a : u.gpr .x3=s.gpr .x3 := klo.gpr _ (by decide)
  have bs : bRegs.map u.gpr=bRegs.map s.gpr := List.map_congr_left fun r hr =>
    klo.gpr r ((show ∀r∈bRegs,r∉(.x14::.x15::pointMulRow2In) from by decide) r hr)
  have hiIn : pointMulRow2High.map u.gpr =
      (addWords (pointMulRow2In.map s.gpr) (bRegs.map (s.gpr .x3 * s.gpr ·)) false).1.tail ++
        [BitVec.ofNat 64 (addWords (pointMulRow2In.map s.gpr) (bRegs.map (s.gpr .x3 * s.gpr ·)) false).2.toNat] := by
    have hr : pointMulRow2High=pointMulRow2In.tail++[.x15] := rfl
    rw [hr,List.map_append,List.map_tail,lo]
    simp only [List.map_cons,List.map_nil,carry]
  have head := congrArg (fun xs : List Word => xs.headD 0) lo
  change u.gpr .x17=_ at head
  have hh : t.gpr .x17=u.gpr .x17 := khi.gpr _ (by decide)
  have hi' : pointMulRow2High.map t.gpr =
      (addWords ((addWords (pointMulRow2In.map s.gpr) (bRegs.map (s.gpr .x3 * s.gpr ·)) false).1.tail ++
        [BitVec.ofNat 64 (addWords (pointMulRow2In.map s.gpr) (bRegs.map (s.gpr .x3 * s.gpr ·)) false).2.toNat])
        ((bRegs.map s.gpr).map (mulHi (s.gpr .x3))) false).1 := by
    rw [hi,hiIn,a,←List.map_map,bs]
  refine ⟨?_,(klo.mono (by decide)).trans (khi.mono (by decide))⟩
  simp only [pointMulRow2Out,List.map_cons,hh,head,hi',rowCarry,List.map_map,Function.comp_def]

theorem pointMulRow2_value (s : State) (hz : s.gpr .x2=0) :
    WP isa (.block (pointMulRow2LowCode++pointMulRow2HighCode)) s fun t =>
      regsVal t pointMulRow2Out = regsVal s pointMulRow2In + (s.gpr .x3).toNat*regsVal s bRegs ∧
      Keeps (.x14::pointMulRow2Out) s t := by
  refine WP.mono (pointMulRow2_words s hz) fun t ⟨h,k⟩ => ?_
  have e := congrArg value h
  rw [value_map_gpr,row_value _ _ _ (by simp only [List.length_map]; decide)
    (by simp only [List.length_map]; decide),value_map_gpr,value_map_gpr] at e
  exact ⟨e,k⟩

end VG.Proof.Mont.AArch64.P521Field
