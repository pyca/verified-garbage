module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.MulLast
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-! Inline point multiplication row 8, retaining the measured GP allocation. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Impl.Mont.AArch64
open VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64
open VG.Proof.Mont.AArch64.P521Square (value addWords)

def pointMulRow8In : List Reg := [.x24,.x1,.x0,.x15,.x16,.x17,.x19,.x20,.x21]
def pointMulRow8High : List Reg := [.x1,.x0,.x15,.x16,.x17,.x19,.x20,.x21]
def pointMulBLowRegs : List Reg := [.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12]

def pointMulRow8LowCode : List Instr := [
  .mul .x .x14 .x3 .x5,
  .adds .x .x24 .x24 .x14,
  .mul .x .x14 .x3 .x6,
  .adcs .x .x1 .x1 .x14,
  .mul .x .x14 .x3 .x7,
  .adcs .x .x0 .x0 .x14,
  .mul .x .x14 .x3 .x8,
  .adcs .x .x15 .x15 .x14,
  .mul .x .x14 .x3 .x9,
  .adcs .x .x16 .x16 .x14,
  .mul .x .x14 .x3 .x10,
  .adcs .x .x17 .x17 .x14,
  .mul .x .x14 .x3 .x11,
  .adcs .x .x19 .x19 .x14,
  .mul .x .x14 .x3 .x12,
  .adcs .x .x20 .x20 .x14,
  .mul .x .x14 .x3 .x13,
  .adc .x .x21 .x21 .x14]

def pointMulRow8HighCode : List Instr := [
  .umulh .x14 .x3 .x5,
  .adds .x .x1 .x1 .x14,
  .umulh .x14 .x3 .x6,
  .adcs .x .x0 .x0 .x14,
  .umulh .x14 .x3 .x7,
  .adcs .x .x15 .x15 .x14,
  .umulh .x14 .x3 .x8,
  .adcs .x .x16 .x16 .x14,
  .umulh .x14 .x3 .x9,
  .adcs .x .x17 .x17 .x14,
  .umulh .x14 .x3 .x10,
  .adcs .x .x19 .x19 .x14,
  .umulh .x14 .x3 .x11,
  .adcs .x .x20 .x20 .x14,
  .umulh .x14 .x3 .x12,
  .adc .x .x21 .x21 .x14]

theorem pointMulRow8_low_words (s : State) :
    WP isa (.block pointMulRow8LowCode) s fun t =>
      pointMulRow8In.map t.gpr = (addWords (pointMulRow8In.map s.gpr) (bRegs.map (s.gpr .x3 * s.gpr ·)) false).1 ∧
      Keeps (.x14::pointMulRow8In) s t := by
  apply WP.of_runBlock
  simp only [pointMulRow8LowCode,runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,Size.bits,
    RegUpd.gpr_write,RegUpd.gpr_addWithCarry,RegUpd.c_addWithCarry,RegUpd.c_write,
    BitVec.setWidth_eq,ite_true,ite_false,reduceCtorEq,Option.some.injEq,exists_eq_left']
  refine ⟨?_,⟨?_,by simp only [RegUpd.mem_write,RegUpd.mem_addWithCarry],
    by simp only [RegUpd.rd_write,RegUpd.rd_addWithCarry],
    by simp only [RegUpd.wr_write,RegUpd.wr_addWithCarry],
    by simp only [RegUpd.sp_write,RegUpd.sp_addWithCarry]⟩⟩
  · simp only [pointMulRow8In,bRegs,List.map_cons,List.map_nil,addWords,
      RegUpd.gpr_write,RegUpd.gpr_addWithCarry,BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false]
    rfl
  · dsimp only [pointMulRow8In]
    reg_keeps

theorem pointMulRow8_high_words (s : State) :
    WP isa (.block pointMulRow8HighCode) s fun t =>
      pointMulRow8High.map t.gpr = (addWords (pointMulRow8High.map s.gpr) (pointMulBLowRegs.map (mulHi (s.gpr .x3) ∘ s.gpr)) false).1 ∧
      Keeps (.x14::pointMulRow8High) s t := by
  apply WP.of_runBlock
  simp only [pointMulRow8HighCode,runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,Size.bits,
    RegUpd.gpr_write,RegUpd.gpr_addWithCarry,RegUpd.c_addWithCarry,RegUpd.c_write,
    BitVec.setWidth_eq,ite_true,ite_false,reduceCtorEq,Option.some.injEq,exists_eq_left']
  refine ⟨?_,⟨?_,by simp only [RegUpd.mem_write,RegUpd.mem_addWithCarry],
    by simp only [RegUpd.rd_write,RegUpd.rd_addWithCarry],
    by simp only [RegUpd.wr_write,RegUpd.wr_addWithCarry],
    by simp only [RegUpd.sp_write,RegUpd.sp_addWithCarry]⟩⟩
  · simp only [pointMulRow8High,pointMulBLowRegs,List.map_cons,List.map_nil,addWords,Function.comp_apply,
      RegUpd.gpr_write,RegUpd.gpr_addWithCarry,BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false]
    rfl
  · dsimp only [pointMulRow8High]
    reg_keeps


theorem pointMulRow8_words (s : State) :
    WP isa (.block (pointMulRow8LowCode++pointMulRow8HighCode)) s fun t =>
      pointMulRow8In.map t.gpr = narrowRow (s.gpr .x3) (pointMulRow8In.map s.gpr) (pointMulBLowRegs.map s.gpr) (s.gpr .x13) ∧
      Keeps (.x14::pointMulRow8In) s t := by
  rw [WP.block_append_iff]
  refine WP.mono (pointMulRow8_low_words s) fun u ⟨lo,klo⟩ => ?_
  refine WP.mono (pointMulRow8_high_words u) fun t ⟨hi,khi⟩ => ?_
  have a : u.gpr .x3=s.gpr .x3 := klo.gpr _ (by decide)
  have bs : pointMulBLowRegs.map u.gpr=pointMulBLowRegs.map s.gpr := List.map_congr_left fun r hr =>
    klo.gpr r ((show ∀r∈pointMulBLowRegs,r∉(.x14::pointMulRow8In) from by decide) r hr)
  have hiIn : pointMulRow8High.map u.gpr =
      (addWords (pointMulRow8In.map s.gpr) (bRegs.map (s.gpr .x3 * s.gpr ·)) false).1.tail := by
    have hr : pointMulRow8High=pointMulRow8In.tail := rfl
    rw [hr,List.map_tail,lo]
  have head := congrArg (fun xs : List Word => xs.headD 0) lo
  change u.gpr .x24=_ at head
  have hh : t.gpr .x24=u.gpr .x24 := khi.gpr _ (by decide)
  have hi' : pointMulRow8High.map t.gpr =
      (addWords (addWords (pointMulRow8In.map s.gpr) (bRegs.map (s.gpr .x3 * s.gpr ·)) false).1.tail
        ((pointMulBLowRegs.map s.gpr).map (mulHi (s.gpr .x3))) false).1 := by
    rw [hi,hiIn,a,←List.map_map,bs]
  have hr : pointMulRow8In=.x24::pointMulRow8High := rfl
  have br : bRegs=pointMulBLowRegs++[.x13] := rfl
  refine ⟨?_,(klo.mono (by decide)).trans (khi.mono (by decide))⟩
  calc
    pointMulRow8In.map t.gpr = t.gpr .x24 :: pointMulRow8High.map t.gpr := congrArg (List.map t.gpr) hr
    _ = _ := by
      rw [hh,head,hi']
      simp only [narrowRow,br,List.map_append,List.map_cons,List.map_nil,List.map_map,Function.comp_def]

theorem pointMulRow8_value (s : State) (htop : mulHi (s.gpr .x3) (s.gpr .x13)=0)
    (hb : regsVal s pointMulRow8In + (s.gpr .x3).toNat*regsVal s bRegs < 2^576) :
    WP isa (.block (pointMulRow8LowCode++pointMulRow8HighCode)) s fun t =>
      regsVal t pointMulRow8In = regsVal s pointMulRow8In + (s.gpr .x3).toNat*regsVal s bRegs ∧
      Keeps (.x14::pointMulRow8In) s t := by
  refine WP.mono (pointMulRow8_words s) fun t ⟨h,k⟩ => ?_
  have br : (pointMulBLowRegs.map s.gpr)++[s.gpr .x13]=bRegs.map s.gpr := rfl
  have hn := narrowRow_value (s.gpr .x3) (pointMulRow8In.map s.gpr) (pointMulBLowRegs.map s.gpr)
    (s.gpr .x13) (by simp only [List.length_map]; decide) htop (by
      have hlen : (pointMulRow8In.map s.gpr).length=9 := by rw [List.length_map]; rfl
      rw [br,value_map_gpr,value_map_gpr,hlen,show (64*9 : Nat)=576 from rfl]
      exact hb)
  have e := congrArg value h
  rw [value_map_gpr,hn,br,value_map_gpr,value_map_gpr] at e
  exact ⟨e,k⟩

end VG.Proof.Mont.AArch64.P521Field
