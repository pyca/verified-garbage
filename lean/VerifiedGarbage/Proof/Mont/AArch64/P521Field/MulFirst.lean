module

public import VerifiedGarbage.Impl.Mont.AArch64.P521Field.Kernels
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.ProductMath
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.Hoist
public import VerifiedGarbage.Proof.Mont.AArch64.Words
import VerifiedGarbage.Proof.Mont.AArch64.Chain
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-! The first streamed multiplication row, with its loads hoisted for proof. -/

-- separate module: isolates the first-row schedule and carry proof
@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Impl.Mont.AArch64
open VG.Impl.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.Word64
open VG.Proof.Ed25519.AArch64
open VG.Proof.Mont.AArch64.P521Square (value)

def bRegs : List Reg := [.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13]
def row0Out : List Reg := [.x15,.x16,.x17,.x19,.x20,.x21,.x22,.x23,.x24,.x25]
def row0Clob : List Reg := .x2::.x14::row0Out
def row0Code : List Instr := (mulFnBlocks.flatten.drop 16).take 39
def row0Loads : List Instr := loadsR .x1 [.x3,.x4] 0 ++ loadsR .x2 bRegs 0

def row0Arithmetic : List Instr := [
  .mul .x .x15 .x3 .x5,
  .umulh .x16 .x3 .x5,
  .mul .x .x14 .x3 .x6,
  .umulh .x17 .x3 .x6,
  .adds .x .x16 .x16 .x14,
  .mul .x .x14 .x3 .x7,
  .umulh .x19 .x3 .x7,
  .adcs .x .x17 .x17 .x14,
  .mul .x .x14 .x3 .x8,
  .umulh .x20 .x3 .x8,
  .adcs .x .x19 .x19 .x14,
  .mul .x .x14 .x3 .x9,
  .umulh .x21 .x3 .x9,
  .adcs .x .x20 .x20 .x14,
  .mul .x .x14 .x3 .x10,
  .umulh .x22 .x3 .x10,
  .adcs .x .x21 .x21 .x14,
  .mul .x .x14 .x3 .x11,
  .umulh .x23 .x3 .x11,
  .adcs .x .x22 .x22 .x14,
  .mul .x .x14 .x3 .x12,
  .umulh .x24 .x3 .x12,
  .adcs .x .x23 .x23 .x14,
  .mul .x .x14 .x3 .x13,
  .umulh .x25 .x3 .x13,
  .adcs .x .x24 .x24 .x14,
  .movz .x .x2 0 0,
  .adc .x .x25 .x25 .x2]

theorem row0_hoist : hoistLoads .x1 row0Code = some (row0Loads,row0Arithmetic) := by
  decide

theorem row0_arithmetic_words_zero (s : State) :
    WP isa (.block row0Arithmetic) s fun t =>
      row0Out.map t.gpr = firstRow (s.gpr .x3) (bRegs.map s.gpr) ∧
      t.gpr .x2=0 ∧ Keeps row0Clob s t := by
  apply WP.of_runBlock
  simp only [row0Arithmetic,runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,Size.bits,
    RegUpd.gpr_write,RegUpd.gpr_addWithCarry,RegUpd.c_addWithCarry,RegUpd.c_write,
    BitVec.setWidth_eq,ite_true,ite_false,reduceCtorEq,Nat.reduceMul,Nat.reduceLT,Option.some.injEq,exists_eq_left']
  refine ⟨?_,rfl,⟨?_,by simp only [RegUpd.mem_write,RegUpd.mem_addWithCarry],
    by simp only [RegUpd.rd_write,RegUpd.rd_addWithCarry],
    by simp only [RegUpd.wr_write,RegUpd.wr_addWithCarry],
    by simp only [RegUpd.sp_write,RegUpd.sp_addWithCarry]⟩⟩
  · simp only [row0Out,bRegs,List.map_cons,List.map_nil,firstRow,firstChain,
      addCarry,carryOut,mulHi,RegUpd.gpr_write,RegUpd.gpr_addWithCarry,
      BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false]
    rfl
  · dsimp only [row0Clob,row0Out]
    reg_keeps

theorem row0_arithmetic_words (s : State) :
    WP isa (.block row0Arithmetic) s fun t =>
      row0Out.map t.gpr = firstRow (s.gpr .x3) (bRegs.map s.gpr) ∧
      Keeps row0Clob s t :=
  WP.mono (row0_arithmetic_words_zero s) fun _ ⟨h,_,k⟩ => ⟨h,k⟩

theorem value_map_gpr (s : State) (rs : List Reg) : value (rs.map s.gpr) = regsVal s rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [List.map_cons,value,regsVal,ih]

theorem row0_arithmetic_value (s : State) :
    WP isa (.block row0Arithmetic) s fun t =>
      regsVal t row0Out = (s.gpr .x3).toNat*regsVal s bRegs ∧ Keeps row0Clob s t := by
  refine WP.mono (row0_arithmetic_words s) fun t ⟨h,k⟩ => ?_
  have e := congrArg value h
  rw [value_map_gpr,firstRow_value,value_map_gpr] at e
  exact ⟨e,k⟩

theorem row0_arithmetic_value_zero (s : State) :
    WP isa (.block row0Arithmetic) s fun t =>
      regsVal t row0Out = (s.gpr .x3).toNat*regsVal s bRegs ∧
      t.gpr .x2=0 ∧ Keeps row0Clob s t := by
  refine WP.mono (row0_arithmetic_words_zero s) fun t ⟨h,z,k⟩ => ?_
  have e := congrArg value h
  rw [value_map_gpr,firstRow_value,value_map_gpr] at e
  exact ⟨e,z,k⟩

/-- The measured interleaved first row loads both multiplicands before
producing the ten-word row. No output memory is written. -/
theorem row0_ok {s : State} {pa pb : Addr}
    (ha : Ptr s .x1 pa 72) (hb : Ptr s .x2 pb 72) :
    WP isa (.block row0Code) s fun t =>
      regsVal t row0Out = (word s.mem pa 0).toNat*wordsVal s.mem pb 0 9 ∧
      t.gpr .x4 = word s.mem pa 8 ∧
      regsVal t bRegs = wordsVal s.mem pb 0 9 ∧
      Keeps (.x3::.x4::bRegs++row0Clob) s t := by
  apply WP.hoistLoads row0_hoist
  have hl : loadsR .x1 [.x3,.x4] 0 =
      ([.ldr .x .x3 .x1 0] : List Instr) ++ [.ldr .x .x4 .x1 8] := rfl
  rw [row0Loads,hl,List.append_assoc,List.append_assoc,WP.block_append_iff]
  refine WP.mono (ldR_ok ha (d:=0) (by decide) (by decide) .x3)
    fun s₁ ⟨a₁,k₁,_⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ldR_ok (ha.of_keeps k₁ (by decide))
    (d:=8) (by decide) (by decide) .x4) fun s₂ ⟨a₂,k₂,_⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadsR_ok bRegs ((hb.of_keeps k₁ (by decide)).of_keeps k₂ (by decide))
    (a:=0) (by decide) (by decide) (by decide) (by decide)) fun s₃ ⟨b₃,k₃,_⟩ => ?_
  refine WP.mono (row0_arithmetic_value s₃) fun t ⟨out,k₄⟩ => ?_
  have a₃ : s₃.gpr .x3 = word s.mem pa 0 := by
    rw [k₃.gpr _ (by decide),k₂.gpr _ (by decide),a₁]
  have a₄ : t.gpr .x4 = word s.mem pa 8 := by
    rw [k₄.gpr _ (by decide),k₃.gpr _ (by decide),a₂,k₁.mem]
  have b₃' : regsVal s₃ bRegs = wordsVal s.mem pb 0 9 := by
    change regsVal s₃ bRegs = wordsVal s₂.mem pb 0 9 at b₃
    rw [b₃,k₂.mem,k₁.mem]
  have b₄ : regsVal t bRegs = regsVal s₃ bRegs := regsVal_congr fun r hr =>
    k₄.gpr r ((show ∀r∈bRegs,r∉row0Clob from by decide) r hr)
  refine ⟨by rw [out,a₃,b₃'],a₄,b₄.trans b₃',?_⟩
  exact (k₁.mono (by decide)).trans ((k₂.mono (by decide)).trans
    ((k₃.mono (by decide)).trans (k₄.mono (by decide))))

end VG.Proof.Mont.AArch64.P521Field
