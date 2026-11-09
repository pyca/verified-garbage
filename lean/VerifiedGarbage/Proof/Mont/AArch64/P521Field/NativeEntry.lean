module

public import VerifiedGarbage.Impl.Mont.AArch64.P521Field.Kernels
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Saves
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-! The ordinary multiplier saves its callee-saved registers in SIMD lanes. -/

-- separate module: entry and pointer setup without arithmetic or layout assumptions
@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Impl.Mont.AArch64.P521Field
open VG.Proof.Ed25519.AArch64
open VG.Proof.Mont.AArch64.P521Square (insCode)

def nativeSaved : List Reg := [.x19,.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x27,.x28]
def nativePointers : List Instr := [
  .addImm .x .x28 .x0 0,
  .addImm .x .x27 .x0 3952,
  .add .x .x4 .x0 .x1,
  .add .x .x1 .x0 .x2,
  .add .x .x2 .x0 .x3,
  .addImm .x .x0 .x4 0]

theorem nativeEntry_eq : mulFnBlocks.flatten.take 16=insCode nativeSaved 0++nativePointers := by decide

theorem native_pointers_ok (s : State) :
    WP isa (.block nativePointers) s fun t =>
      t.gpr .x0=s.gpr .x0+s.gpr .x1 ∧
      t.gpr .x1=s.gpr .x0+s.gpr .x2 ∧
      t.gpr .x2=s.gpr .x0+s.gpr .x3 ∧
      t.gpr .x27=s.gpr .x0+BitVec.ofNat 64 3952 ∧ t.gpr .x28=s.gpr .x0 ∧
      Keeps [.x0,.x1,.x2,.x4,.x27,.x28] s t ∧ t.v=s.v := by
  apply WP.of_runBlock
  simp only [nativePointers,runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,
    RegUpd.gpr_write,BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false,
    show (0 : Nat)<4096 from by decide,show (3952 : Nat)<4096 from by decide,
    BitVec.add_zero,Option.some.injEq,exists_eq_left']
  refine ⟨trivial,trivial,trivial,trivial,trivial,⟨?_,by simp only [RegUpd.mem_write],
    by simp only [RegUpd.rd_write],by simp only [RegUpd.wr_write],
    by simp only [RegUpd.sp_write]⟩,by simp only [RegUpd.v_write]⟩
  reg_keeps

end VG.Proof.Mont.AArch64.P521Field
