module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.BuildAdvance
public import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Omega

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Ed25519.AArch64
open VG.Impl.Weierstrass.AArch64.P521Native

def buildCounter : List Instr := [.addImm .x .x20 .x20 216,.subImm .x .x19 .x19 1]

theorem build_counter_source : outerBlock027.drop 109=buildCounter := by lit_decide

theorem build_counter_ok (s : State) :
    WP isa (.block buildCounter) s fun t =>
      t.gpr .x20=s.gpr .x20+216#64 ∧ t.gpr .x19=s.gpr .x19-1#64 ∧
      Keeps [.x20,.x19] s t ∧ t.v=s.v := by
  apply WP.of_runBlock
  simp only [buildCounter,
    runBlock_cons,runStep_some,runBlock_nil,reduceExec,Size.bits,Nat.reduceLT,
    RegUpd.gpr_write,RegUpd.v_write,BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false,
    Option.some.injEq,exists_eq_left']
  refine ⟨rfl,rfl,⟨?_,by simp only [RegUpd.mem_write],by simp only [RegUpd.rd_write],
    by simp only [RegUpd.wr_write],by simp only [RegUpd.sp_write]⟩,trivial⟩
  reg_keeps

theorem build_counter_pointer {table : Addr} {m : Nat} :
    (off table (216*m))+216#64=off table (216*(m+1)) := by
  dsimp only [off]
  rw [Nat.mul_add,Nat.mul_one,BitVec.ofNat_add]
  exact BitVec.add_assoc _ _ _

theorem build_counter_count (m : Nat) (hm : m<16) :
    BitVec.ofNat 64 (16-m)-1#64=BitVec.ofNat 64 (16-(m+1)) := by
  have he : 16-m=(16-(m+1))+1 := by omega_arith
  rw [he,BitVec.ofNat_add,BitVec.add_sub_cancel]

end VG.Proof.Weierstrass.AArch64.P521Native
