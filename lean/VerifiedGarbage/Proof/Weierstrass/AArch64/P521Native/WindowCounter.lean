module

public import VerifiedGarbage.Impl.Weierstrass.AArch64.P521Native.OuterBlocks
public import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega

/-! Exact public loop-counter and double-call argument blocks. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Ed25519.AArch64
open VG.Impl.Weierstrass.AArch64.P521Native

 theorem window_counter_enter (s : State) :
    WP isa (.block outerBlock137) s fun t =>
      t.gpr .x19=s.gpr .x19-1#64+8589934592#64 ∧
      t.gpr .x2=8589934592#64 ∧ Keeps [.x19,.x2] s t ∧ t.v=s.v := by
  change WP isa (.block [.subImm .x .x19 .x19 1,.movz .x .x2 2 2,.add .x .x19 .x19 .x2]) s _
  apply WP.of_runBlock
  simp only [
    runBlock_cons,runStep_some,runBlock_nil,reduceExec,Size.bits,Nat.reduceLT,Nat.reduceMul,
    RegUpd.gpr_write,RegUpd.v_write,BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false,
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,?_,⟨?_,by simp only [RegUpd.mem_write],by simp only [RegUpd.rd_write],
    by simp only [RegUpd.wr_write],by simp only [RegUpd.sp_write]⟩,trivial⟩
  · rfl
  · rfl
  · reg_keeps

 theorem window_counter_pair (s : State) :
    WP isa (.block outerBlock140) s fun t =>
      t.gpr .x19=s.gpr .x19-4294967296#64 ∧
      t.gpr .x2=(s.gpr .x19-4294967296#64)>>>32 ∧
      Keeps [.x19,.x2] s t ∧ t.v=s.v := by
  change WP isa (.block [.movz .x .x2 1 2,.sub .x .x19 .x19 .x2,.lsr .x .x2 .x19 32]) s _
  apply WP.of_runBlock
  simp only [
    runBlock_cons,runStep_some,runBlock_nil,reduceExec,Size.bits,Nat.reduceLT,Nat.reduceMul,
    RegUpd.gpr_write,RegUpd.v_write,BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false,
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,?_,⟨?_,by simp only [RegUpd.mem_write],by simp only [RegUpd.rd_write],
    by simp only [RegUpd.wr_write],by simp only [RegUpd.sp_write]⟩,trivial⟩
  · rfl
  · rfl
  · reg_keeps

/-- The low word is the digit index; the high word counts double pairs. -/
def windowPacked (j c : Nat) : BitVec 64 := BitVec.ofNat 64 (j+c*4294967296)

theorem window_counter_enter_value (j : Nat) :
    BitVec.ofNat 64 (j+1)-1#64+8589934592#64=windowPacked j 2 := by
  rw [BitVec.ofNat_add,BitVec.add_sub_cancel]
  exact (BitVec.ofNat_add j 8589934592).symm

theorem window_counter_pair_value (j c : Nat) (hc : 1≤c) :
    windowPacked j c-4294967296#64=windowPacked j (c-1) := by
  have e : j+c*4294967296=(j+(c-1)*4294967296)+4294967296 := by omega_arith
  simp only [windowPacked,e,BitVec.ofNat_add,BitVec.add_sub_cancel]

theorem window_counter_high (j c : Nat) (hj : j<4294967296) (hc : c≤2) :
    windowPacked j c>>>32=BitVec.ofNat 64 c := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight,windowPacked,BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega_arith),Nat.mod_eq_of_lt (by omega_arith),Nat.shiftRight_eq_div_pow]
  rw [show (2:Nat)^32=4294967296 from rfl,Nat.add_mul_div_right j c (by decide),
    Nat.div_eq_of_lt hj,Nat.zero_add]

end VG.Proof.Weierstrass.AArch64.P521Native
