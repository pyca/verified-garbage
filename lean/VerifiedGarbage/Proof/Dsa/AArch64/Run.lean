module

public import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-! Symbolic execution retaining linked workspace base addresses. -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64

syntax "drun" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| drun) => `(tactic| drun [])
  | `(tactic| drun [$ls,*]) => `(tactic| plain_simp_names (
                       apply WP.of_runBlock
                       set_option linter.unusedSimpArgs false in
                       simp only [↓reduceIte, Nat.reduceLT, Nat.reduceAdd, Nat.reduceMul, Nat.reducePow, runBlock_cons, runStep_some, runBlock_nil,
                         exec_ldr_x', exec_str_x', exec_ldrb', exec_strb', exec_add_x, exec_sub_x, exec_logic_x, exec_mul_x,
                         exec_umulh, exec_adds_x, exec_adcs_x, exec_subs_x, exec_sbcs_x, exec_adc_x, exec_csel_x,
                         exec_addImm_x', exec_subImm_x', exec_lsl_x, exec_lsr_x', exec_movz_x,
                         ld, st, ldh, sth, mov, movi, next,
                         State.read, Size.bits, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
                         RegUpd.sp_write, RegUpd.c_write, gpr_addWithCarry_x, c_addWithCarry_x, RegUpd.mem_addWithCarry,
                         RegUpd.rd_addWithCarry, RegUpd.wr_addWithCarry, RegUpd.sp_addWithCarry, gpr_mem, mem_mem, rd_mem,
                         wr_mem, c_mem, BitVec.setWidth_eq, off_zero, Nat.add_zero, Option.some.injEq,
                         exists_eq_left', ite_true, ite_false, reduceCtorEq, true_and, and_true, List.cons_append,
                         List.nil_append, $ls,*]))

end VG.Proof.Dsa.AArch64
