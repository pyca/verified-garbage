import VerifiedGarbage.Proof.X25519.X86_64.Step

/-!
# X25519 on x86-64, inversion by divsteps: running blocks

`drun` runs a block of the inversion by symbolic execution, reading
registers through the writes and deciding `cmov`s from the given facts.
-/

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64

theorem dz2 : (2 : BitVec 32).setWidth 64 = 2 := by decide
theorem ds2 : (2 : BitVec 32).signExtend 64 = 2 := by decide
theorem ds1 : (1 : BitVec 32).signExtend 64 = 1 := by decide
theorem b10 : ((1 : BitVec 64) == 0) = false := by decide
theorem b00 : ((0 : BitVec 64) == 0) = true := by decide
theorem and0 (x : BitVec 64) : x &&& 0 = 0 := by simp

/-- Runs a block by symbolic execution, reading registers through the
writes and deciding the `cmov`s from the given facts. -/
syntax "drun" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| drun) => `(tactic| drun [])
  | `(tactic| drun [$ls,*]) => `(tactic| (
      apply WP.of_runBlock
      set_option linter.unusedSimpArgs false in
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu,
        execShift, execMul, execCmov, eval, State.setReg32, Option.bind_some,
        Option.map_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags,
        RegUpd.zf_setReg, RegUpd.zf_arithFlags, RegUpd.cf_setReg, RegUpd.cf_arithFlags,
        RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
        RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setFlags,
        RegUpd.rd_setFlags, RegUpd.wr_setFlags, ite_true, ite_false, reduceCtorEq, Nat.le_refl,
        true_and, and_true, and_self, Nat.reduceLeDiff, Nat.reduceSub, Nat.reduceEqDiff, ↓reduceIte,
        Option.some.injEq, exists_eq_left', Bool.not_false, Bool.not_true, dz2, ds2, ds1, b10, b00,
        $ls,*]))

end VG.Proof.X25519.X86_64
