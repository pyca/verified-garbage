import VerifiedGarbage.Impl.Weierstrass.X86_64.Inv
import VerifiedGarbage.Proof.Weierstrass.X86_64.Loop

/-!
# Inversion by divsteps on x86-64: running blocks

`irun`, which runs a block of register and memory instructions by symbolic
execution, reading registers through the writes, for the inversion's proofs.
-/

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)

theorem sext1 : (1 : BitVec 32).signExtend 64 = 1 := by decide
theorem sext2 : (2 : BitVec 32).signExtend 64 = 2 := by decide
theorem zext0 : (0 : BitVec 32).setWidth 64 = 0 := by decide

/-- Runs a block of register and memory instructions by symbolic execution,
reading registers through the writes. -/
syntax "irun" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| irun) => `(tactic| irun [])
  | `(tactic| irun [$ls,*]) => `(tactic| (
      apply WP.of_runBlock
      set_option linter.unusedSimpArgs false in
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu,
        execShift, execMul, State.setReg32, Option.bind_some,
        Option.map_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags,
        RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.cf_arithFlags,
        RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setFlags,
        RegUpd.rd_setFlags, RegUpd.wr_setFlags, ite_true, ite_false, reduceCtorEq, Nat.le_refl,
        true_and, and_true, and_self, Nat.reduceLeDiff, Nat.reduceSub, Nat.reduceEqDiff, ↓reduceIte,
        Option.some.injEq, exists_eq_left', sext1, sext2, zext0, $ls,*]))

end VG.Proof.Weierstrass.X86_64
