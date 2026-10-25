module

public import VerifiedGarbage.Proof.Framework.Block
public meta import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.PPC64LE.Exec -- shake: keep (`crunr` names its lemmas where it runs)
public meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
public import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd -- shake: keep (`crunr` names its lemmas where it runs)
public meta import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd

/-!
# Running short PPC64LE blocks symbolically, registers read through writes

Untrusted: everything here is checked by Lean. `crunr [h, …]` is `crun`
(`Run.lean`) but for the registers: it reads them through `State.write` with
`RegUpd.gpr_write` (an `if`, decided for literal registers) rather than
unfolding the write into a function on registers, which `simp` would
simplify again after every instruction. Its result is not always in the
shape `crun` leaves, so a proof written after `crun` may need changes.
-/

public meta section

namespace VG.PPC64LE

syntax "crunr" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| crunr) => `(tactic| crunr [])
  | `(tactic| crunr [$ls,*]) => `(tactic| (
      apply WP.of_runBlock
      set_option linter.unusedSimpArgs false in
      simp only [runBlock_cons, runStep_some, runBlock_nil,
        exec, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write,
        RegUpd.lr_write, State.read, addr, State.load, State.store, Size.bytes, Size.bits, Size.ext,
        BitVec.setWidth_eq, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
        Mem.read, BitVec.zero_width_append, BitVec.cast_eq, Option.bind_some, Option.map_some,
        Option.some.injEq, exists_eq_left', ite_true, ite_false, reduceCtorEq, ne_eq,
        not_false_eq_true, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, Nat.reduceAdd, Nat.reducePow,
        Nat.reduceEqDiff, Nat.reduceLeDiff, Nat.reduceSub, Nat.reduceDiv, implies_true, true_implies,
        ↓reduceIte, and_self, true_and, and_true, $ls,*]))

end VG.PPC64LE
