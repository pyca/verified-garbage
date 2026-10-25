module

public import VerifiedGarbage.Proof.Framework.Block
public meta import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.RISCV64.Exec -- shake: keep (`crun` expands to its lemmas)
public meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec

/-!
# Running short RISC-V blocks symbolically

Untrusted: everything here is checked by Lean. `crun [h, …]` proves `WP isa
(.block is) s Q` for a short block by running it with `runBlock_cons`,
`runStep_some` and `runBlock_nil`, unfolding each instruction's semantics
and simplifying with the given facts, as PPC64LE's does; the immediates,
which are `Int`s, are decided encodable and turned into bit-vector
literals (a negative one added as a subtraction). It suits blocks of
a few instructions; longer ones are composed from them.
-/

public meta section

namespace VG.RISCV64

syntax "crun" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| crun) => `(tactic| crun [])
  | `(tactic| crun [$ls,*]) => `(tactic| (
      apply WP.of_runBlock
      set_option linter.unusedSimpArgs false in
      simp only [runBlock_cons, runStep_some, runBlock_nil,
        exec, State.write, addr, State.load, State.store, Width.bytes, imm12,
        BitVec.setWidth_eq, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
        Mem.read, BitVec.zero_width_append, BitVec.cast_eq, Option.bind_some, Option.map_some,
        Option.some.injEq, exists_eq_left', ite_true, ite_false, reduceCtorEq, ne_eq,
        not_false_eq_true, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, Nat.reduceAdd, Nat.reducePow,
        Nat.reduceEqDiff, Nat.reduceLeDiff, Nat.reduceSub, Nat.reduceDiv, Nat.mod_one, implies_true,
        true_implies, ↓reduceIte, and_self, true_and, and_true, Int.reduceLE, Int.reduceLT,
        Int.reduceNeg, BitVec.ofInt_neg, BitVec.ofInt_ofNat, ← BitVec.sub_eq_add_neg, $ls,*]))

end VG.RISCV64
