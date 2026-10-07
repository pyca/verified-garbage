import Lean.Meta.Closure
import Lean.Elab.Tactic.BuiltinTactic

/-!
# Proofs the kernel checks with free variables

Untrusted: this only changes how proofs are found; the kernel checks them.

The kernel reduces closed `Nat` arithmetic it compares by evaluating it: a
proof whose terms contain `8 * ws.length` in two forms that are equal only by
unfolding (`8 * (sym, ws).2.length`, which `simp` reduces to
`8 * ws.length`) has the kernel evaluate `ws`, which for a large constant
table (a comb's, `Impl.Ecdsa.AArch64.Cfg.combWords`) takes most of a minute.
`generalize ws = x` does not help on its own: `instantiateMVars` puts `ws`
back for `x` in the proof. `kernel_aux => tac` proves the goal with `tac` in
an auxiliary theorem over the goal's free variables, which the kernel checks
with them free, so after `generalize ws = x`, never evaluating `ws`.
-/

namespace VG

open Lean Meta Elab Tactic in
/-- Proves the goal with `tac` in an auxiliary theorem, which the kernel
checks with the goal's free variables free. -/
elab "kernel_aux" " => " tac:tacticSeq : tactic => withMainContext do
  let g ← getMainGoal
  let gs ← Tactic.run g (evalTactic tac)
  unless gs.isEmpty do throwError "kernel_aux: unsolved goals"
  -- `zetaDelta := true` skips the `MetaM` type check of the proof that
  -- `as_aux_lemma` runs, seconds on a contract's terms; the kernel checks it.
  g.assign (← mkAuxTheorem (← g.getType) (← instantiateMVars (mkMVar g)) (zetaDelta := true))
  replaceMainGoal []

end VG
