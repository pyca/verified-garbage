module

public import VerifiedGarbage.Proof.Framework.Omega
public meta import VerifiedGarbage.Proof.Framework.Omega
public meta import Lean.Elab.Tactic.Basic

/-!
# `omega_arith` on many goals

Untrusted: this only changes how proofs are found.

The facts about the offsets of many buffers, taken apart by `and_intros`,
are dozens of goals that repeat each other (the same bound of the same
buffer, against every buffer it is separate from), and `omega_arith` costs
as much on a repeat as on the first. `all_omega_arith` proves each type of
goal once, and uses that proof for the others; it closes a goal `a ≤ a`
about natural numbers by `Nat.le_refl`.
-/

public meta section

namespace VG.Omega

open Lean Meta Elab Tactic

/-- `omegaArith` on every goal, once for each type of goal. -/
def omegaArithAll : TacticM Unit := do
  let mut reps : Std.HashMap Expr MVarId := {}
  let mut todo : Array MVarId := #[]
  for g in ← getUnsolvedGoals do
    let ty ← instantiateMVars (← g.getType)
    if let some r := reps[ty]? then
      g.assign (.mvar r)
      continue
    if let (``LE.le, #[.const ``Nat [], _, a, b]) := ty.getAppFnArgs then
      if a == b then
        g.assign (mkApp (.const ``Nat.le_refl []) a)
        continue
    reps := reps.insert ty g
    todo := todo.push g
  for g in todo do
    setGoals [g]
    omegaArith
  setGoals []

end VG.Omega

/-- `omega_arith` on every goal, once for each type of goal (`omegaArithAll`). -/
elab "all_omega_arith" : tactic => VG.Omega.omegaArithAll
