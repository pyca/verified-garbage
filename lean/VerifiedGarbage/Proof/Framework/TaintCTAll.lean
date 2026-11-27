module

public import VerifiedGarbage.Proof.Framework.TaintCT
public meta import VerifiedGarbage.Proof.Framework.TaintCT

/-!
# Several checks of a `TaintCT` in one kernel evaluation

The kernel forgets what it evaluated at the end of a declaration. Functions
that run the same code (a cipher's modes, a hash function's variants) each
proved in a declaration of its own what its residue analysis ends in, and
the kernel analysed the code they share once for each.
`taint_decide_ct_all` proves several in one declaration, from which each
function takes its own:

    theorem residue :
        rtaint.Ends (RTaint.init 1580 0) Fn.cbcDecryptChained (RTaint.done 0) ∧
        rtaint.Ends (RTaint.init 1580 0) Fn.cfbDecrypt (RTaint.done 0) := by
      taint_decide_ct_all

The analysis of the same instructions from the same taint is then evaluated
once: for nine modes of a cipher, the time of two.
-/

@[expose] public section

namespace VG

/-- The analysis of `c` from `τ` succeeds, for some hint, and ends in a taint
that `done` accepts. -/
abbrev TaintCT.Ends {M : ISA} (A : TaintCT M) (τ : A.T) (c : Prog M) (done : A.T → Bool) : Prop :=
  ∃ hc, (A.check τ c hc).any done = true

open Lean Meta in
/-- The goals of `g`, a conjunction: those that are `∃ hc, …` of a hint. -/
private meta partial def splitGoals (g : MVarId) : MetaM (List MVarId) := g.withContext do
  let ty ← whnf (← g.getType)
  if let some (a, b) := ty.and? then
    let x ← mkFreshExprSyntheticOpaqueMVar a
    let y ← mkFreshExprSyntheticOpaqueMVar b
    g.assign (mkApp4 (mkConst ``And.intro) a b x y)
    return (← splitGoals x.mvarId!) ++ (← splitGoals y.mvarId!)
  if ty.isAppOfArity ``Exists 2 then
    let (α, p) := (ty.appFn!.appArg!, ty.appArg!)
    let w ← mkFreshExprSyntheticOpaqueMVar α
    let x ← mkFreshExprSyntheticOpaqueMVar (p.beta #[w])
    g.assign (mkApp4 (mkConst ``Exists.intro ty.getAppFn.constLevels!) α p w x)
    return [x.mvarId!]
  return [g]

open Lean Meta Elab Tactic in
/-- Assigns the hint of the goal `g`, if it is an equation whose left side
contains `TaintCT.check A τ c ?hint`, from compiled code. -/
private meta def assignHintCT (g : MVarId) (chunkSize : Expr) : TacticM Unit := g.withContext do
  let some (_, lhs, _) := (← instantiateMVars (← g.getType)).eq? | return
  let some chk := lhs.find? (·.isAppOfArity ``TaintCT.check 5) | return
  let args := chk.getAppArgs
  let (m, a, τ, c, h) := (args[0]!, args[1]!, args[2]!, args[3]!, args[4]!)
  unless h.isMVar do return
  let tT ← whnfD (mkApp2 (mkConst ``TaintCT.T) m a)
  let hint := mkApp5 (mkConst ``TaintCT.hintOfSize) (← Taint.compiled m) a chunkSize τ c
  let instT ← synthInstance (mkApp (mkConst ``ToExpr [0]) tT)
  h.mvarId!.assign
    (← unsafe VG.Lit.evalOnce Expr (mkConst ``Expr) (mkApp3 (mkConst ``Taint.Hint.toExprNS) tT instT hint))

open Lean Meta Elab Tactic in
/-- Proves the goals together: the hints, and then one kernel evaluation of
their conjunction. -/
private meta def taintDecideCTAll (chunkSize : Expr) : TacticM Unit := do
  let gs ← getGoals
  for g in gs do assignHintCT g chunkSize
  let tys ← gs.mapM fun g => do instantiateMVars (← g.getType)
  let some last := tys.getLast? | return
  let conj := tys.dropLast.foldr mkAnd last
  let m ← mkFreshExprSyntheticOpaqueMVar conj
  let mut p : Expr := m
  let mut rest := tys
  for g in gs do
    match rest with
    | a :: b :: bs =>
      let r := (b :: bs).dropLast.foldr mkAnd last
      g.assign (mkApp3 (mkConst ``And.left) a r p)
      p := mkApp3 (mkConst ``And.right) a r p
      rest := b :: bs
    | _ => g.assign p
  setGoals [m.mvarId!]
  evalTactic (← `(tactic| lit_decide))

open Lean Elab Tactic in
/-- Proves a conjunction of `TaintCT.Ends` (and of decidable propositions
about closed terms), as `taint_decide_ct` does each, in one kernel
evaluation. -/
elab "taint_decide_ct_all" : tactic => do
  let g ← getMainGoal
  replaceMainGoal (← splitGoals g)
  let saved ← saveState
  try
    taintDecideCTAll (mkNatLit 1024)
  catch _ =>
    saved.restore
    taintDecideCTAll (mkConst ``Taint.chunk)

end VG
