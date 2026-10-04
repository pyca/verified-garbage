import VerifiedGarbage.Proof.Framework.Taint

/-!
# Many decidable checks in one kernel evaluation

`taint_decide` pays a fixed cost for every check: compiling and running the
search for its hint (`Taint.hintOf`), rewriting the goal to literals
(`rw_lit`) and a declaration for the kernel. A module that proves many small
checks (e.g. a hash function's `CoreOK`, dozens of short pieces of code
between calls) pays it dozens of times. `taint_decide_all` proves all the
goals at once: it computes the hints of every `Taint.check` among them in one
compiled evaluation, and has the kernel evaluate the conjunction of the goals
in one declaration (`lit_decide`), from which each goal is a projection.

The goals may be any decidable propositions (e.g. `allInstrs` checks or
`depth` bounds), with or without `Taint.check`, but must not mention local
hypotheses.
-/

namespace VG

open Lean Meta Elab Tactic

/-- The applications `Taint.check M A τ c ?h` of `e`, whose hint `?h` is an
unassigned metavariable. -/
private partial def checksWithHole (e : Expr) (acc : Array Expr) : Array Expr :=
  let acc := e.getAppArgs.foldl (fun acc a => checksWithHole a acc) acc
  let acc := match e.getAppFn with
    | .lam _ t b _ | .forallE _ t b _ => checksWithHole b (checksWithHole t acc)
    | .letE _ t v b _ => checksWithHole b (checksWithHole v (checksWithHole t acc))
    | .mdata _ b | .proj _ _ b => checksWithHole b acc
    | _ => acc
  if e.isAppOfArity ``Taint.check 5 && e.getAppArgs[4]!.isMVar then acc.push e else acc

/-- A `Decidable` instance of `t`, built conjunct by conjunct. -/
private partial def decAnd (t : Expr) : MetaM Expr := do
  if t.isAppOfArity ``And 2 then
    let p := t.appFn!.appArg!
    let q := t.appArg!
    return mkApp4 (mkConst ``instDecidableAnd) p q (← decAnd p) (← decAnd q)
  synthInstance (mkApp (mkConst ``Decidable) t)

/-- Proves every goal, each a decidable proposition about closed terms, some
with `Taint.check A τ c ?hint` whose hint is to be computed (as
`taint_decide` does): all hints in one compiled evaluation, and all goals with
one kernel evaluation of their conjunction (as `lit_decide`). -/
elab "taint_decide_all" : tactic => do
  let gs ← getUnsolvedGoals
  if gs.isEmpty then return
  -- The hints, computed in one evaluation.
  let mut seen : Std.HashSet MVarId := {}
  let mut holes : Array MVarId := #[]
  let mut vals : Array Expr := #[]
  for g in gs do
    let ty ← instantiateMVars (← g.getType)
    for chk in checksWithHole ty #[] do
      let args := chk.getAppArgs
      let (m, a, τ, c, h) := (args[0]!, args[1]!, args[2]!, args[3]!, args[4]!)
      let hm := h.mvarId!
      if seen.contains hm then continue
      seen := seen.insert hm
      let tT ← whnfD (mkApp2 (mkConst ``Taint.T) m a)
      let hty := mkApp (mkConst ``Taint.Hint) tT
      let inst ← synthInstance (mkApp (mkConst ``ToExpr [0]) hty)
      let hint := mkApp4 (mkConst ``Taint.hintOf) m a τ c
      holes := holes.push hm
      vals := vals.push (mkApp3 (mkConst ``ToExpr.toExpr [0]) hty inst hint)
  unless holes.isEmpty do
    let lst ← mkListLit (mkConst ``Expr) vals.toList
    let hvs ← unsafe evalExpr (List Expr) (mkApp (mkConst ``List [0]) (mkConst ``Expr)) lst
    for (hm, hv) in holes.zip hvs.toArray do
      hm.assign hv
  -- The goals, from one kernel evaluation of their conjunction (the hints,
  -- if they were goals, are assigned).
  let gs ← gs.filterM fun g => return !(← g.isAssigned)
  if gs.isEmpty then return
  let tys ← gs.mapM fun g => do
    let ty ← instantiateMVars (← g.getType)
    if ty.hasFVar || ty.hasMVar then
      throwError "taint_decide_all: the goal mentions local hypotheses or metavariables{indentExpr ty}"
    return ty
  -- Each proposition once (the same check is often a goal several times).
  let mut uniq : Array Expr := #[]
  for t in tys do
    unless uniq.contains t do uniq := uniq.push t
  let some last := uniq.back? | return
  let conj := uniq.pop.foldr (fun t acc => mkAnd t acc) last
  let m ← gs.head!.withContext do mkFreshExprSyntheticOpaqueMVar conj
  setGoals [m.mvarId!]
  evalTactic (← `(tactic| rw_lit))
  -- `decide +kernel`, with the instance built conjunct by conjunct
  -- (instance synthesis gives up on a long conjunction).
  let g ← getMainGoal
  let conj' ← instantiateMVars (← g.getType)
  let d ← decAnd conj'
  let pf := mkApp3 (mkConst ``of_decide_eq_true) conj' d (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool)
    (mkConst ``Bool.true))
  let lemmaName ← withOptions (Elab.async.set · false) do mkAuxLemma [] conj' pf
  g.assign (mkConst lemmaName)
  -- Each proposition is a projection of the conjunction.
  let mut prfs : Array Expr := #[]
  let mut p ← instantiateMVars m
  for k in [:uniq.size] do
    if k + 1 == uniq.size then
      prfs := prfs.push p
    else
      let rest := (uniq.extract (k + 1) (uniq.size - 1)).foldr (fun t acc => mkAnd t acc) uniq.back!
      prfs := prfs.push (mkApp3 (mkConst ``And.left) uniq[k]! rest p)
      p := mkApp3 (mkConst ``And.right) uniq[k]! rest p
  for (g, t) in gs.zip tys do
    let some k := uniq.findIdx? (· == t) | throwError "taint_decide_all: lost a goal"
    g.assign prfs[k]!
  setGoals []

end VG
