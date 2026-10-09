import Lean.Elab.Tactic.Basic
import Lean.Meta.AppBuilder
import Lean.Meta.Tactic.Assert

/-!
# Deciding a check for each parameter set

A proof about a function over several parameter sets (ML-DSA-44, -65 and -87)
states its checks for any parameter set `p`, with what it uses of `p` as facts,
and proves them by unfolding them into arithmetic on the fields of `p` for
`omega`. A check that mentions nothing but `p` and a few bounded indices is
cheaper to decide for each parameter set: `decide_at` states it as one closed
proposition per parameter set, which the kernel evaluates in milliseconds.
-/

namespace VG.Proof.MlDsa

open Lean Elab Tactic Meta

/-- The sides of `t < c` or `t ≤ c` on `Nat`. -/
private def ineq? (t : Expr) : Option (Expr × Expr) :=
  if (t.isAppOfArity ``LT.lt 4 || t.isAppOfArity ``LE.le 4) &&
      t.appFn!.appFn!.appFn!.appArg!.isConstOf ``Nat then
    some (t.appFn!.appArg!, t.appArg!)
  else none

/-- The variables of `e`, but `p`. -/
private def varsOf (p e : Expr) : Array FVarId :=
  (collectFVars {} e).fvarIds.filter fun v => !(Expr.fvar v == p)

/-- For each variable `x` of the goal (or of its variables' bounds) with no bound `x < c` or `x ≤ c` but a hypothesis
`t < c` or `t ≤ c` whose `t` mentions `x` alone (such as `4 * x + 4 ≤ c`), adds the
bound `x ≤ c`, by `omega`; and for each variable of the goal with no bound that mentions
`p` alone but one `x < y` (or `x ≤ y`), and a bound `y < c` (or `y ≤ c`) that does, the
bound `x < c` (or `x ≤ c`). -/
private def deriveBounds (p : Expr) (g : MVarId) : TacticM (MVarId × Array FVarId) := g.withContext do
  let mut g := g
  let mut sources : Array FVarId := #[]
  let lctx ← getLCtx
  let decls ← lctx.foldlM (init := #[]) fun acc d => do
    if d.isImplementationDetail then return acc
    return acc.push (d, ineq? (← instantiateMVars d.type))
  let mut todo := varsOf p (← instantiateMVars (← g.getType))
  let mut seen : Array FVarId := #[]
  while h : todo.size > 0 do
    let x := todo[todo.size - 1]
    todo := todo.pop
    if seen.contains x then continue
    seen := seen.push x
    let direct := decls.filterMap fun (_, i) => i.bind fun (l, c) => if l == .fvar x then some c else none
    if !direct.isEmpty then
      for c in direct do todo := todo ++ varsOf p c
      continue
    for (d, i) in decls do
      let some (l, c) := i | continue
      unless varsOf p l == #[x] && !c.containsFVar x do continue
      let ty ← mkAppM ``LE.le #[.fvar x, c]
      let pf ← mkFreshExprMVar ty
      let gs ← Tactic.run pf.mvarId! (evalTactic (← `(tactic| omega)))
      unless gs.isEmpty do continue
      g := (← (← g.assert `hbound ty pf).intro1P).2
      sources := sources.push d.fvarId
      todo := todo ++ varsOf p c
      break
  -- Bounds through another variable, `x < y` and `y < c` to `x < c` (for `closed`).
  g.withContext do
  let mut g := g
  let lctx ← getLCtx
  let decls ← lctx.foldlM (init := #[]) fun acc d => do
    if d.isImplementationDetail then return acc
    let t ← instantiateMVars d.type
    match ineq? t with
    | some (.fvar x, c) => return acc.push (x, d.toExpr, t.isAppOfArity ``LT.lt 4, c)
    | _ => return acc
  for x in varsOf p (← instantiateMVars (← g.getType)) do
    if decls.any fun (y, _, _, c) => y == x && (varsOf p c).isEmpty then continue
    let some (_, hxy, sxy, y) := decls.find? fun (y, _, _, c) => y == x && c.isFVar | continue
    let some (_, hyc, syc, c) := decls.find? fun (z, _, _, c) => .fvar z == y && (varsOf p c).isEmpty
      | continue
    let (ty, pf) ← match sxy, syc with
      | true, true => pure (← mkAppM ``LT.lt #[.fvar x, c], ← mkAppM ``Nat.lt_trans #[hxy, hyc])
      | true, false => pure (← mkAppM ``LT.lt #[.fvar x, c], ← mkAppM ``Nat.lt_of_lt_of_le #[hxy, hyc])
      | false, true => pure (← mkAppM ``LT.lt #[.fvar x, c], ← mkAppM ``Nat.lt_of_le_of_lt #[hxy, hyc])
      | false, false => pure (← mkAppM ``LE.le #[.fvar x, c], ← mkAppM ``Nat.le_trans #[hxy, hyc])
    g := (← (← g.assert `hbound ty pf).intro1P).2
  return (g, sources)

/-- The variables of `e` other than `p`, with their bounds (each hypothesis `x < c` or
`x ≤ c`, whose `c` mentions `p` and other such variables; at least one for each), in an
order in which each variable comes after the variables of one of its bounds, each other
hypothesis `t < c` or `t ≤ c` a bound was derived from (`sources`), and `t = c`, `t ≠ c`
or `¬t = c` about them, after its variables: `#[x₁, h₁, x₂, h₂, h₂', …]`. With `closed`, only
the bounds that mention `p` alone, and the variables of the goal. -/
private def bounded (p : Expr) (e : Expr) (sources : Array FVarId) (closed : Bool) :
    MetaM (Array Expr) := do
  let lctx ← getLCtx
  let decls ← lctx.foldlM (init := #[]) fun acc d => do
    if d.isImplementationDetail then return acc
    match ineq? (← instantiateMVars d.type) with
    | some (l, c) => return acc.push (d.fvarId, l, c)
    | none => return acc
  -- Facts `a = b` and `a ≠ b` on `Nat`.
  let facts ← lctx.foldlM (init := #[]) fun acc d => do
    if d.isImplementationDetail then return acc
    let t ← instantiateMVars d.type
    let t := if t.isAppOfArity ``Not 1 then t.appArg! else t
    let isNat (t : Expr) := t.appFn!.appFn!.appArg!.isConstOf ``Nat
    if (t.isAppOfArity ``Eq 3 || t.isAppOfArity ``Ne 3) && isNat t then return acc.push (d.fvarId, t)
    return acc
  -- The bounds of each variable needed, until every variable in a bound has them.
  let mut todo := varsOf p e
  let mut found : Std.HashMap FVarId (Array (FVarId × Array FVarId)) := {}
  while h : todo.size > 0 do
    let x := todo[todo.size - 1]
    todo := todo.pop
    if found.contains x then continue
    let hs := decls.filterMap fun (h, l, c) =>
      if l == .fvar x && (!closed || (varsOf p c).isEmpty) then some (h, varsOf p c) else none
    if hs.isEmpty then throwError "decide_at: no bound `{mkFVar x} < c` for a variable of the goal"
    found := found.insert x hs
    for (_, vs) in hs do todo := todo ++ vs
  -- The other hypotheses about these variables.
  let bounds := found.fold (init := (∅ : Std.HashSet FVarId)) fun acc _ hs =>
    hs.foldl (fun acc (h, _) => acc.insert h) acc
  let mut pending : Array (FVarId × Array FVarId) := decls.filterMap fun (h, l, c) =>
    let vs := varsOf p l ++ varsOf p c
    if sources.contains h && vs.all found.contains then some (h, vs) else none
  pending := pending ++ facts.filterMap fun (h, t) =>
    let vs := varsOf p t
    if !vs.isEmpty && vs.all found.contains then some (h, vs) else none
  -- Place each variable once one of its bounds mentions only earlier variables, and
  -- each other hypothesis once its variables are placed.
  let mut placed : Array FVarId := #[]
  let mut out : Array Expr := #[]
  let mut rest := found.toArray
  while rest.size > 0 do
    let (ready, later) := rest.partition fun (_, hs) => hs.any fun (_, vs) => vs.all placed.contains
    if ready.isEmpty then throwError "decide_at: the bounds of the goal's variables are circular"
    for (x, hs) in ready do
      let (now, after) := hs.partition fun (_, vs) => vs.all placed.contains
      placed := placed.push x
      out := out.push (mkFVar x)
      for (h, _) in now do out := out.push (mkFVar h)
      pending := pending ++ after
    rest := later
    let (now, after) := pending.partition fun (_, vs) => vs.all placed.contains
    for (h, _) in now do out := out.push (mkFVar h)
    pending := after
  return out

/-- `decide_at hm`, for `hm : p = a ∨ p = b ∨ p = c`: decides the goal for each of `a`,
`b`, `c` and all values of the goal's other variables, each bounded by a hypothesis
`x < c` or `x ≤ c` whose `c` mentions only `p` and other such variables, as
statements `∀ x₁ < c₁, …, goal` that mention no other hypothesis. -/
elab "decide_at" hm:ident : tactic => withMainContext do
  let hmv ← getFVarFromUserName hm.getId
  -- `p = a ∨ (p = b ∨ p = c)`
  let some (p, vals) ← (do
      let t ← instantiateMVars (← inferType hmv)
      let some (_, p, a) := t.appFn!.appArg!.eq? | return none
      let t := t.appArg!
      let some (_, _, b) := t.appFn!.appArg!.eq? | return none
      let some (_, _, c) := t.appArg!.eq? | return none
      return some (p, #[a, b, c])) | throwError "decide_at: {hm} is not `p = a ∨ p = b ∨ p = c`"
  let (g, sources) ← deriveBounds p (← getMainGoal)
  -- First with bounds on `p` alone, fewer cases when the goal needs no more.
  let attempt (closed : Bool) : TacticM Unit := g.withContext do
    let vars ← bounded p (← instantiateMVars (← g.getType)) sources closed
    -- Explicit binders, which the instances of `Decidable` for bounded `∀` match.
    let rec explicit : Nat → Expr → Expr
      | n + 1, .forallE x t b _ => .forallE x t (explicit n b) .default
      | _, e => e
    let motive ← mkLambdaFVars #[p]
      (explicit vars.size (← mkForallFVars vars (← instantiateMVars (← g.getType))))
    if motive.hasFVar then throwError "decide_at: the goal mentions other hypotheses: {motive}"
    -- The statement for each value, by evaluation.
    let pfs ← vals.mapM fun v => do
      let pf ← mkFreshExprMVar (motive.beta #[v])
      let gs ← Tactic.run pf.mvarId! (evalTactic (← `(tactic| decide +kernel)))
      unless gs.isEmpty do throwError "decide_at: goals remain"
      return pf
    -- `motive p`, along `hm`.
    let along (e : Expr) (pf : Expr) : MetaM Expr := do mkEqNDRec motive pf (← mkEqSymm e)
    let t ← instantiateMVars (← inferType hmv)
    let tbc := t.appArg!
    let caseBC ← withLocalDeclD `h tbc fun h => do
      let l ← withLocalDeclD `e tbc.appFn!.appArg! fun e => do mkLambdaFVars #[e] (← along e pfs[1]!)
      let r ← withLocalDeclD `e tbc.appArg! fun e => do mkLambdaFVars #[e] (← along e pfs[2]!)
      mkLambdaFVars #[h] (← mkAppOptM ``Or.elim #[none, none, motive.beta #[p], h, l, r])
    let caseA ← withLocalDeclD `e t.appFn!.appArg! fun e => do mkLambdaFVars #[e] (← along e pfs[0]!)
    let pfp ← mkAppOptM ``Or.elim #[none, none, motive.beta #[p], hmv, caseA, caseBC]
    g.assign (mkAppN pfp vars)
    replaceMainGoal []
  attempt true <|> attempt false

end VG.Proof.MlDsa
