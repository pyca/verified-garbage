module

public import VerifiedGarbage.Proof.Framework.Lit
public meta import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.TaintTactic
public meta import VerifiedGarbage.Proof.Framework.TaintTactic
public meta import Lean.Meta.Eval
public meta import Lean.Elab.Tactic.Basic

/-!
# The code of a check, as a literal

`taint_decide` has the kernel evaluate the literal of any code that has one
(`rw_lit`), but not of code it reaches through a structure with proofs about
it (`Lit.reaches`: rewriting inside one would change the types of its
proofs): the code of a registration or the functions of a variant (`MdHash`, `StreamFn`). The kernel then builds the
code from the functions that generate it, and what it walks are their
terms: two instructions that are the same after evaluation are different
terms, each met for the first time (x86-64's `RTaint.stepFn1K`, a third of a
millisecond), and no step is found again. Here the code of such a check is evaluated in
compiled code and the check stated of that literal, with the literals of the
functions it calls (as `materialize_code` writes one): the kernel compares
the code with it once, by evaluation, and the analysis walks a literal. A
check of such code is proven by `taint_decide_lit`, not `taint_decide`, and by
`lit_decide_lit`, not `lit_decide`.
-/

@[expose] public section

namespace VG.LitHidden

open Lean Meta Elab Tactic

/-- Whether the closed code `c` is reached through a structure with proofs
among its fields, which `rw_lit` does not unfold. -/
meta def hidden (c : Expr) : MetaM Bool := do
  if c.hasLooseBVars || c.hasFVar || c.hasMVar then return false
  let env ← getEnv
  for k in c.getUsedConstants do
    if let some info := env.find? k then
      for t in info.type.getForallBody.getUsedConstants do
        if ← Lit.hasProofFields (mkConst t) then return true
  return false

/-- Whether the code `c` is `hidden` and names no literal: code that
`rw_lit` leaves, all of it, to the functions that generate it. (Code of
which it finds the literals of some functions stays as it leaves it: the
literal of ML-DSA's key preparation, whose polynomial arithmetic it does not
find, gained nothing and cost a comparison.) -/
meta def hiddenCode (c : Expr) : MetaM Bool := do
  if c.getUsedConstants.any (· matches .str _ "lit") then return false
  hidden c

/-- For `v`, the value of the closed code `c : ty` (`Lit.evalCodes`): `c` as a literal, calling
the literals of the code materialized so far (`lits`; as `Lit.materialize`
writes `N.lit`), and a proof that `c` is that literal: by evaluation, then each
function called rewritten to its literal. -/
meta def codeLit (ty : Expr) (lits : Std.HashMap Expr Name) (c v : Expr) : MetaM (Expr × Expr) := do
  let (abs, gs) ← Lit.abstractToLits lits v
  let lhss ← gs.mapM Lit.lhsOf
  -- `abs` with the `i`-th callee (marked `.bvar (1000000 + i)`) replaced by `f i`.
  let fill (f : Nat → Expr) : Expr :=
    abs.replace fun e => match e with
      | .bvar k => if 1000000 ≤ k then some (f (k - 1000000)) else none
      | _ => none
  let eqTy (rhs : Expr) := mkApp3 (mkConst ``Eq [1]) ty c rhs
  -- `c = abs[callees]` by evaluation, then each callee rewritten to its literal.
  let mut prf := mkApp2 (mkConst ``Eq.refl [1]) ty c
  for i in [0:gs.size] do
    let motive := Expr.lam `x ty
      (eqTy ((fill fun j => if j < i then mkConst (gs[j]! ++ `lit)
        else if j == i then .bvar 0 else lhss[j]!))) .default
    prf := mkApp4 (mkConst ``Eq.mp [0])
      (mkApp motive lhss[i]!) (mkApp motive (mkConst (gs[i]! ++ `lit)))
      (mkApp6 (mkConst ``congrArg [1, 1]) ty (mkSort 0) lhss[i]!
        (mkConst (gs[i]! ++ `lit)) motive (mkConst (gs[i]! ++ `lit_eq))) prf
  return (ShareCommon.shareCommon' (fill fun i => mkConst (gs[i]! ++ `lit)), ShareCommon.shareCommon' prf)

/-- The code of `e`, of the largest subterms that are code, that is reached
through a structure with proofs (`hidden`). -/
meta def hiddenCodes (e : Expr) : MetaM (Array Expr) :=
  return (← (go e).run ({}, #[])).2.2
where
  go (e : Expr) : StateT (Std.HashSet Expr × Array Expr) MetaM Unit := do
    -- each subterm once
    if (← get).1.contains e then return
    modify fun (seen, acc) => (seen.insert e, acc)
    if !e.hasLooseBVars && !e.hasFVar && !e.hasMVar then
      if (← whnfR (← inferType e)).isAppOfArity ``Code 2 then
        if ← hidden e then modify fun (seen, acc) => (seen, acc.push e)
        return
    match e with
    | .app f a => go f; go a
    | .lam _ t b _ | .forallE _ t b _ => go t; go b
    | .mdata _ b | .proj _ _ b => go b
    | _ => return

/-- The goal, with the codes `cs` in it replaced by their literals (`codeLit`): evaluated
together, and rewritten at once. -/
meta def rwCodeLits (cs : Array Expr) : TacticM Unit := do
  let some c₀ := cs[0]? | return
  let g ← getMainGoal
  let tgt ← instantiateMVars (← g.getType)
  let ty ← inferType c₀
  let codeTy ← whnfD ty
  unless codeTy.isAppOfArity ``Code 2 do throwError "{c₀} is not code: {ty}"
  for c in cs do
    unless ← isDefEq (← inferType c) ty do throwError "{c} is not code of the type {ty}"
  let vs ← Lit.evalCodes (← whnfD codeTy.appFn!.appArg!) (← whnfD codeTy.appArg!) cs
  let lits ← Lit.expandedLits ty
  let mut ls := #[]
  for c in cs, v in vs do ls := ls.push (← codeLit ty lits c v)
  let k := cs.size
  let idx : Std.HashMap Expr Nat := cs.zipIdx.foldl (fun m (c, i) => m.insert c i) {}
  let put (f : Nat → Expr) : Expr := tgt.replace fun t => idx[t]?.map f
  -- The goal as a function of the codes: at them, and at their literals, by congruence.
  let xs ← cs.mapM fun _ => mkFVar <$> mkFreshFVarId
  let F := cs.foldr (fun _ b => Expr.lam `y ty b .default) ((put (xs[·]!)).abstract xs)
  let mut l := F
  let mut r := F
  let mut prf := mkApp2 (mkConst ``Eq.refl [1]) (mkSort 0) tgt
  for i in [0:k] do
    let (c', p) := ls[i]!
    let B := (List.range (k - 1 - i)).foldl (fun b _ => mkForall `y .default ty b) (mkSort 0)
    prf := if i == 0 then mkApp6 (mkConst ``congrArg [1, 1]) ty B cs[i]! c' F p
      else mkAppN (mkConst ``congr [1, 1]) #[ty, B, l, r, cs[i]!, c', prf, p]
    l := mkApp l cs[i]!
    r := mkApp r c'
  replaceMainGoal [← g.replaceTargetEq (put fun i => (ls[i]!).1) prf]

/-- `taint_decide` (`VG.taintDecideAt`), but that after `rw_lit` a check of
code that `rw_lit` has left to the functions that generate it (`hiddenCode`)
is stated of the code's literal (`codeLit`) before the kernel evaluates it. -/
meta def taintDecideLit (chunkSize : Expr) : TacticM Unit := do
  let g ← getMainGoal
  let some chk := (← instantiateMVars (← g.getType)).find? (·.isAppOfArity `VG.Taint.check 5)
    | throwError "taint_decide_lit: the goal is not an equation about `Taint.check A τ c h`"
  let args := chk.getAppArgs
  let (m, a, τ, c, h) := (args[0]!, args[1]!, args[2]!, args[3]!, args[4]!)
  unless h.isMVar do throwError "taint_decide_lit: the hint is already given"
  let tT ← whnfD (mkApp2 (mkConst `VG.Taint.T) m a)
  let instT ← synthInstance (mkApp (mkConst ``ToExpr [0]) tT)
  let hv ← unsafe VG.Lit.evalOnce Expr (mkConst ``Expr) (mkApp3 (mkConst `VG.Taint.Hint.toExprNS) tT instT
    (mkApp5 (mkConst `VG.Taint.hintOfSize) (← VG.Taint.compiled m) a chunkSize τ c))
  h.mvarId!.assign hv
  evalTactic (← `(tactic| rw_lit))
  let tgt ← instantiateMVars (← getMainTarget)
  let some chk := tgt.find? (·.isAppOfArity `VG.Taint.check 5)
    | throwError "taint_decide_lit: the goal is not an equation about `Taint.check A τ c h`"
  let c := chk.getArg! 3
  if ← hiddenCode c then rwCodeLits #[c]
  evalTactic (← `(tactic| (kernel_rw; decide +kernel)))

/-- `lit_decide_lit`: `lit_decide` for a check of code that `rw_lit` cannot
see (the functions of a variant), which it states of the code's literal, as
`taint_decide_lit` does, before the kernel evaluates it. On any other code it
is `lit_decide`. -/
elab "lit_decide_lit" : tactic => withMainContext do
  rwCodeLits (← hiddenCodes (← instantiateMVars (← getMainTarget)))
  evalTactic (← `(tactic| lit_decide))

/-- `taint_decide_lit`: `taint_decide` for a check of
code that `rw_lit` cannot see (a registration's code, the functions of a
variant), which it states of the code's literal before the kernel evaluates
it. On any
other code it is `taint_decide`. -/
elab "taint_decide_lit" : tactic => withMainContext do
  let saved ← saveState
  try
    taintDecideLit (mkNatLit 1024)
  catch _ =>
    -- Discard the failed attempt's hint assignment before constructing another.
    saved.restore
    taintDecideLit (mkConst `VG.Taint.chunk)

end VG.LitHidden
