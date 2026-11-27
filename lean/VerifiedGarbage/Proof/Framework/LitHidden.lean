module

public import VerifiedGarbage.Proof.Framework.Lit
public meta import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Taint
public meta import VerifiedGarbage.Proof.Framework.Taint
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

/-- The closed code `c` as a literal, calling the literals of the code
materialized so far (as `Lit.materialize` writes `N.lit`), and a proof that
`c` is that literal: by evaluation, then each function called rewritten to
its literal. -/
meta def codeLit (c : Expr) : MetaM (Expr × Expr) := do
  let ty ← inferType c
  let codeTy ← whnfD ty
  unless codeTy.isAppOfArity ``Code 2 do throwError "taint_decide: {c} is not code: {ty}"
  let codeTy := mkApp2 (mkConst ``Code) (← whnfD codeTy.appFn!.appArg!) (← whnfD codeTy.appArg!)
  let v ← Lit.evalCode codeTy.appFn!.appArg! codeTy.appArg! c
  let (abs, gs) ← Lit.abstractToLits ty v
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
meta partial def hiddenCodes (e : Expr) (acc : Array Expr := #[]) : MetaM (Array Expr) := do
  if !e.hasLooseBVars && !e.hasFVar && !e.hasMVar then
    if (← whnfR (← inferType e)).isAppOfArity ``Code 2 then
      return if !acc.contains e && (← hidden e) then acc.push e else acc
  match e with
  | .app f a => hiddenCodes a (← hiddenCodes f acc)
  | .lam _ t b _ | .forallE _ t b _ => hiddenCodes b (← hiddenCodes t acc)
  | .mdata _ b | .proj _ _ b => hiddenCodes b acc
  | _ => return acc

/-- The goal, with the code `c` in it replaced by its literal (`codeLit`). -/
meta def rwCodeLit (c : Expr) : TacticM Unit := do
  let g ← getMainGoal
  let tgt ← instantiateMVars (← g.getType)
  let (lit, prf) ← codeLit c
  let ty ← inferType c
  let motive ← withLocalDeclD `y ty fun y =>
    mkLambdaFVars #[y] (tgt.replace fun t => if t == c then some y else none)
  replaceMainGoal [← g.replaceTargetEq (tgt.replace fun t => if t == c then some lit else none)
    (mkApp6 (mkConst ``congrArg [1, 1]) ty (mkSort 0) c lit motive prf)]

/-- `taint_decide` (`VG.taintDecideAt`), but that after `rw_lit` a check of
code that `rw_lit` has left to the functions that generate it (`hiddenCode`)
is stated of the code's literal (`codeLit`) before the kernel evaluates it. -/
meta def taintDecideLit (chunkSize : Expr) : TacticM Unit := do
  let g ← getMainGoal
  let some chk := (← instantiateMVars (← g.getType)).find? (·.isAppOfArity ``VG.Taint.check 5)
    | throwError "taint_decide_lit: the goal is not an equation about `Taint.check A τ c h`"
  let args := chk.getAppArgs
  let (m, a, τ, c, h) := (args[0]!, args[1]!, args[2]!, args[3]!, args[4]!)
  unless h.isMVar do throwError "taint_decide_lit: the hint is already given"
  let tT ← whnfD (mkApp2 (mkConst ``VG.Taint.T) m a)
  let instT ← synthInstance (mkApp (mkConst ``ToExpr [0]) tT)
  let hv ← unsafe evalExpr Expr (mkConst ``Expr) (mkApp3 (mkConst ``VG.Taint.Hint.toExprNS) tT instT
    (mkApp5 (mkConst ``VG.Taint.hintOfSize) m a chunkSize τ c))
  h.mvarId!.assign hv
  evalTactic (← `(tactic| rw_lit))
  let tgt ← instantiateMVars (← getMainTarget)
  let some chk := tgt.find? (·.isAppOfArity ``VG.Taint.check 5)
    | throwError "taint_decide_lit: the goal is not an equation about `Taint.check A τ c h`"
  let c := chk.getArg! 3
  if ← hiddenCode c then rwCodeLit c
  evalTactic (← `(tactic| (kernel_rw; decide +kernel)))

/-- `lit_decide_lit`: `lit_decide` for a check of code that `rw_lit` cannot
see (the functions of a variant), which it states of the code's literal, as
`taint_decide_lit` does, before the kernel evaluates it. On any other code it
is `lit_decide`. -/
elab "lit_decide_lit" : tactic => withMainContext do
  for c in ← hiddenCodes (← instantiateMVars (← getMainTarget)) do rwCodeLit c
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
    taintDecideLit (mkConst ``VG.Taint.chunk)

end VG.LitHidden
