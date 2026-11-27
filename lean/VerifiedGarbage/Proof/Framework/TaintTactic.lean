module

public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Meta.Eval
public import VerifiedGarbage.Proof.Framework.Lit
public meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# The tactics `taint_decide` and `taint_decide_weak`

They name the analysis (`Proof/Framework/Taint.lean`, which imports this
module) by its names alone, so that this module imports only Lean core and is
compiled (`NativeTactics` in `lean/lakefile.toml`).
-/

public meta section

namespace VG

/-- The ISA `M`, as the tactics name it in the code they compile for the search of a hint:
`isaC` for `isa`. The search only needs its types, but the compiler would compile its functions
at each check: an `abbrev` is inlined wherever it is named. -/
def Taint.compiled (M : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let .const (.str p "isa") [] := M | return M
  return if (← Lean.getEnv).contains (p.str "isaC") then Lean.mkConst (p.str "isaC") else M

open Lean Meta Elab Tactic in
/-- `taint_decide`, with the taints of the hint weakened by `w`, if given. -/
def taintDecideAt (chunkSize : Expr) (name : String) (w : Option Term) : TacticM Unit := do
  let g ← getMainGoal
  let some (_, lhs, _) := (← instantiateMVars (← g.getType)).eq?
    | throwError "{name}: the goal is not an equation about `Taint.check A τ c h`"
  let some chk := lhs.find? (·.isAppOfArity `VG.Taint.check 5)
    | throwError "{name}: the goal is not an equation about `Taint.check A τ c h`"
  let args := chk.getAppArgs
  let (m, a, τ, c, h) := (args[0]!, args[1]!, args[2]!, args[3]!, args[4]!)
  let tT ← whnfD (mkApp2 (mkConst `VG.Taint.T) m a)
  let mut hint := mkApp5 (mkConst `VG.Taint.hintOfSize) (← Taint.compiled m) a chunkSize τ c
  if let some w := w then
    unless h.isMVar do throwError "{name}: the hint is already given"
    let wv ← Term.elabTermEnsuringType w (← mkArrow tT tT)
    Term.synthesizeSyntheticMVarsNoPostponing
    hint := mkApp4 (mkConst `VG.Taint.Hint.map) tT tT (← instantiateMVars wv) hint
  let instT ← synthInstance (mkApp (mkConst ``ToExpr [0]) tT)
  let hv ← unsafe VG.Lit.evalOnce Expr (mkConst ``Expr) (mkApp3 (mkConst `VG.Taint.Hint.toExprNS) tT instT hint)
  if h.isMVar then h.mvarId!.assign hv
  -- The kernel evaluates the literal of any code that has one (`materialize_code`).
  evalTactic (← `(tactic| lit_decide))

open Lean Elab Tactic in
/-- Try larger hint intervals, retaining the original bounded check as a fallback. -/
def taintDecide (name : String) (w : Option Term) : TacticM Unit := do
  let saved ← saveState
  try
    taintDecideAt (mkNatLit 1024) name w
  catch _ =>
    -- Discard the failed attempt's hint assignment before constructing another.
    saved.restore
    taintDecideAt (mkConst `VG.Taint.chunk) name w

/-- Proves `(Taint.check A τ c ?hint).isSome = true`, or any decidable
equation whose left side contains `Taint.check A τ c ?hint` (e.g. a property of
the resulting taint): computes the hint (`Taint.hintOf`, in compiled code) and
then has the kernel evaluate the goal, with each code constant that has a
literal (`materialize_code`) rewritten to it. The domain `A.T` needs a `ToExpr`
instance. -/
elab "taint_decide" : tactic => taintDecide "taint_decide" none

/-- `taint_decide`, with the taints of the hint weakened by `w : A.T → A.T`
(computed in compiled code, like the hint).

`Taint.check` accepts any hint whose taints are at most what the analysis
computes (`le`): at every `chunkSize` instructions of a block, between the parts
of a `seq` and at every loop, the analysis continues from the hint's taint.
So a hint may forget public facts that the rest of the code never uses. The
kernel is a slow evaluator, and the cost of each instruction grows with the
size of the taint (e.g. the x86 analysis's list of public memory slots, which
a table of constants stored on the stack fills), so forgetting them can make
the kernel's check several times faster. Nothing about `w` needs to be sound:
a hint it weakens too much only makes the check fail. -/
elab "taint_decide_weak " w:term : tactic => taintDecide "taint_decide_weak" (some w)

end VG
