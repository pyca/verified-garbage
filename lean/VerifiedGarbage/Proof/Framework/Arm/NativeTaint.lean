module

public import VerifiedGarbage.Proof.Framework.NativeTaint
public meta import VerifiedGarbage.Proof.Framework.NativeTaint
public import VerifiedGarbage.Proof.Framework.Arm.TaintMono
public meta import VerifiedGarbage.Proof.Framework.Arm.TaintMono
public import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
public meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData

/-! `native_taint_decide` for ARMv7 (`VG.Arm.taint`, `VG.Arm.taintS`): the
hint is searched in compiled code (`Arm/NativeHintData.lean`, in the
`NativeHintSearch` library) rather than interpreted, then reified into the
checked domain's constructors; the kernel checks it with `Taint.check`
exactly as for `taint_decide`. For any other domain, the elaborators of
`Proof/Framework/NativeTaint.lean` run. -/

public meta section

namespace VG.NativeHints.ArmTactic
open Lean Meta Elab Tactic

/-- Convert records field by field (`VG.Arm.Taint.T` and
`VG.NativeHints.Arm.T` have the same fields). -/
def convertState (src dst : Name) (e : Expr) : MetaM Expr := do
  let env ← getEnv
  let fields ← (getStructureFields env src).mapM fun field => do
    let some info := getFieldInfo? env src field | throwError "unknown taint field {field}"
    return mkApp (mkConst info.projFn) e
  return mkAppN (mkConst (getStructureCtor env dst).name) fields

/-- The checked domain of the goal's `Taint.check`, and whether it is
`VG.Arm.taintS` (else `VG.Arm.taint`); `none` for any other domain. -/
def armDomain? (g : MVarId) : MetaM (Option Bool) := do
  let some (_, lhs, _) := (← instantiateMVars (← g.getType)).eq? | return none
  let some chk := lhs.find? (·.isAppOfArity ``Taint.check 5) | return none
  let a := chk.getAppArgs[1]!
  if a.isConstOf ``VG.Arm.taint then return some false
  if a.isConstOf ``VG.Arm.taintS then return some true
  return none

def decideAt (summ : Bool) (chunkSize : Expr) (w : Option Term) : TacticM Unit := do
  let g ← getMainGoal
  let some (_, lhs, _) := (← instantiateMVars (← g.getType)).eq?
    | throwError "native_taint_decide: expected a checker equation"
  let some chk := lhs.find? (·.isAppOfArity ``Taint.check 5)
    | throwError "native_taint_decide: expected a taint check"
  let args := chk.getAppArgs
  let (m, a, τ, c, h) := (args[0]!, args[1]!, args[2]!, args[3]!, args[4]!)
  let nativeType := mkConst ``VG.NativeHints.Arm.T
  let state ← convertState ``VG.Arm.Taint.T ``VG.NativeHints.Arm.T τ
  let (hOf, hWeak) := if summ then
      (``VG.NativeHints.Arm.provider.hintOfSizeS, ``VG.NativeHints.Arm.provider.hintWeakOfSizeS)
    else (``VG.NativeHints.Arm.provider.hintOfSize, ``VG.NativeHints.Arm.provider.hintWeakOfSize)
  let mut hint := mkApp3 (mkConst hOf) chunkSize state c
  if let some w := w then
    unless h.isMVar do throwError "native_taint_decide: hint already supplied"
    let tT ← whnfD (mkApp2 (mkConst ``Taint.T) m a)
    let wv ← Term.elabTermEnsuringType w (← mkArrow tT tT)
    Term.synthesizeSyntheticMVarsNoPostponing
    let wv ← instantiateMVars wv
    let nw ← withLocalDeclD `τ nativeType fun t => do
      let old ← convertState ``VG.NativeHints.Arm.T ``VG.Arm.Taint.T t
      let new ← convertState ``VG.Arm.Taint.T ``VG.NativeHints.Arm.T (mkApp wv old)
      mkLambdaFVars #[t] new
    hint := mkApp4 (mkConst hWeak) chunkSize nw state c
  let hty := mkApp (mkConst ``VG.NativeHints.Hint) nativeType
  let inst ← synthInstance (mkApp (mkConst ``ToExpr [0]) hty)
  let hv ← unsafe evalExpr Expr (mkConst ``Expr)
    (mkApp3 (mkConst ``ToExpr.toExpr [0]) hty inst hint)
  if h.isMVar then h.mvarId!.assign (checkedHintExpr ``VG.NativeHints.Arm.T ``VG.Arm.Taint.T hv)
  evalTactic (← `(tactic| lit_decide))

/-- As `taintDecide`: the larger interval first, then the fallback. Any
domain but ARMv7's is left to the other elaborators. -/
def decide (w : Option Term) : TacticM Unit := do
  let some summ ← armDomain? (← getMainGoal) | throwUnsupportedSyntax
  let saved ← saveState
  try decideAt summ (mkNatLit 1024) w
  catch _ =>
    saved.restore
    decideAt summ (mkConst ``Taint.chunk) w

elab_rules : tactic
  | `(tactic| native_taint_decide) => decide none
  | `(tactic| native_taint_decide_weak $w:term) => decide (some w)

end VG.NativeHints.ArmTactic
