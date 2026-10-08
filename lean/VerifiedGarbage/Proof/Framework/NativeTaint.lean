import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.X86.NativeHintData

/-! Optional native hint search. The original taint domain and checker stay
unchanged: generated expressions must pass the same kernel check. -/
namespace VG.NativeHints
open Lean Meta Elab Tactic

/-- Convert records field by field, so the native search can use its own
computational representation without changing the checked abstract domain. -/
private def convertState (src dst : Name) (e : Expr) : MetaM Expr := do
  let env ← getEnv
  let fields ← (getStructureFields env src).mapM fun field => do
    let some info := getFieldInfo? env src field | throwError "unknown taint field {field}"
    return mkApp (mkConst info.projFn) e
  return mkAppN (mkConst (getStructureCtor env dst).name) fields

private def decideAt (chunkSize : Nat) (w : Option Term) : TacticM Unit := do
  let g ← getMainGoal
  let some (_, lhs, _) := (← instantiateMVars (← g.getType)).eq?
    | throwError "native_taint_decide: expected a checker equation"
  let some chk := lhs.find? (·.isAppOfArity ``Taint.check 5)
    | throwError "native_taint_decide: expected a taint check"
  let args := chk.getAppArgs
  let (m, a, τ, c, h) := (args[0]!, args[1]!, args[2]!, args[3]!, args[4]!)
  unless a.getAppFn.isConstOf ``VG.X86.taint do
    return ← VG.taintDecideAt chunkSize "native_taint_decide" w
  let nativeType := mkConst ``VG.NativeHints.X86.T
  let state ← convertState ``VG.X86.Taint.T ``VG.NativeHints.X86.T τ
  let mut hint := mkApp3 (mkConst ``VG.NativeHints.X86.provider.hintOfSize)
    (mkNatLit chunkSize) state c
  if let some w := w then
    unless h.isMVar do throwError "native_taint_decide: hint already supplied"
    let tT ← whnfD (mkApp2 (mkConst ``Taint.T) m a)
    let wv ← Term.elabTermEnsuringType w (← mkArrow tT tT)
    Term.synthesizeSyntheticMVarsNoPostponing
    let wv ← instantiateMVars wv
    let nw ← withLocalDeclD `τ nativeType fun t => do
      let old ← convertState ``VG.NativeHints.X86.T ``VG.X86.Taint.T t
      let new ← convertState ``VG.X86.Taint.T ``VG.NativeHints.X86.T (mkApp wv old)
      mkLambdaFVars #[t] new
    hint := mkApp4 (mkConst ``VG.NativeHints.X86.provider.hintWeakOfSize)
      (mkNatLit chunkSize) nw state c
  let hty := mkApp (mkConst ``VG.NativeHints.Hint) nativeType
  let inst ← synthInstance (mkApp (mkConst ``ToExpr [0]) hty)
  let hv ← unsafe evalExpr Expr (mkConst ``Expr)
    (mkApp3 (mkConst ``ToExpr.toExpr [0]) hty inst hint)
  if h.isMVar then h.mvarId!.assign (checkedHintExpr ``VG.NativeHints.X86.T ``VG.X86.Taint.T hv)
  evalTactic (← `(tactic| lit_decide))

private def decide (w : Option Term) : TacticM Unit := do
  let saved ← saveState
  try decideAt 1024 w
  catch _ =>
    saved.restore
    decideAt Taint.chunk w

elab "native_taint_decide" : tactic => decide none
elab "native_taint_decide_weak " w:term : tactic => decide (some w)

end VG.NativeHints
