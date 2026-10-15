module

public import VerifiedGarbage.Proof.Framework.Taint
public meta import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Framework.NativeHintOps
public meta import VerifiedGarbage.Proof.Framework.NativeHintOps

/-! Optional native hint search (`native_taint_decide`), for the domains
with a compiled copy, by name: `X86.taint` (`Proof/Framework/NativeTaint.lean`)
and `Arm.taint` (`Proof/Framework/Arm/NativeTaint.lean`), which import them. The original taint domain and checker stay
unchanged: generated expressions must pass the same kernel check. -/

public meta section

namespace VG.NativeHints
open Lean Meta Elab Tactic

/-- Convert records field by field, so the native search can use its own
computational representation without changing the checked abstract domain. -/
private meta def convertState (src dst : Name) (e : Expr) : MetaM Expr := do
  let env ← getEnv
  let fields ← (getStructureFields env src).mapM fun field => do
    let some info := getFieldInfo? env src field | throwError "unknown taint field {field}"
    return mkApp (mkConst info.projFn) e
  return mkAppN (mkConst (getStructureCtor env dst).name) fields

private meta def decideAt (chunkSize : Expr) (w : Option Term) : TacticM Unit := do
  let g ← getMainGoal
  let some (_, lhs, _) := (← instantiateMVars (← g.getType)).eq?
    | throwError "native_taint_decide: expected a checker equation"
  let some chk := lhs.find? (·.isAppOfArity ``Taint.check 5)
    | throwError "native_taint_decide: expected a taint check"
  let args := chk.getAppArgs
  let (m, a, τ, c, h) := (args[0]!, args[1]!, args[2]!, args[3]!, args[4]!)
  -- The checked domain's state type, the native one, and the native provider.
  let some (srcT, natT, prov) :=
      if a.getAppFn.isConstOf `VG.X86.taint then
        some (`VG.X86.Taint.T, `VG.NativeHints.X86.T, `VG.NativeHints.X86.provider)
      else if a.getAppFn.isConstOf `VG.Arm.taint then
        some (`VG.Arm.Taint.T, `VG.NativeHints.Arm.T, `VG.NativeHints.Arm.provider)
      else none
    | return ← VG.taintDecideAt chunkSize "native_taint_decide" w
  -- The copy of the domain is not imported: the interpreted search.
  unless (← getEnv).contains natT && (← getEnv).contains (prov ++ `hintOfSize) do
    return ← VG.taintDecideAt chunkSize "native_taint_decide" w
  let nativeType := mkConst natT
  let state ← convertState srcT natT τ
  let mut hint := mkApp3 (mkConst (prov ++ `hintOfSize)) chunkSize state c
  if let some w := w then
    unless h.isMVar do throwError "native_taint_decide: hint already supplied"
    let tT ← whnfD (mkApp2 (mkConst ``Taint.T) m a)
    let wv ← Term.elabTermEnsuringType w (← mkArrow tT tT)
    Term.synthesizeSyntheticMVarsNoPostponing
    let wv ← instantiateMVars wv
    let nw ← withLocalDeclD `τ nativeType fun t => do
      let old ← convertState natT srcT t
      let new ← convertState srcT natT (mkApp wv old)
      mkLambdaFVars #[t] new
    hint := mkApp4 (mkConst (prov ++ `hintWeakOfSize)) chunkSize nw state c
  let hty := mkApp (mkConst ``VG.NativeHints.Hint) nativeType
  let inst ← synthInstance (mkApp (mkConst ``ToExpr [0]) hty)
  let hv ← unsafe evalExpr Expr (mkConst ``Expr)
    (mkApp3 (mkConst ``ToExpr.toExpr [0]) hty inst hint)
  if h.isMVar then h.mvarId!.assign (checkedHintExpr natT srcT hv)
  evalTactic (← `(tactic| lit_decide))

private def decide (w : Option Term) : TacticM Unit := do
  let saved ← saveState
  try decideAt (mkNatLit 1024) w
  catch _ =>
    saved.restore
    decideAt (mkConst ``Taint.chunk) w

elab "native_taint_decide" : tactic => decide none
elab "native_taint_decide_weak " w:term : tactic => decide (some w)

end VG.NativeHints
