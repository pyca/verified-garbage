module

public import VerifiedGarbage.Proof.Framework.Taint
public meta import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Framework.TaintSum
public meta import VerifiedGarbage.Proof.Framework.TaintSum
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

/-! ## With summaries -/

/-- The domains whose frames have a compiled copy: the checked domain's state
type, the copy's, and the copy's provider. -/
private meta def frameCopy? (a : Expr) : MetaM (Option (Name × Name × Name)) := do
  let some r :=
      if a.getAppFn.isConstOf `VG.X86.taint then
        some (`VG.X86.Taint.T, `VG.NativeHints.X86.T, `VG.NativeHints.X86.provider)
      else none
    | return none
  let env ← getEnv
  return if env.contains r.2.1 && env.contains (r.2.2 ++ `hintReport) then some r else none

/-- `Taint.codeBeq` of `M` (in compiled code: `NativeHints.codeBeq`), if `M`
has a `Taint.CodeEq` instance for `same` (as `TaintSum.sameFn` asks), or for
`body`; otherwise none. -/
private meta def codeFn (M : Expr) (needCodeEq : Bool) : MetaM Expr := do
  let P := mkApp (mkConst ``Prog) M
  let none := Expr.lam `a P (.lam `b P (mkConst ``Bool.false) .default) .default
  try
    if needCodeEq then discard <| synthInstance (mkApp (mkConst ``Taint.CodeEq) M)
    let I ← whnfD (mkApp (mkConst ``ISA.Instr) M)
    let C ← whnfD (mkApp (mkConst ``ISA.Cond) M)
    let bi ← synthInstance (mkApp (mkConst ``BEq [0]) I)
    let bc ← synthInstance (mkApp (mkConst ``BEq [0]) C)
    return mkApp4 (mkConst ``VG.NativeHints.codeBeq) I C bi bc
  catch _ => return none

/-- `TaintSum.hintChecked`, with the domain's compiled copy. -/
private meta def hintCheckedNative (who : String) (M c : Expr) (ss : List Expr) (τ : Expr)
    (srcT natT prov : Name) : MetaM Expr := do
  let natTy := mkConst natT
  let sTy ← mkAppM ``Prod #[mkApp (mkConst ``Prog) M,
    ← mkAppM ``Prod #[natTy, ← mkAppM ``Prod #[natTy, natTy]]]
  -- The summaries, their taints converted to the copy's.
  let conv (e : Expr) := convertState srcT natT e
  let nss ← ss.mapM fun s => do
    let c' ← mkAppM ``Prod.fst #[s]
    let r ← mkAppM ``Prod.snd #[s]
    let pre ← conv (← mkAppM ``Prod.fst #[r])
    let r ← mkAppM ``Prod.snd #[r]
    let post ← conv (← mkAppM ``Prod.fst #[r])
    let F ← conv (← mkAppM ``Prod.snd #[r])
    mkAppM ``Prod.mk #[c', ← mkAppM ``Prod.mk #[pre, ← mkAppM ``Prod.mk #[post, F]]]
  let S ← mkListLit sTy nss
  let hTy := mkApp (mkConst ``VG.NativeHints.SHint) natTy
  let phTy ← mkAppM ``Prod #[natTy, hTy]
  let repTy := mkApp (mkConst ``List [0]) (mkConst ``String)
  let r := mkAppN (mkConst (prov ++ `hintReport)) #[S, ← codeFn M true, ← codeFn M false, ← conv τ, c]
  let e ← withLetDecl `r (← mkAppM ``Prod #[phTy, repTy]) r fun r => do
    let ph ← mkAppM ``ToExpr.toExpr #[← mkAppM ``Prod.snd #[← mkAppM ``Prod.fst #[r]]]
    mkLetFVars #[r] (← mkAppM ``Prod.mk #[ph, ← mkAppM ``Prod.snd #[r]])
  let ty ← mkAppM ``Prod #[mkConst ``Expr, repTy]
  let (h, missed) ← unsafe evalExpr (Expr × List String) ty e
  unless missed.isEmpty do
    throwError "{who}: the calls {missed.eraseDups} are analysed in full, although a summary \
      of the same function (by its name or its code) is given: its `pre` does not hold \
      there, or it is stated about another name or code"
  -- The copy's constructors renamed to the checked domain's.
  let h := checkedHintExpr natT srcT h
  return h.replace fun t => match t with
    | .const n us =>
      let n' := renamePrefix `VG.NativeHints.SHint `VG.Taint.SHint n
      if n' == n then none else some (.const n' us)
    | _ => none

open TaintSum in
/-- `taint_decide_sum`, with the hint computed by the domain's compiled copy
(for `X86.taint`, importing `Proof/Framework/NativeTaint.lean`), checked by the
kernel as `taint_decide_sum`'s; the interpreted search for any other domain. -/
elab "native_taint_decide_sum " "[" ls:ident,* "]" : tactic => withMainContext do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let some (_, body) := ty.app2? ``Exists
    | throwError "native_taint_decide_sum: the goal is not `∃ h, (Taint.check A τ c h).isSome = true`"
  let .lam _ _ b _ := body
    | throwError "native_taint_decide_sum: the goal is not `∃ h, (Taint.check A τ c h).isSome = true`"
  let some chk := b.find? (·.isAppOfArity ``Taint.check 5)
    | throwError "native_taint_decide_sum: the goal is not `∃ h, (Taint.check A τ c h).isSome = true`"
  let args := chk.getAppArgs
  let (M, A, τ, c) := (args[0]!, args[1]!, args[2]!, args[3]!)
  let names ← ls.getElems.mapM fun l => realizeGlobalConstNoOverloadWithInfo l
  let (S, hS) ← summaries M A names
  let hint ← match ← frameCopy? A with
    | some (srcT, natT, prov) =>
      let ss ← names.toList.mapM fun l => do
        return (← instantiateMVars (← inferType (mkConst l))).getArg! 3
      hintCheckedNative "native_taint_decide_sum" M c ss τ srcT natT prov
    | none =>
      let fr ← synthInstance (mkApp2 (mkConst ``Taint.Frame) M A)
      pure (← hintChecked "native_taint_decide_sum" M A fr S τ c).2
  proveWith M A S hS c ``Taint.exists_check_of_checkSum #[τ] hint

end VG.NativeHints
