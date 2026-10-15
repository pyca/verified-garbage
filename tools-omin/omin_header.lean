public meta import Lean
public meta import VerifiedGarbage.Proof.Framework.Omega

meta section
open Lean Elab Tactic Meta in
elab "omega_min" : tactic => do
  let ps := (← getFileMap).toPosition ((← getRef).getPos?.getD 0)
  let at_ := s!"@{ps.line}:{ps.column} "
  let (rel, all) ← withMainContext do
    let all ← (← getLocalHyps).filterM fun h => do VG.Omega.isArithProp (← inferType h)
    pure (← VG.Omega.relevantFacts all (← getMainTarget), all)
  let tryWith (fs : Array Expr) : TacticM Bool := do
    let s ← saveState
    try VG.Omega.omegaFromFacts fs; s.restore; return true
    catch _ => s.restore; return false
  let start ← if ← tryWith rel then pure (some rel) else if ← tryWith all then pure (some all) else pure none
  let some facts := start | logInfo m!"OMIN-KEEP{at_}fail"; VG.Omega.omegaArith; return
  let mut cur := facts
  let mut i := 0
  while i < cur.size do
    let cand := cur.eraseIdx! i
    if ← tryWith cand then cur := cand else i := i + 1
  let names ← withMainContext do
    let lctx ← getLCtx
    cur.mapM fun f => do
      let n := (lctx.get! f.fvarId!).userName
      let dup := (lctx.getFVarIds.filter fun d => (lctx.get! d).userName == n).size > 1
      pure (if n.hasMacroScopes || dup then none else some n)
  if names.any (·.isNone) then logInfo m!"OMIN-KEEP{at_}{cur.size}"
  else logInfo m!"OMIN{at_}[{", ".intercalate (names.toList.map fun n => n.get!.toString)}]"
  VG.Omega.omegaFromFacts cur
end
set_option maxHeartbeats 0

