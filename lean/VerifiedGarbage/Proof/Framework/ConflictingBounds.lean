module

public meta import Lean

/-!
# Conflicting natural-number bounds in proof hypotheses

The build plugin checks named theorems when their proof module finishes elaborating.
It checks chains of `<`, `≤`, and `=` between natural-number variables and numerals,
and literal bounds on compound expressions. A negated disjunction such as
`¬ PreLen fold len` can supply a bound. For a lemma deliberately about
an unreachable case, explain why and mark the theorem `@[intentional_vacuity]`.
-/

public meta section

namespace VG.ConflictingBounds

open Lean Meta Elab Command

private initialize intentionalVacuity : TagAttribute ←
  registerTagAttribute `intentional_vacuity "This theorem deliberately describes an impossible case."

/-- The original comparison and a proof obtained from a theorem hypothesis. -/
private structure Comparison where
  rel : Expr
  lhs : Expr
  rhs : Expr
  negated : Bool
  proof : Expr

private def Comparison.prop (c : Comparison) (lhs rhs : Expr) : Expr :=
  let p := mkApp2 c.rel lhs rhs
  if c.negated then mkNot p else p

/-- Only treat a numeral as a literal when it uses the standard Nat instance. -/
private def isLiteral (e : Expr) : Bool := Id.run do
  let_expr OfNat.ofNat _ n inst := e | return e.rawNatLit?.isSome
  return n.rawNatLit?.isSome && inst == mkApp (mkConst ``instOfNatNat) n

private def comparison? (p proof : Expr) (negated : Bool) : Option Comparison := do
  let .app (.app rel lhs) rhs := p | none
  let simple := (lhs.isFVar || isLiteral lhs) && (rhs.isFVar || isLiteral rhs)
  match rel.getAppFnArgs with
  | (``Eq, #[ty]) => guard (ty.isConstOf ``Nat && simple && !negated)
  | (op, #[ty, inst]) =>
    guard (ty.isConstOf ``Nat && ((op == ``LT.lt && inst.isConstOf ``instLTNat) ||
                                 (op == ``LE.le && inst.isConstOf ``instLENat)))
    guard (simple || isLiteral lhs || isLiteral rhs)
  | _ => none
  return ⟨rel, lhs, rhs, negated, proof⟩

private def comparisons (hyp : Expr) : MetaM (Array Comparison) := do
  let type ← inferType hyp
  if let some c := comparison? type hyp false then return #[c]
  let_expr Not p := type | return #[]
  -- Unfold one predicate abbreviation, without evaluating an arbitrary proposition.
  let p ← match (← getEnv).find? (p.getAppFn.constName?.getD .anonymous) with
    | some (.defnInfo d) => if d.hints.isAbbrev then pure ((← delta? p).getD p) else pure p
    | _ => pure p
  if let some c := comparison? p hyp true then return #[c]
  let_expr Or lhs rhs := p | return #[]
  let mut result := #[]
  for (side, intro) in [(lhs, ``Or.inl), (rhs, ``Or.inr)] do
    if let some c := comparison? side hyp true then
      let proof ← withLocalDeclD `h side fun h =>
        mkLambdaFVars #[h] (mkApp hyp (mkApp3 (mkConst intro) lhs rhs h))
      result := result.push { c with proof }
  return result

private def conflict? (type : Expr) : MetaM (Option MessageData) :=
  forallTelescope type fun xs _ => do
    let facts := (← xs.mapM comparisons).flatten
    if facts.isEmpty then return none
    -- Treat a compound operand such as `L s` as one unknown Nat. The solver
    -- sees its bounds, but never expands the expression or its arithmetic.
    let mut terms := #[]
    for c in facts do
      for e in #[c.lhs, c.rhs] do
        unless e.isFVar || isLiteral e || terms.contains e do terms := terms.push e
    withLocalDeclsDND (terms.map fun _ => (`x, mkConst ``Nat)) fun vars => do
      let abstractTerm (e : Expr) := (terms.idxOf? e).map (vars[·]!) |>.getD e
      let assumptions := facts.map fun c => (`h, c.prop (abstractTerm c.lhs) (abstractTerm c.rhs))
      withLocalDeclsDND assumptions fun hs => do
        let goal ← mkFreshExprMVar (mkConst ``False)
        try
          Elab.Tactic.Omega.omega hs.toList goal.mvarId! {
            splitDisjunctions := false, splitNatSub := false, splitNatAbs := false, splitMinMax := false }
        catch ex =>
          if (← ex.toMessageData.toString).startsWith "omega could not prove the goal" then return none
          throw ex
        let proof ← instantiateMVars goal
        if proof.hasMVar || proof.hasSorry then throwError "unfinished conflicting-bounds proof"
        let general ← mkLambdaFVars (vars ++ hs) proof
        let witness := mkAppN (mkAppN general terms) (facts.map (·.proof))
        checkWithKernel (← mkLambdaFVars xs (mkExpectedPropHint witness (mkConst ``False)))
        let mut used := #[]
        for h in hs, c in facts do
          if proof.containsFVar h.fvarId! then used := used.push m!"{c.prop c.lhs c.rhs}"
        return some (← addMessageContext (MessageData.joinSep used.toList ", "))

/-- Audit the current module's named theorems using their original source positions. -/
def checkModule : CommandElabM Unit := do
  let env ← getEnv
  let fm ← getFileMap
  for (n, ranges) in declRangeExt.toPersistentEnvExtension.getState env do
    let name := privateToUserName n
    if name.isInternal || intentionalVacuity.hasTag env n then continue
    let some (.thmInfo thm) := env.find? n | continue
    let conflict ← liftTermElabM <| tryCatchRuntimeEx (withCurrHeartbeats <| conflict? thm.type) fun ex =>
      if ex.isMaxHeartbeat then pure none else throw ex
    if let some conflict := conflict then
      let pos := ranges.selectionRange
      let ref := Syntax.ofRange ⟨fm.ofPosition pos.pos, fm.ofPosition pos.endPos⟩
      logErrorAt ref m!"conflicting bounds in {name}: {conflict}"

initialize addModuleLinter { run := fun _ => do
  if (`VerifiedGarbage.Proof).isPrefixOf (← getMainModule) then checkModule }

end VG.ConflictingBounds
