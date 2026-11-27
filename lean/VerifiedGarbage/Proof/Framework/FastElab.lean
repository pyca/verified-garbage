module

public meta import Lean.Elab.SyntheticMVars
public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Meta.Tactic.Assert

/-!
# Patterns of conjunctions and existences, and short tactic blocks

Untrusted: this only changes how proofs are found.

`fun s ⟨a, b, c⟩ => …`, `match h with | ⟨a, b⟩ => …` and `intro ⟨a, b⟩` define a matcher for
every pattern, a function of the hypothesis and of the alternative that the kernel checks and
the module stores, 5 to 10 ms each: there are some fifty thousand. `obtain ⟨a, b, c⟩ := h` runs
`cases` for every `∧` of `h`, each in a context one fact larger, and `obtain x : T := e` abstracts
`e` in the goal and checks the goal's type again. For a proof of a proposition, with a
pattern of names, `_`, `-` and tuples of them, and `∧` and `∃` in the proof's type, the names are
bound here to the projections themselves: `(fun a b c => …) h.1 h.2.1 h.2.2`, with `Exists.elim`
for an `∃` (`go`). Any other pattern is left to Lean (`throwUnsupportedSyntax`): a constructor
or `rfl` in it, a structure, an equation, a goal that is not a proposition.

A tactic block nested in a term, `foo (by tac)`, first instantiates and shares every
hypothesis of the context (`Term.runTactic`), 2 to 5% of a long proof. `elabShortBy` runs a
block of at most three tactics without that, when neither its goal nor the context has a
metavariable.

All this is for modules of `VerifiedGarbage.Proof` alone.
-/

public meta section

namespace VG.FastElab

open Lean Meta Elab Term Lean.Parser.Tactic

/-- Whether this is a module of proofs. -/
def inProof : CoreM Bool :=
  return (`VerifiedGarbage.Proof).isPrefixOf (← getEnv).mainModule

/-- A pattern: a variable, `_`, `-` or `⟨p, …⟩` with at least two patterns. -/
inductive Pat where
  | var (ref : Syntax) (name : Name)
  | hole
  | clear
  | tuple (ps : List Pat)
  deriving Inhabited

/-- The pattern of a term. -/
partial def ofTerm (stx : Syntax) : OptionT TermElabM Pat := do
  match stx with
  | `(⟨$ps,*⟩) =>
    let ps ← ps.getElems.toList.mapM (ofTerm ·.raw)
    if ps.length < 2 then failure
    return .tuple ps
  | `(_) => return .hole
  | _ =>
    unless stx.isIdent do failure
    let n := stx.getId
    unless n.eraseMacroScopes.isAtomic do failure
    -- not a constant that a pattern may name
    for (c, fs) in ← resolveGlobalName n do
      if fs.isEmpty then
        if (← getEnv).isConstructor c || hasMatchPatternAttribute (← getEnv) c then failure
    return .var stx n

/-- The proposition `type` is, if it is a conjunction or an existence. -/
def view? (type : Expr) : MetaM (Option Expr) := do
  let ok (t : Expr) := t.isAppOfArity ``And 2 || t.isAppOfArity ``Exists 2
  let type := type.consumeMData
  if ok type then return some type
  let t ← whnfR type
  if ok t then return some t
  let t ← whnf type
  if ok t then return some t
  return none

/-- Records that `x` is bound at `ref`. The linter of variables named as a constructor of their
type evaluates the type of every variable bound without an expected type, however large: here it
gets one. -/
def bound (ref : Syntax) (x : Expr) : TermElabM Unit :=
  addTermInfo' (isBinder := true) (expectedType? := some (.sort .zero)) ref x

/-- Binds the patterns `todo`, each with a proof and its type, and elaborates `k`, a proof of `goal`,
under them. `fvs` are bound already, and stand for `vals`. A conjunction that an `∃` has in it
is not in the context of `k`, which has only its parts. -/
partial def go (goal : Expr) (todo : List (Pat × Expr × Expr)) (fvs vals : Array Expr)
    (k : TermElabM Expr) : TermElabM Expr := do
  let close (b : Expr) : TermElabM Expr := do
    if fvs.isEmpty then return b
    return mkAppN (← mkLambdaFVars fvs b) vals
  match todo with
  | [] => close (← k)
  | (.var ref n, e, ty) :: rest =>
    withLocalDeclD n ty fun x => do
      bound ref x
      go goal rest (fvs.push x) (vals.push e) k
  | (.hole, e, ty) :: rest =>
    withLocalDeclD (← mkFreshUserName `x) ty fun x => go goal rest (fvs.push x) (vals.push e) k
  | (.clear, _, _) :: rest => go goal rest fvs vals k
  | (.tuple ps, e, ty) :: rest =>
    let some ty ← view? (← instantiateMVars ty) | throwError "not a conjunction or an existence"
    let p :: ps := ps | throwError "an empty pattern"
    let q := match ps with
      | [q] => q
      | ps => .tuple ps
    match_expr ty with
    | And a b =>
      go goal ((p, .proj ``And 0 e, a) :: (q, .proj ``And 1 e, b) :: rest) fvs vals k
    | Exists α pr =>
      if p matches .tuple _ | .clear then throwError "the witness is not a proof"
      let body ← withLocalDeclD (← nameOf p) α fun w => do
        info p w
        let hty := (mkApp pr w).headBeta
        match q with
        | .tuple _ | .clear =>
          let h := mkFVar (← mkFreshFVarId)
          let b ← go goal ((q, h, hty) :: rest) #[] #[] k
          withLCtx ((← getLCtx).mkLocalDecl h.fvarId! `h hty) (← getLocalInstances) <| mkLambdaFVars #[w, h] b
        | _ =>
          withLocalDeclD (← nameOf q) hty fun h => do
            info q h
            mkLambdaFVars #[w, h] (← go goal rest #[] #[] k)
      close (mkApp5 (.const ``Exists.elim [← getLevel α]) α pr goal e body)
    | _ => throwError "not a conjunction or an existence"
where
  nameOf : Pat → TermElabM Name
    | .var _ n => return n
    | _ => mkFreshUserName `x
  info : Pat → Expr → TermElabM Unit
    | .var ref _, x => bound ref x
    | _, _ => return ()

/-- `match e with | ⟨p, …⟩ => body`, which `fun ⟨p, …⟩ => body` expands to, for a hypothesis `e`. -/
@[term_elab Lean.Parser.Term.match]
def elabMatchFast : TermElab := fun stx expectedType? => do
  let `(match $e:term with | $pat:term => $body) := stx | throwUnsupportedSyntax
  unless pat.raw.isOfKind ``Lean.Parser.Term.anonymousCtor do throwUnsupportedSyntax
  unless ← inProof do throwUnsupportedSyntax
  let some p ← (ofTerm pat).run | throwUnsupportedSyntax
  let some goal := expectedType? | throwUnsupportedSyntax
  let started ← IO.mkRef false
  let s ← saveState
  try
    tryPostponeIfMVar goal
    let goal ← instantiateMVars goal
    if goal.getAppFn.isMVar then throwError "the goal is not known"
    unless ← isProp goal do throwError "the goal is not a proposition"
    let xe ← elabTerm e none
    let ty ← instantiateMVars (← inferType xe)
    tryPostponeIfMVar ty
    unless xe.isFVar do throwError "not a hypothesis"
    -- `match` elaborates the body and then waits for the types of the variables
    if ty.hasExprMVar then throwError "the type is not known"
    let some _ ← view? ty | throwError "not a conjunction or an existence"
    let r ← go goal [(p, xe, ty)] #[] #[] do
      started.set true
      elabTermEnsuringType body goal
    -- as `match` does
    synthesizeSyntheticMVarsUsingDefault
    return r
  catch e =>
    if ← started.get then throw e
    if let .internal id _ := e then
      if id == postponeExceptionId then throw e
    s.restore
    throwUnsupportedSyntax

/-! ### `obtain` and `rintro` -/

open Tactic

mutual

/-- The pattern of an `rcases` pattern. -/
partial def ofRCases (stx : Syntax) : OptionT TacticM Pat := do
  match stx with
  | `(rcasesPat| _) => return .hole
  | `(rcasesPat| $h:ident) =>
    if h.getId == `rfl then failure
    return .var h h.getId
  | `(rcasesPat| -) => return .clear
  | `(rcasesPat| ($p:rcasesPatLo)) => ofRCasesLo p
  | `(rcasesPat| ⟨$ps,*⟩) =>
    let ps ← ps.getElems.toList.mapM (ofRCasesLo ·.raw)
    if ps.length < 2 then failure
    return .tuple ps
  | _ => failure

partial def ofRCasesMed (stx : Syntax) : OptionT TacticM Pat := do
  match stx with
  | `(rcasesPatMed| $ps:rcasesPat|*) =>
    let #[p] := ps.getElems | failure
    ofRCases p
  | _ => failure

partial def ofRCasesLo (stx : Syntax) : OptionT TacticM Pat := do
  match stx with
  | `(rcasesPatLo| $p:rcasesPatMed) => ofRCasesMed p
  | _ => failure

end

/-- The goal `g` with the pattern `p` of the proof `e : ty`, or `none` if it is not one for `go`. -/
def split? (g : MVarId) (p : Pat) (e ty : Expr) : TacticM (Option MVarId) := do
  let goal ← instantiateMVars (← g.getType)
  unless (← isProp goal) && (← isProp ty) do return none
  let some _ ← view? ty | return none
  let s ← saveState
  try
    let new ← IO.mkRef (none : Option MVarId)
    let tag ← g.getTag
    let k : TermElabM Expr := do
      let m ← mkFreshExprSyntheticOpaqueMVar goal tag
      new.set (some m.mvarId!)
      return m
    let r ← if e.isFVar then go goal [(p, e, ty)] #[] #[] k else
      let h := mkFVar (← mkFreshFVarId)
      let b ← go goal [(p, h, ty)] #[] #[] k
      let f ← withLCtx ((← getLCtx).mkLocalDecl h.fvarId! `h ty) (← getLocalInstances) <| mkLambdaFVars #[h] b
      pure (mkApp f e)
    g.assign r
    let some m ← new.get | throwError "no goal"
    if let .fvar h := e then return some (← m.tryClear h)
    return some m
  catch _ =>
    s.restore
    return none

/-- `obtain` of a name or a tuple. -/
elab_rules : tactic
  | `(tactic| obtain $pat:rcasesPatMed $[: $ty?]? := $val:term) => do
    unless ← inProof do throwUnsupportedSyntax
    let some p ← (ofRCasesMed pat).run | throwUnsupportedSyntax
    let g ← getMainGoal
    let g? : Option MVarId ← g.withContext do
      let (e, ty) ← Term.withSynthesize do
        match ty? with
        | some ty =>
          let ty ← Term.elabType ty
          let e ← Term.ensureHasType (some ty) (← Term.elabTerm val (some ty))
          return (e, ty)
        | none =>
          let e ← Term.ensureHasType none (← Term.elabTerm val none)
          return (e, ← inferType e)
      let e ← instantiateMVars e
      let ty ← instantiateMVars ty
      match p with
      | .var ref n =>
        if e.isFVar then throwUnsupportedSyntax
        if ← isProp ty then
          let (x, g) ← (← g.assert n ty e).intro1P
          g.withContext do bound ref (.fvar x)
          return some g
        let t ← Term.exprToSyntax e
        let ty ← Term.exprToSyntax ty
        evalTactic (← `(tactic| rcases $t:term with $pat:rcasesPatMed : $ty:term))
        return none
      | .tuple _ =>
        if let some g ← split? g p e ty then return some g
        if e.isFVar then throwUnsupportedSyntax
        let t ← Term.exprToSyntax e
        evalTactic (← `(tactic| rcases $t:term with $pat:rcasesPatMed))
        return none
      | _ => throwUnsupportedSyntax
    if let some g := g? then replaceMainGoal [g]

/-- `rintro` of names and tuples. -/
elab_rules : tactic
  | `(tactic| rintro $pats:rintroPat*) => do
    unless ← inProof do throwUnsupportedSyntax
    let mut ts : Array (TSyntax `tactic) := #[]
    for p in pats do
      let `(rintroPat| $p:rcasesPat) := p | throwUnsupportedSyntax
      match ← (ofRCases p).run with
      | some (.var ref _) => ts := ts.push (← `(tactic| intro $(⟨ref⟩):ident))
      | some .hole => ts := ts.push (← `(tactic| intro _))
      | some (.tuple _) =>
        ts := ts.push (← `(tactic| intro h))
        ts := ts.push (← `(tactic| obtain $(← `(rcasesPatMed| $p:rcasesPat)) := h))
      | _ => throwUnsupportedSyntax
    for t in ts do evalTactic t

/-! ### `by` in a term -/

/-- `by` with at most three tactics. -/
def isShortBy (stx : Syntax) : Bool :=
  let seq := stx[1][0]
  seq.isOfKind ``Lean.Parser.Tactic.tacticSeq1Indented && seq[0].getNumArgs ≤ 5

@[term_elab Lean.Parser.Term.byTactic]
def elabShortBy : TermElab := fun stx expectedType? => do
  unless isShortBy stx do throwUnsupportedSyntax
  let some ty := expectedType? | throwUnsupportedSyntax
  if (← getEnv).isExporting || (← read).tacSnap?.isSome then throwUnsupportedSyntax
  unless ← inProof do throwUnsupportedSyntax
  -- A block that may assign metavariables runs when, and in the order in which, Lean runs it.
  let ty ← instantiateMVars ty
  if ty.hasMVar then throwUnsupportedSyntax
  let lctx ← instantiateLCtxMVars (← getLCtx)
  if lctx.any fun d => d.type.hasMVar then throwUnsupportedSyntax
  unless ← isProp ty do throwUnsupportedSyntax
  -- The others only once the rest of the term is elaborated, in case it fails.
  tryPostpone
  let m ← mkFreshExprMVarAt lctx (← getLocalInstances) ty MetavarKind.syntheticOpaque
  let s ← saveState
  -- As `Term.runTactic` runs it: terms in the block may be postponed.
  let run : TermElabM Bool := withoutAutoBoundImplicit <| withReader ({ · with mayPostpone := true }) do
    let gs ← Tactic.run m.mvarId! do
      Tactic.withTacticInfoContext stx do
        withoutTacticIncrementality true (evalTactic stx[1])
      withoutTacticIncrementality true do
        synthesizeSyntheticMVars (postpone := .no)
    return gs.isEmpty && !(← MonadLog.hasErrors)
  -- Also when it reaches the recursion limit, which is near at the end of a long proof: Lean's
  -- elaborator then runs the block, from where fewer calls are open.
  let ok ← tryCatchRuntimeEx run fun _ => return false
  -- Lean's own elaborator reports what is wrong.
  unless ok do
    s.restore
    throwUnsupportedSyntax
  return m

end VG.FastElab
