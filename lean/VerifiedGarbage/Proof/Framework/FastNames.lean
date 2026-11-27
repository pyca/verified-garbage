module

public meta import Lean.Elab.Tactic.Simp

/-!
# Names are looked up once

Untrusted: this only changes how the elaborator finds what a name means, not
what it means.

To find what a name means the elaborator asks whether the name, and
each prefix of it, is a constant in each enclosing namespace and each opened
one, public or private: in a module with a dozen of them that takes 40 µs for
the `Eq` of `=`, 115 µs for the `HAdd.hAdd` of `+`, 80 µs for the constructor
of `⟨…⟩`, half a millisecond for a lemma's full name in a macro's
`simp only [...]`. It does so twice for every name (the first time to decide whether a
local declaration may have the name), twice that for a lemma of a `simp`, which
looks up its arguments twice, and three times for one of a `rw`; also for the projections of a
local declaration, `h.foo`, though a local declaration comes before any constant; and also for a
name that a macro writes, which its quotation has resolved to a constant where it is written.

Here, in the modules of `VerifiedGarbage.Proof` (and nowhere else: registrations
and contracts are elaborated by Lean's own rules alone):

* a name with macro scopes that its quotation resolved to exactly one constant
  becomes an identifier that carries the constant and whose own name no scope
  has (`constIdent`), which the elaborator resolves to the same constant at
  once, unless a local declaration might have the name (`namesLocal`): the head
  of an application, a term, and a lemma of a `simp` (here in any module);
* a name of the source there, or a lemma of a `rw`, that no local declaration has becomes such an
  identifier too, with the constant that Lean's own rules find; and `h.foo`, with `h` a
  local declaration, the projection `foo` of it (`ofSource?`);
* the macros of the operators (`+`, `=`, `≤`, `∧`, `∈`, …) write such an
  identifier, in the same syntax as Lean's.

Whatever is not of these forms is left to Lean's own elaborators and macros
(`throwUnsupportedSyntax`).

For the same reason a numeral of a type that is not known yet (an operand of an operator) does not
look for an instance that it cannot find, and one of type `Nat` or `BitVec w` for the one it
always finds (`elabNumFast`).
-/

public meta section

namespace VG.FastNames

open Lean Elab Term Meta

/-- An identifier that names the constant `c` and that the elaborator finds at once: its own name
(a number, not a string) names nothing in any scope. -/
def constIdent (info : SourceInfo) (c : Name) : Syntax :=
  .ident info (c.toString false).toRawSubstring (.num .anonymous 0) [.decl c []]

/-- Whether the module `m` is one of proofs: terms elsewhere (registrations, contracts) are elaborated
by Lean's own rules alone. -/
def isProof (m : Name) : Bool := (`VerifiedGarbage.Proof).isPrefixOf m

/-- Whether a name with macro scopes, `n` or a prefix of it, might name a local declaration. -/
def namesLocal (lctx : LocalContext) (n : Name) : Bool := Id.run do
  let view := extractMacroScopes n
  let rec prefixes : Name → List Name
    | m@(.str p _) => { view with name := m }.review :: prefixes p
    | _ => []
  let ns := prefixes view.name
  for d? in lctx.decls do
    let some d := d? | continue
    if ns.contains d.userName then return true
    if d.isAuxDecl then
      -- The declarations being defined are matched with the names less strictly.
      if d.userName.hasMacroScopes then return true
      if let some full := lctx.auxDeclToFullName.get? d.fvarId then
        if full.hasMacroScopes then return true
  return false

/-- `stx`, if it is an identifier a macro wrote (its macro scopes are those of one expansion) that the
quotation resolved to one constant, as a `constIdent`: the meaning Lean gives it unless a local
declaration the macro introduced has that name. -/
def ofScoped? (lctx : LocalContext) (stx : Syntax) : Option Syntax :=
  match stx with
  | .ident info _ n [.decl c []] =>
    if n.hasMacroScopes && !namesLocal lctx n then some (constIdent info c) else none
  | _ => none

/-! ### Terms -/

/-- Lean's own elaborator of `stx`. -/
def elabBuiltin : TermElab := fun stx expectedType? => do
  let some e := (termElabAttribute.getEntries (← getEnv) stx.getKind).getLast? | throwUnsupportedSyntax
  e.value stx expectedType?

/-- Whether an auxiliary declaration (one that is being defined) might have the name `n`, or a prefix
of it: they are found by a part of their names, which has a component of theirs in it. -/
def namesAux (lctx : LocalContext) (n : Name) : Bool :=
  lctx.decls.any fun
    | some d => d.isAuxDecl &&
      (d.userName.hasMacroScopes || (n.components.any fun c => d.userName.components.contains c))
    | none => false

/-- The number of components of `n` after its longest prefix that is a local declaration's name. -/
def localPrefix? (lctx : LocalContext) (n : Name) : Option Nat :=
  go n 0
where
  go : Name → Nat → Option Nat
    | m@(.str p _), k => if (lctx.findFromUserName? m).isSome then some k else go p (k + 1)
    | _, _ => none

/-- The projections `fields` of `e`. -/
def projections (info : SourceInfo) (e : Syntax) (fields : List Syntax) : Syntax :=
  fields.foldl (init := e) fun e f => .node info ``Lean.Parser.Term.proj #[e, mkAtom ".", f]

/-- An identifier `stx` of the source, with what Lean finds it to mean written out: a constant or
a local declaration, and the projections of it. None for the name of a local declaration, which Lean
finds at once, and for what is left to Lean: a name that a declaration being defined might have,
one of a constant that is only generated when it is used, and what Lean does not find. -/
def ofSource? (stx : Syntax) : TermElabM (Option Syntax) := do
  let .ident info _ n [] := stx | return none
  unless n matches .str .. do return none
  if n.hasMacroScopes then return none
  let lctx ← getLCtx
  match localPrefix? lctx n with
  | some 0 => return none
  | some k =>
    if namesAux lctx n then return none
    let hd :: fields := stx.identComponents (nFields? := some k) | return none
    return projections info hd fields
  | none =>
    if namesAux lctx n then return none
    let cs ← resolveGlobalName n
    let env ← getEnv
    unless cs.all fun (c, _) => env.contains c do return none
    let (c, projs) :: rest := cs | return none
    if cs.all (·.2.isEmpty) then
      return some <| .ident info (c.toString false).toRawSubstring (.num .anonymous 0) (cs.map fun (c, _) => .decl c [])
    unless rest.isEmpty do return none
    let hd :: fields := stx.identComponents (nFields? := some projs.length) | return none
    return projections info (constIdent hd.getHeadInfo c) fields

/-- `ofScoped?` or `ofSource?`. -/
def ofIdent? (stx : Syntax) : TermElabM (Option Syntax) := do
  match ofScoped? (← getLCtx) stx with
  | some s => return some s
  | none => ofSource? stx

/-- The head of an application, with the identifier in it as `ofIdent?` gives it. -/
partial def ofHead? (stx : Syntax) : TermElabM (Option Syntax) := do
  match stx with
  | .ident .. => ofIdent? stx
  | .node _ k _ =>
    if k == ``Lean.Parser.Term.proj || k == ``Lean.Parser.Term.explicitUniv then
      return (← ofHead? stx[0]).map (stx.setArg 0 ·)
    else if k == ``Lean.Parser.Term.explicit then
      return (← ofHead? stx[1]).map (stx.setArg 1 ·)
    else return none
  | _ => return none

@[term_elab Lean.Parser.Term.app]
def elabAppFast : TermElab := fun stx expectedType? => do
  unless isProof (← getEnv).mainModule do throwUnsupportedSyntax
  let some f ← ofHead? stx[0] | throwUnsupportedSyntax
  elabBuiltin (stx.setArg 0 f) expectedType?

@[term_elab ident]
def elabIdentFast : TermElab := fun stx expectedType? => do
  unless isProof (← getEnv).mainModule do throwUnsupportedSyntax
  let some f ← ofIdent? stx | throwUnsupportedSyntax
  elabBuiltin f expectedType?

@[term_elab Lean.Parser.Term.proj]
def elabProjFast : TermElab := fun stx expectedType? => do
  unless isProof (← getEnv).mainModule do throwUnsupportedSyntax
  let some f ← ofHead? stx | throwUnsupportedSyntax
  elabBuiltin f expectedType?

@[term_elab Lean.Parser.Term.explicit]
def elabExplicitFast : TermElab := fun stx expectedType? => do
  unless isProof (← getEnv).mainModule do throwUnsupportedSyntax
  let some f ← ofHead? stx | throwUnsupportedSyntax
  elabBuiltin f expectedType?

/-! ### Numerals -/

/-- A numeral of type `Nat` or `BitVec w`, with the instance Lean finds for it; one of a type that is
not known yet, without looking for an instance, which is found when it is. -/
@[term_elab num]
def elabNumFast : TermElab := fun stx expectedType? => do
  unless isProof (← getEnv).mainModule do throwUnsupportedSyntax
  let some val := stx.isNatLit? | throwUnsupportedSyntax
  let n := mkRawNatLit val
  let type ← match expectedType? with
    | some t => instantiateMVars t
    | none => mkFreshTypeMVar .synthetic
  match type with
  | .const ``Nat _ => return mkApp3 (.const ``OfNat.ofNat [0]) type n (.app (.const ``instOfNatNat []) n)
  | .app (.const ``BitVec _) w =>
    return mkApp3 (.const ``OfNat.ofNat [0]) type n (mkApp2 (.const ``BitVec.instOfNat []) w n)
  | .mvar _ =>
    let u ← getDecLevel type
    let m ← mkFreshExprMVar (mkApp2 (.const ``OfNat [u]) type n) .synthetic
    registerSyntheticMVarWithCurrRef m.mvarId! (.typeClass none)
    let r := mkApp3 (.const ``OfNat.ofNat [u]) type n m
    registerMVarErrorImplicitArgInfo m.mvarId! stx r
    return r
  | _ => throwUnsupportedSyntax

/-! ### Operators -/

/-- The position of what a macro writes, in a module of proofs (the quotation context is the module's
name and a number). -/
private def infoInProof : MacroM SourceInfo := do
  unless isProof (← read).quotContext do Macro.throwUnsupported
  MonadRef.mkInfoFromRefPos

/-- `x op y` as `head op x y`, for the syntax `head` (`binop% `, …). -/
private def infixOp (kind : SyntaxNodeKind) (head : String) (c : Name) : Macro := fun stx => do
  let info ← infoInProof
  return .node info kind #[.atom info head, constIdent info c, stx[0], stx[2]]

private def binop := infixOp ``Lean.Parser.Term.binop "binop%"
private def binrel := infixOp ``Lean.Parser.Term.binrel "binrel%"

@[macro «term_|||_»] def mOr : Macro := binop ``HOr.hOr
@[macro «term_^^^_»] def mXor : Macro := binop ``HXor.hXor
@[macro «term_&&&_»] def mAnd : Macro := binop ``HAnd.hAnd
@[macro «term_+_»] def mAdd : Macro := binop ``HAdd.hAdd
@[macro «term_-_»] def mSub : Macro := binop ``HSub.hSub
@[macro «term_*_»] def mMul : Macro := binop ``HMul.hMul
@[macro «term_/_»] def mDiv : Macro := binop ``HDiv.hDiv
@[macro «term_%_»] def mMod : Macro := binop ``HMod.hMod
@[macro «term_++_»] def mAppend : Macro := binop ``HAppend.hAppend
@[macro «term_=_»] def mEq : Macro := binrel ``Eq
@[macro «term_≠_»] def mNe : Macro := binrel ``Ne
@[macro «term_≤_»] def mLe : Macro := binrel ``LE.le
@[macro «term_<_»] def mLt : Macro := binrel ``LT.lt
@[macro «term_≥_»] def mGe : Macro := binrel ``GE.ge
@[macro «term_>_»] def mGt : Macro := binrel ``GT.gt
@[macro «term_==_»] def mBeq : Macro := infixOp ``Lean.Parser.Term.binrel_no_prop "binrel_no_prop%" ``BEq.beq

/-- `x ^ y`; a numeral `y` as `(y : Nat)`, as `PowLit` has it. -/
@[macro «term_^_»] def mPow : Macro := fun stx => do
  let info ← infoInProof
  let y := stx[2]
  let y ← if y.isOfKind numLitKind then `(($(⟨y⟩) : $(⟨constIdent info ``Nat⟩))) else pure ⟨y⟩
  return .node info ``Lean.Parser.Term.rightact #[.atom info "rightact%", constIdent info ``HPow.hPow, stx[0], y]

/-- The constant `c` applied to `args`. -/
private def mkApp (info : SourceInfo) (c : Name) (args : Array Syntax) : Syntax :=
  .node info ``Lean.Parser.Term.app #[constIdent info c, .node info nullKind args]

/-- `x op y` as `c x y`. -/
private def infixApp (c : Name) : Macro := fun stx => do
  return mkApp (← infoInProof) c #[stx[0], stx[2]]

@[macro «term_∧_»] def mConj : Macro := infixApp ``And
@[macro «term_∨_»] def mDisj : Macro := infixApp ``Or
@[macro «term_↔_»] def mIff : Macro := infixApp ``Iff
@[macro «term_∣_»] def mDvd : Macro := infixApp ``Dvd.dvd
@[macro «term_<<<_»] def mShl : Macro := infixApp ``HShiftLeft.hShiftLeft
@[macro «term_>>>_»] def mShr : Macro := infixApp ``HShiftRight.hShiftRight
@[macro «term_&&_»] def mBand : Macro := infixApp ``and
@[macro «term_||_»] def mBor : Macro := infixApp ``or
@[macro «term_∈_»] def mMem : Macro := fun stx => do
  return mkApp (← infoInProof) ``Membership.mem #[stx[2], stx[0]]
@[macro «term_∉_»] def mNotMem : Macro := fun stx => do
  let info ← infoInProof
  return mkApp info ``Not #[mkApp info ``Membership.mem #[stx[2], stx[0]]]
@[macro «term¬_»] def mNot : Macro := fun stx => do
  return mkApp (← infoInProof) ``Not #[stx[1]]

/-! ### `simp` -/

open Tactic

/-- The argument `arg` of a `simp` with its name, if it is one, as a name the elaborator finds at
once. -/
def simpArg (arg : Syntax) : TermElabM (Option Syntax) := do
  if arg.isOfKind ``Lean.Parser.Tactic.simpLemma then
    if arg[2].isIdent then
      if let some t := ofScoped? (← getLCtx) arg[2] then return some (arg.setArg 2 t)
      if isProof (← getEnv).mainModule then
        if let some t ← ofSource? arg[2] then return some (arg.setArg 2 t)
  return none

/-- `stx` with the arguments of the `simp` it is as `simpArg` gives them; none if it has no such
argument. -/
partial def simpArgs? (stx : Syntax) : TermElabM (Option Syntax) := do
  match stx with
  | .node info k args =>
    if k == ``Lean.Parser.Tactic.simpLemma then simpArg stx else
    let mut out := args
    let mut changed := false
    for h : i in [0:args.size] do
      let a := args[i]
      if a matches .node .. then
        if a.isOfKind ``Lean.Parser.Tactic.location || a.isOfKind ``Lean.Parser.Tactic.optConfig then continue
        if let some a' ← simpArgs? a then
          out := out.set! i a'
          changed := true
    return if changed then some (.node info k out) else none
  | _ => return none

/-- `stx` (a `simp`, `dsimp` or `simp_all`), with the constants that the names of its lemmas are. -/
private def simpNames : Tactic := fun stx => do
  let some stx ← withMainContext do simpArgs? stx | throwUnsupportedSyntax
  evalTactic stx

@[tactic Lean.Parser.Tactic.simp] def evalSimpNames : Tactic := simpNames
@[tactic Lean.Parser.Tactic.dsimp] def evalDSimpNames : Tactic := simpNames
@[tactic Lean.Parser.Tactic.simpAll] def evalSimpAllNames : Tactic := simpNames

/-! ### `rw` -/

/-- A `rewrite` with the constants that the names of its lemmas are. -/
@[tactic Lean.Parser.Tactic.rewriteSeq] def evalRwNames : Tactic := fun stx => do
  unless isProof (← getEnv).mainModule do throwUnsupportedSyntax
  let mut rules := stx[2][1]
  let mut changed := false
  for i in [0:rules.getNumArgs] do
    let r := rules[i]
    if r.isOfKind ``Lean.Parser.Tactic.rwRule && r[1].isIdent then
      if let some t ← withMainContext (ofIdent? r[1]) then
        rules := rules.setArg i (r.setArg 1 t)
        changed := true
  unless changed do throwUnsupportedSyntax
  evalTactic (stx.setArg 2 (stx[2].setArg 1 rules))

end VG.FastNames
