module

public meta import Lean.Elab.Tactic.Simp

/-!
# Names that macros write are not looked up

Untrusted: this only changes how the elaborator finds what a name means, not
what it means.

A quotation resolves the names in it to constants where it is written, and the
elaborator takes that constant for a name a macro writes; but first it asks
whether a local declaration has that name, and on the way whether the name and
each prefix of it is a constant in each enclosing namespace and each opened
one, public or private. In a module with a dozen of them that takes 40 µs for
the `Eq` of `=`, 115 µs for the `HAdd.hAdd` of `+`, 80 µs for the constructor
of `⟨…⟩`, half a millisecond for a lemma's full name in a macro's
`simp only [...]`, and twice that, since `simp` looks up its arguments twice.

Here, in the modules of `VerifiedGarbage.Proof` (and nowhere else: registrations
and contracts are elaborated by Lean's own rules alone):

* a name with macro scopes that its quotation resolved to exactly one constant
  becomes an identifier that carries the constant and whose own name no scope
  has (`constIdent`), which the elaborator resolves to the same constant at
  once, unless a local declaration might have the name (`namesLocal`): the head
  of an application, a term, and a lemma of a `simp` (here in any module);
* the macros of the operators (`+`, `=`, `≤`, `∧`, `∈`, …) write such an
  identifier, in the same syntax as Lean's. (Not `^`, whose macro `PowLit` adds to:
  a macro here would come before it.)

Names that the source writes are not touched. Whatever is not of these forms is
left to Lean's own elaborators and macros (`throwUnsupportedSyntax`).
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

@[term_elab Lean.Parser.Term.app]
def elabAppFast : TermElab := fun stx expectedType? => do
  unless isProof (← getEnv).mainModule do throwUnsupportedSyntax
  let some f := ofScoped? (← getLCtx) stx[0] | throwUnsupportedSyntax
  elabTerm (stx.setArg 0 f) expectedType?

@[term_elab ident]
def elabIdentFast : TermElab := fun stx expectedType? => do
  unless isProof (← getEnv).mainModule do throwUnsupportedSyntax
  let some f := ofScoped? (← getLCtx) stx | throwUnsupportedSyntax
  elabTerm f expectedType?

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
def simpArg (lctx : LocalContext) (arg : Syntax) : Option Syntax :=
  if arg.isOfKind ``Lean.Parser.Tactic.simpLemma then
    (ofScoped? lctx arg[2]).map fun t => arg.setArg 2 t
  else none

/-- `stx` with the arguments of the `simp` it is as `simpArg` gives them; none if it has no such
argument. -/
partial def simpArgs? (lctx : LocalContext) (stx : Syntax) : Option Syntax :=
  match stx with
  | .node info k args =>
    if k == ``Lean.Parser.Tactic.simpLemma then simpArg lctx stx else Id.run do
    let mut out := args
    let mut changed := false
    for h : i in [0:args.size] do
      let a := args[i]
      if a matches .node .. then
        if a.isOfKind ``Lean.Parser.Tactic.location || a.isOfKind ``Lean.Parser.Tactic.optConfig then continue
        if let some a' := simpArgs? lctx a then
          out := out.set! i a'
          changed := true
    return if changed then some (.node info k out) else none
  | _ => none

/-- `stx` (a `simp`, `dsimp` or `simp_all`), if a macro wrote names of its lemmas, with their constants
for them. -/
private def simpNames : Tactic := fun stx => do
  let some stx ← withMainContext do return simpArgs? (← getLCtx) stx | throwUnsupportedSyntax
  evalTactic stx

@[tactic Lean.Parser.Tactic.simp] def evalSimpNames : Tactic := simpNames
@[tactic Lean.Parser.Tactic.dsimp] def evalDSimpNames : Tactic := simpNames
@[tactic Lean.Parser.Tactic.simpAll] def evalSimpAllNames : Tactic := simpNames

end VG.FastNames
