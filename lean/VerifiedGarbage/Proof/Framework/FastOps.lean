module

public import VerifiedGarbage.Proof.Framework.FastNames
public meta import VerifiedGarbage.Proof.Framework.FastNames

/-!
# Operators between operands of one type

Untrusted: this only changes how terms are elaborated, not what they mean.

`x + 5 < 2 ^ 64` is a tree of operators (`binop%`, `binrel%`, `rightact%`), whose elaborator
first elaborates each operand without a type, then finds the type that they all coerce to (which
between `Nat` and `Int` looks for a coercion from `Int` to `Nat` first). A numeral
has none then: for each of them it looks for an instance `OfNat ?α 5`, which it cannot find, when
it meets it and again every time it asks for the instances that are still to be found. Each operator
is then applied like any function, and asks for its instance twice. Where the operands all have
the same type, or are natural numbers and integers, none of that is needed.

Here, in the modules of `VerifiedGarbage.Proof` (as in `FastNames`), the operands that are not
numerals are elaborated first. If their types are the same term (or `Nat` and `Int`, where the natural
numbers are cast), the numerals are elaborated with that type and the operators applied to them, with
the instances that Lean finds for that type.
Otherwise (and where an operator is not one of the known ones) Lean's elaborator goes on
with the operands, already elaborated.

Elaborating an operand may give every numeral whose type is not known yet its default type, `Nat`:
in `x &&& 0xFFFF ||| y <<< 16` the shift does so (its result's type is an output of its instance),
and `0xFFFF` is a `Nat`, cast. A numeral that comes before such an operand is left to Lean's elaborator,
with the whole expression (`mkProbe`).
-/

public meta section

namespace VG.FastOps

open Lean Elab Term Meta VG.FastNames

/-- A tree of operators; an operand is a number in the list of operands. -/
inductive Tree where
  | leaf (i : Nat)
  | num (stx : Syntax)
  | op (f : Name) (l r : Tree)
  | pow (l : Tree) (i : Nat)
  deriving Inhabited

/-- The operators whose operands and result have one type. -/
def isOp (f : Name) : Bool :=
  f == ``HAdd.hAdd || f == ``HSub.hSub || f == ``HMul.hMul || f == ``HDiv.hDiv || f == ``HMod.hMod ||
  f == ``HAnd.hAnd || f == ``HOr.hOr || f == ``HXor.hXor || f == ``HAppend.hAppend

/-- The constant an operator's syntax names. -/
def opName? (stx : Syntax) : Option Name :=
  match stx with
  | .ident _ _ _ [.decl c []] => some c
  | _ => none

/-- The operands of a tree that are not numerals, in their order, and how many of them come before the
first numeral, if there is one. -/
structure Operands where
  stxs : Array Syntax := #[]
  num? : Option Nat := none

/-- The tree of `stx`, whose operands are added to those found so far. None if it has an operator that
is not known. -/
partial def toTree (stx : Syntax) : StateRefT Operands (OptionT TermElabM) Tree := do
  let k := stx.getKind
  if k == numLitKind then
    modify fun s => { s with num? := s.num? <|> some s.stxs.size }
    return .num stx
  if k == ``Lean.Parser.Term.binop then
    let some f := opName? stx[1] | failure
    unless isOp f do failure
    return .op f (← toTree stx[2]) (← toTree stx[3])
  if k == ``Lean.Parser.Term.rightact then
    let some f := opName? stx[1] | failure
    unless f == ``HPow.hPow do failure
    let l ← toTree stx[2]
    return .pow l (← operand stx[3])
  if k == ``Lean.Parser.Term.unop || k == ``Lean.Parser.Term.leftact || k == ``Lean.Parser.Term.binop_lazy ||
    k == choiceKind then failure
  match stx with
  | `(($h:hygieneInfo $e)) =>
    if hasCDot e h.getHygieneInfo then leaf stx else toTree e
  | _ =>
    match ← (liftMacroM <| expandMacroImpl? (← getEnv) stx : TermElabM _) with
    | some (_, .ok stx') => toTree stx'
    | some (_, .error _) => failure
    | none => leaf stx
where
  operand (stx : Syntax) : StateRefT Operands (OptionT TermElabM) Nat := do
    let i := (← get).stxs.size
    modify fun s => { s with stxs := s.stxs.push stx }
    return i
  leaf (stx : Syntax) : StateRefT Operands (OptionT TermElabM) Tree := return .leaf (← operand stx)

/-- The operands `es` in the tree's place, in Lean's own syntax. -/
partial def Tree.toSyntax (es : Array Syntax) : Tree → Syntax
  | .leaf i => es[i]!
  | .num stx => stx
  | .op f l r => .node .none ``Lean.Parser.Term.binop
    #[mkAtom "binop%", constIdent .none f, l.toSyntax es, r.toSyntax es]
  | .pow l i => .node .none ``Lean.Parser.Term.rightact
    #[mkAtom "rightact%", constIdent .none ``HPow.hPow, l.toSyntax es, es[i]!]

/-- Whether a numeral is an operand. -/
def Tree.hasNum : Tree → Bool
  | .leaf _ => false
  | .num _ => true
  | .op _ l r => l.hasNum || r.hasNum
  | .pow l _ => l.hasNum

/-- The type that operands of types `T` and `T'` coerce to: `T`, if they are the same, or `Int`. -/
def join (T? : Option Expr) (T' : Expr) : OptionT TermElabM Expr := do
  let T' := T'.cleanupAnnotations
  if T'.hasExprMVar then failure
  let some T := T? | return T'
  if T == T' then return T
  if T'.isConstOf ``Nat then
    if T.isConstOf ``Int then return T
  if T.isConstOf ``Nat && T'.isConstOf ``Int then return T'
  unless ← withNewMCtxDepth <| withConfig (fun c => { c with isDefEqStuckEx := true }) <| isDefEqGuarded T T' do failure
  return T

/-- The type that the operands of `t` coerce to, and an operand of the type `T?`. -/
def Tree.type? (ts : Array Expr) (t : Tree) (T? : Option Expr) : OptionT TermElabM (Option Expr) :=
  match t with
  | .leaf i => do return some (← join T? ts[i]!)
  | .num _ => return T?
  | .op _ l r => do r.type? ts (← l.type? ts T?)
  | .pow l i => do
    unless ts[i]!.cleanupAnnotations.isConstOf ``Nat do failure
    l.type? ts T?

/-- The operators of `t`. -/
def Tree.ops (t : Tree) (a : Array Name) : Array Name :=
  match t with
  | .leaf _ | .num _ => a
  | .op f l r => r.ops (l.ops (if a.contains f then a else a.push f))
  | .pow l _ => l.ops a

/-- The operators found so far, each with its operands' types, applied up to its operands, and its
result's type. -/
abbrev Fns := Array (Name × Expr × Expr × Expr × Expr)

/-- The operator `f` between operands of types `T` and `T'`. -/
def opFn (f : Name) (T T' : Expr) : StateRefT Fns (OptionT TermElabM) (Expr × Expr) := do
  for (f', T₁, T₂, r) in ← get do
    if f == f' && T == T₁ && T' == T₂ then return r
  let .str cls _ := f | failure
  let u ← getDecLevel T
  let v ← if T == T' then pure u else getDecLevel T'
  let R ← mkFreshTypeMVar
  let w ← getDecLevel R
  let .some inst ← trySynthInstance (mkApp3 (.const cls [u, v, w]) T T' R) | failure
  let fn ← instantiateMVars (.app (mkApp3 (.const f [u, v, w]) T T' R) inst)
  let R ← instantiateMVars R
  if fn.hasMVar then failure
  modify (·.push (f, T, T', fn, R))
  return (fn, R)

/-- The term of `t`, whose operands coerce to the type `T`, and its type. -/
partial def Tree.build (es ts : Array Expr) (T : Expr) (t : Tree) : StateRefT Fns (OptionT TermElabM) (Expr × Expr) := do
  match t with
  | .leaf i =>
    if T.isConstOf ``Int && ts[i]!.cleanupAnnotations.isConstOf ``Nat then
      return (mkApp3 (.const ``Nat.cast [.zero]) T (.const ``instNatCastInt []) es[i]!, T)
    return (es[i]!, ts[i]!)
  | .num stx => return (← elabTermEnsuringType stx T, T)
  | .op f l r =>
    let (l, Tl) ← l.build es ts T
    let (r, Tr) ← r.build es ts T
    let (fn, R) ← opFn f Tl Tr
    return (mkApp2 fn l r, R)
  | .pow l i =>
    let (l, Tl) ← l.build es ts T
    let (fn, R) ← opFn ``HPow.hPow Tl ts[i]!
    return (mkApp2 fn l es[i]!, R)

/-- A metavariable for an instance of `OfScientific ?α`, which is found when the numerals whose type is
not known are given their default type: it is a class with a default instance, as `OfNat` is, but
with few instances to try before that. -/
def mkProbe : TermElabM MVarId := do
  let type ← mkFreshTypeMVar .synthetic
  let u ← getDecLevel type
  let m ← mkFreshExprMVar (mkApp (.const ``OfScientific [u]) type) .synthetic
  registerSyntheticMVarWithCurrRef m.mvarId! (.typeClass none)
  return m.mvarId!

/-- The operands `o`, elaborated without a type, the first `n` before the others, and their types. None
if Lean's elaborator would have given a numeral its default type meanwhile. -/
def elabOperands? (o : Operands) (n : Nat) : TermElabM (Option (Array Expr × Array Expr)) := do
  let mut probe? : Option MVarId := none
  let mut es := #[]
  for h : i in [0:o.stxs.size] do
    if i == n then synthesizeSyntheticMVars (postpone := .yes)
    if o.num? == some i then probe? := some (← mkProbe)
    es := es.push (← elabTerm o.stxs[i] none)
  synthesizeSyntheticMVars (postpone := .yes)
  if let some m := probe? then
    if ← m.isAssigned then return none
    modify fun s => { s with
      pendingMVars := s.pendingMVars.filter (· != m)
      syntheticMVars := s.syntheticMVars.erase m }
  return some (es, ← es.mapM fun e => do instantiateMVars (← inferType e))

/-- The term of the trees `ts`, if their operands coerce to one type and the operators have an instance
for it, with `k` to apply to them. -/
def build? (es ts : Array Expr) (trees : List Tree) (T0? : Option Expr)
    (k : List (Expr × Expr) → OptionT TermElabM Expr) : TermElabM (Option Expr) := do
  let s ← saveState
  let r? ← OptionT.run do
    let some T ← trees.foldlM (init := T0?) fun T? t => t.type? ts T? | failure
    if T.hasMVar then failure
    if trees.any Tree.hasNum then
      unless (← whnfR T) matches .const ``Nat _ | .const ``Int _ | .app (.const ``BitVec _) _ do failure
    -- Lean coerces operands only where the operator has an instance for their type.
    let rs ← StateRefT'.run' (s := (#[] : Fns)) do
      for f in trees.foldl (fun a t => t.ops a) #[] do discard <| opFn f T T
      trees.mapM (·.build es ts T)
    k rs
  if r?.isNone then s.restore
  return r?

/-- `es`, as syntax. -/
def holes (es : Array Expr) : TermElabM (Array Syntax) :=
  es.mapM fun e => return (← exprToSyntax e).raw

@[term_elab binop, term_elab rightact]
def elabOpFast : TermElab := fun stx expectedType? => do
  unless isProof (← getEnv).mainModule do throwUnsupportedSyntax
  if (← read).inPattern then throwUnsupportedSyntax
  let some (t, o) ← ((toTree stx).run {}).run | throwUnsupportedSyntax
  if o.stxs.isEmpty then throwUnsupportedSyntax
  let some (es, ts) ← elabOperands? o 0 | throwUnsupportedSyntax
  let T0? ← expectedType?.mapM fun T => return (← instantiateMVars T).cleanupAnnotations
  let T0? := T0?.filter (!·.getAppFn.isMVar)
  match ← build? es ts [t] T0? fun rs => return rs.head!.1 with
  | some r => ensureHasType expectedType? r
  | none => elabBuiltin (t.toSyntax (← holes es)) expectedType?

@[term_elab binrel]
def elabRelFast : TermElab := fun stx expectedType? => do
  unless isProof (← getEnv).mainModule do throwUnsupportedSyntax
  if (← read).inPattern then throwUnsupportedSyntax
  let some f := opName? stx[1] | throwUnsupportedSyntax
  let cls? ← if f == ``Eq || f == ``Ne then pure none
    else if f == ``LT.lt || f == ``GT.gt then pure (some ``LT)
    else if f == ``LE.le || f == ``GE.ge then pure (some ``LE)
    else throwUnsupportedSyntax
  let some ((l, r, n), o) ← ((do
      let l ← toTree stx[2]
      let n := (← get).stxs.size
      return (l, ← toTree stx[3], n)).run {}).run | throwUnsupportedSyntax
  if o.stxs.isEmpty then throwUnsupportedSyntax
  withSynthesizeLight do
    let some (es, ts) ← elabOperands? o n | throwUnsupportedSyntax
    let r? ← build? es ts [l, r] none fun rs => do
      let [(l, T), (r, _)] := rs | failure
      let hd ← match cls? with
        | none => pure (.app (.const f [← getLevel T]) T)
        | some cls =>
          let u ← getDecLevel T
          let .some inst ← trySynthInstance (.app (.const cls [u]) T) | failure
          pure (mkApp2 (.const f [u]) T inst)
      if hd.hasMVar then failure
      return mkApp2 hd l r
    match r? with
    | some r => return r
    | none =>
      let hs ← holes es
      elabBuiltin (stx.setArgs #[stx[0], stx[1], l.toSyntax hs, r.toSyntax hs]) expectedType?

end VG.FastOps
