module

public meta import Lean.Elab.Term
public meta import Lean.Meta.Match.MatcherInfo

/-!
# The match on an instruction, with its cases closed

A function of an instruction is a `match`, which Lean compiles to a matcher:
a function of the instruction and of the match's alternatives. The kernel
unfolds it at every instruction it has not met before, which builds a term
of every case of the matcher around the alternatives it was given, to keep
one: a third of a millisecond for a match on `Instr`, and the step of a
plain instruction is two of them (x86-64's `RTaint.stepFn1` and `stepKeepFn`).
`inline_match% f g …` is `f` as a `casesOn` whose minor premises are closed
terms, the alternatives themselves with the matches of `f` (and of the
functions `g …` it applies to the instruction) on that constructor resolved:
the kernel then only keeps the one it needs. Where a pattern looks into an
argument of the constructor (`.mov d (.mem m)`), the case is a `casesOn` of
that argument in turn.
-/

public meta section

namespace VG

namespace InlineMatch
open Lean Meta

/-- Whether `n` is a matcher, a `casesOn` or a sparse `casesOn`. -/
def isCaseFn (env : Environment) (n : Name) : Bool :=
  Lean.Meta.isMatcherCore env n || isCasesOnRecursor env n ||
    (match n with | .str _ s => s.startsWith "_sparseCasesOn" | _ => false)

/-- `e`, with the applications of the functions `fs` to constructors unfolded and reduced. -/
partial def reduceCalls (fs : Array Name) (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun x => do
    let .const g _ := x.getAppFn | return .continue
    unless fs.contains g do return .continue
    let args := x.getAppArgs
    if args.isEmpty then return .continue
    let .const c _ := args.back!.getAppFn | return .continue
    unless (← getEnv).find? c matches some (.ctorInfo _) do return .continue
    let some x' ← unfoldDefinition? x | return .continue
    return .visit (← whnfCore x'.headBeta))

/-- `e` with its head reduced: matches, and the functions `fs` of constructors. Unlike
`reduceCalls`, never looks into the cases of a match that is stuck, of which at most one is
kept once its discriminant is known. -/
partial def headReduce (fs : Array Name) (e : Expr) : MetaM Expr := do
  let e ← whnfCore e
  let .const g _ := e.getAppFn | return e
  unless fs.contains g do return e
  let .const c _ := e.appArg!.getAppFn | return e
  unless (← getEnv).find? c matches some (.ctorInfo _) do return e
  let some e' ← unfoldDefinition? e | return e
  headReduce fs e'.headBeta

/-- The free variables of inductive types that are arguments of the constructor
applications `es`, in order. -/
partial def ctorFVars (es : Array Expr) : MetaM (Array Expr) := do
  let mut out := #[]
  for e in es do
    if e.isFVar then
      let t ← whnfD (← inferType e)
      if let .const n _ := t.getAppFn then
        if let some (.inductInfo iv) := (← getEnv).find? n then
          if iv.ctors.length ≥ 2 && !iv.isRec then out := out.push e
    else if let .const c _ := e.getAppFn then
      if (← getEnv).find? c matches some (.ctorInfo _) then
        out := out ++ (← ctorFVars e.getAppArgs)
  return out

/-- `e`, a value of the type `β` whose head is reduced and that may be a match stuck on free
variables of its discriminant: as a tree of `casesOn` on them, the match resolved in each branch. -/
partial def build (fs : Array Name) (β : Expr) (u : Level) (e : Expr) : Nat → MetaM Expr
  | 0 => reduceCalls fs e
  | fuel + 1 => do
    let .const h _ := e.getAppFn | reduceCalls fs e
    unless isCaseFn (← getEnv) h do return ← reduceCalls fs e
    for x in ← ctorFVars e.getAppArgs do
      let t ← whnfD (← inferType x)
      let .const ind _ := t.getAppFn | continue
      let some (.inductInfo iv) := (← getEnv).find? ind | continue
      let mut progress := false
      let mut minors := #[]
      for c in iv.ctors do
        let cinfo ← getConstInfoCtor c
        let (m, p) ← forallTelescope (← instantiateForall cinfo.type t.getAppArgs) fun ys _ => do
          let e' ← headReduce fs (e.replaceFVar x (mkAppN (mkAppN (mkConst c) t.getAppArgs) ys))
          let p := match e'.getAppFn with
            | .const h' _ => !(h' == h && e'.getAppNumArgs == e.getAppNumArgs)
            | _ => true
          return (← mkLambdaFVars ys (← build fs β u e' fuel), p)
        minors := minors.push m
        progress := progress || p
      if progress then
        return mkAppN (mkApp2 (mkConst (ind ++ `casesOn) [u]) (Expr.lam `_ t β .default) x) minors
    reduceCalls fs e

end InlineMatch

open Lean Meta Elab Term InlineMatch in
@[inherit_doc InlineMatch.build]
elab "inline_match% " f:ident gs:ident* : term => liftMetaM do
  let fn ← realizeGlobalConstNoOverload f
  let fs := (← gs.mapM fun g => realizeGlobalConstNoOverload g).push fn
  let .forallE _ dom cod _ := (← getConstInfo fn).type | throwError "inline_match%: {fn} is not a function"
  let .const ind _ := dom.getAppFn | throwError "inline_match%: the domain of {fn} is not an inductive type"
  let some (.inductInfo iv) := (← getEnv).find? ind
    | throwError "inline_match%: the domain of {fn} is not an inductive type"
  let u ← getLevel cod
  let minors ← iv.ctors.toArray.mapM fun c => do
    forallTelescope (← getConstInfoCtor c).type fun xs _ => do
      mkLambdaFVars xs (← build fs cod u (← headReduce fs (mkApp (mkConst fn) (mkAppN (mkConst c) xs))) 3)
  return Expr.lam `i dom
    (mkAppN (mkApp2 (mkConst (ind ++ `casesOn) [u]) (Expr.lam `_ dom cod .default) (.bvar 0)) minors) .default

end VG
