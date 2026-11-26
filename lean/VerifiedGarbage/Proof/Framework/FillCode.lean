module

public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Meta.WHNF

/-!
# `fill_code`: code that differs only in what it calls

Untrusted: this only changes how proofs are found; the kernel checks them.

The cleanup of a function generic over what it calls needs a proof of
`R a b`, `R` a relation such as `X86_64.Scrub.Fill k n`: `a` is the
function's code with a stub, and `b` its code with an implementation. `R` is
an inductive predicate with a constructor for each of `Code`'s, named as it
is, and others for the stub's holes (`hole`, …), whose hypotheses the
context has.

`fill_code` unfolds the two codes together, a definition at a time, until
they are equal, when `R.refl` proves the goal without looking inside, or
each is a constructor of `Code`, when it applies a rule and goes on with
what it needs. Projections of structures built in the code's arguments (the
fields of a callee) are reduced as it goes, so that code of both sides that
is built from the same fields is the same term. A pair of codes met again
has the proof it had. What it cannot prove it leaves as goals, and fails
where no rule applies to the first.

This is an order of magnitude faster than `refine`ing the rules one after
the other in a `repeat'`: each then unfolds both codes again for every rule
that does not apply, and code the two sides share is walked to its blocks,
whose instructions are compared.
-/

public meta section

namespace VG.FillCode

open Lean Meta Elab Tactic

/-- The constructor `e` is an application of. -/
def ctor? (e : Expr) : MetaM (Option Name) := do
  let .const n _ := e.getAppFn | return none
  let some (.ctorInfo _) := (← getEnv).find? n | return none
  return some n

/-- `e` with the projections of structures it builds reduced, and a number
computed from them (a function's value, of a term with variables) unfolded
where that leaves no variable in it: Lean computes only with closed terms. -/
partial def norm (e : Expr) : MetaM Expr :=
  transform e (usedLetOnly := true) (pre := fun e => do
    match e with
    | .proj _ i s =>
      let s' ← whnf s
      let some c ← ctor? s' | return .continue
      let some (.ctorInfo c) := (← getEnv).find? c | return .continue
      return .visit (s'.getArg! (c.numParams + i))
    | .app .. =>
      let .const n _ := e.getAppFn | return .continue
      let some info ← getProjectionFnInfo? n |
        unless e.hasFVar && !e.hasLooseBVars do return .continue
        let some c := (← getEnv).find? n | return .continue
        unless c.type.getForallBody.isConstOf ``Nat do return .continue
        let some e' ← unfoldDefinition? e | return .continue
        let e' ← norm e'
        return if e'.hasFVar then .continue else .done e'
      unless info.numParams < e.getAppNumArgs && !info.fromClass do return .continue
      let args := e.getAppArgs
      let s' ← whnf args[info.numParams]!
      let some c ← ctor? s' | return .continue
      unless c == info.ctorName do return .continue
      return .visit ((s'.getArg! (info.numParams + info.i)).beta (args.extract (info.numParams + 1) args.size))
    | _ => return .continue)

/-- One step of evaluating `e`, if there is one. A projection of what is not
built by a constructor stays as it is. -/
def step? (e : Expr) : MetaM (Option Expr) := do
  let e' ← whnfCore e
  if e' != e then return some e'
  if e.isAppOfArity ``ite 5 || e.isAppOfArity ``dite 5 then
    let args := e.getAppArgs
    let d ← whnf (mkApp2 (mkConst ``Decidable.decide) args[1]! args[2]!)
    if d.isConstOf ``Bool.true || d.isConstOf ``Bool.false then return (← unfoldDefinition? e)
    return none
  if let .const n _ := e.getAppFn then
    if (← getProjectionFnInfo? n).isSome then return none
  if let some e' ← unfoldDefinition? e then return some e'
  -- A recursion on a number that is yet to be computed.
  let args ← e.getAppArgs.mapM fun a => do
    if a.isRawNatLit || a.isAppOf ``OfNat.ofNat || a.hasFVar || !(← inferType a).isConstOf ``Nat then return a
    let v ← whnf a
    return if v.isRawNatLit then v else a
  let e' := mkAppN e.getAppFn args
  return if e' == e then none else some e'

/-- `a` and `b` evaluated together, until they are the same term (if `refl`),
or neither goes on. -/
partial def sync (refl : Bool) (a b : Expr) : MetaM (Expr × Expr) := do
  if refl && a == b then return (a, b)
  let na ← norm a
  let nb ← norm b
  if refl && na == nb then return (na, nb)
  if (na.getAppFn.constName?.any (·.getString! == "holeStub")) then return (na, nb)
  let sa ← if (← ctor? na).isSome then pure none else step? na
  let sb ← if (← ctor? nb).isSome then pure none else step? nb
  if sa.isNone && sb.isNone then return (na, nb)
  sync refl (sa.getD na) (sb.getD nb)

/-- Whether `e` is `.block []`, or a call of it. -/
partial def emptyBlock (e : Expr) : MetaM Bool := do
  let e ← whnf e
  let some c ← ctor? e | return false
  match c.getString! with
  | "block" => return (← whnf e.appArg!).isAppOf ``List.nil
  | "call" => emptyBlock e.appArg!
  | _ => return false

/-- `e` with the functions applied to variables unfolded, where that leaves
no variable in them. -/
partial def unfoldVars (fuel : Nat) (e : Expr) : MetaM Expr := do
  if !e.hasFVar then return e
  let e ← norm e
  if !e.hasFVar || fuel == 0 then return e
  transform e (pre := fun e => do
    unless e.isApp && e.hasFVar && !e.hasLooseBVars && e.getAppFn.isConst do return .continue
    let some e' ← unfoldDefinition? e | return .continue
    let e' ← unfoldVars (fuel - 1) e'
    return if e'.hasFVar then .continue else .done e')

/-- The elements of the list `e`, if it can be evaluated. -/
partial def elems? (e : Expr) : MetaM (Option (Array Expr)) := do
  let e ← norm (← whnfCore e)
  let args := e.getAppArgs
  match e.getAppFn.constName?, args.size with
  | some ``List.nil, 1 => return some #[]
  | some ``List.cons, 3 =>
    let some l ← elems? args[2]! | return none
    return some (#[args[1]!] ++ l)
  | some ``HAppend.hAppend, 6 | some ``List.append, 3 =>
    let some l ← elems? args[args.size - 2]! | return none
    let some l' ← elems? args.back! | return none
    return some (l ++ l')
  | some ``List.range, 1 =>
    let .ok (.lit (.natVal n)) := Kernel.whnf (← getEnv) (← getLCtx) (← unfoldVars 4 args[0]!) | return none
    return some ((Array.range n).map mkNatLit)
  | some ``List.flatMap, 4 =>
    let some l ← elems? args[3]! | return none
    let mut r := #[]
    for x in l do
      let some l ← elems? (args[2]!.beta #[x]) | return none
      r := r ++ l
    return some r
  | some ``List.map, 4 =>
    let some l ← elems? args[3]! | return none
    return some (l.map fun x => args[2]!.beta #[x])
  | _, _ =>
    let some e ← step? e | return none
    elems? e

/-- The instructions `is` written out, if that leaves no variable in them. -/
def instrs? (is : Expr) : MetaM (Option Expr) := do
  let some l ← elems? is | return none
  if l.isEmpty then return none
  let l ← l.mapM fun i => do unfoldVars 4 (← whnf (← norm i))
  if l.any fun i => i.hasFVar || i.hasMVar then return none
  some <$> mkListLit (← inferType l[0]!) l.toList

/-- The rules of a relation, by name, that fill a hole. -/
def holeRules : List String := ["hole", "budget", "icalls"]

structure State where
  cache : Std.HashMap (Expr × Expr) Expr := {}
  left : Array MVarId := #[]

abbrev M := StateRefT State MetaM

/-- A hypothesis that proves `p`. -/
def hyp? (p : Expr) : MetaM (Option Expr) := do
  for tr in [TransparencyMode.reducible, .default] do
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      let body := if p.isForall then ty else ty.getForallBody
      if p.isForall then
        unless ty.isForall do continue
      else
        unless body.getAppFn == p.getAppFn && body.getAppNumArgs == p.getAppNumArgs do continue
      -- An equation's left sides: the same predicate of code.
      if p.isAppOfArity ``Eq 3 then
        unless (p.getArg! 1).getAppFn == (body.getArg! 1).getAppFn do continue
      let h? ← withTransparency tr <| withNewMCtxDepth do
        let (xs, _, ty) ← if p.isForall then pure (#[], #[], ty) else forallMetaTelescope ty
        unless ← isDefEq ty p do return none
        let h ← instantiateMVars (mkAppN d.toExpr xs)
        return if h.hasExprMVar then none else some h
      if h?.isSome then return h?
  return none

/-- The goals of `rule` on `goal`, if it applies. -/
def apply? (rule : Name) (goal : Expr) : MetaM (Option (Expr × Array Expr)) := do
  let c ← mkConstWithFreshMVarLevels rule
  let (xs, _, ty) ← forallMetaTelescopeReducing (← inferType c)
  unless ← (withReducible <| isDefEq ty goal) <||> isDefEq ty goal do return none
  let mut gs := #[]
  for x in xs do
    unless ← x.mvarId!.isAssigned do gs := gs.push x
  return some (mkAppN c xs, gs)

mutual

/-- A proof of `R … a b`, `rel` the relation `R …`. -/
partial def prove (rel a b : Expr) : M Expr := do
  if let some p := (← get).cache[(a, b)]? then return p
  let p ← prove' rel a b
  modify fun s => { s with cache := s.cache.insert (a, b) p }
  return p

partial def prove' (rel a b : Expr) : M Expr := do
  let R := rel.getAppFn.constName!
  let env ← getEnv
  let goal := mkApp2 rel a b
  if let some h ← withReducible <| hyp? goal then return h
  let refl := env.contains (R ++ `refl)
  let (a', b') ← sync refl a b
  let goal' := mkApp2 rel a' b'
  if refl && a' == b' then
    if let some (p, #[]) ← apply? (R ++ `refl) goal' then return p
  let hole ← (do
    if a'.getAppFn.constName?.any (·.getString! == "holeStub") then return true
    emptyBlock a')
  -- The instructions of two blocks are the same: written out, so that the
  -- kernel compares each block with them, and not one with the other, which,
  -- where the two are a function of different arguments (the stub and the
  -- implementation), compares those arguments first, down to the names in
  -- them, in vain, and then those of the function's every call.
  if !hole && !a'.hasFVar && (← ctor? a').any (·.getString! == "block") && (← ctor? b').any (·.getString! == "block") then
    let rule := if env.contains (R ++ `block) then R ++ `block else R ++ `refl
    if let some is := ← (if env.contains rule then instrs? b'.appArg! else pure none) then
      if let some (p, #[]) ← apply? rule (mkApp2 rel (mkApp a'.appFn! is) (mkApp b'.appFn! is)) then
        return ← instantiateMVars p
  let mut rules : Array Name := #[]
  if hole then rules := holeRules.toArray.map (R ++ .mkSimple ·)
  if b'.getAppFn.constName?.any (·.getString! == "icalls") then rules := rules.push (R ++ `tab)
  if a' == b' then rules := rules.push (R ++ `same)
  if let some c ← ctor? a' then rules := rules.push (R ++ .mkSimple c.getString!)
  if b'.isAppOf ``ite then
    rules := if a'.isAppOf ``ite then rules ++ #[R ++ `ifp, R ++ `ite_same] else rules ++ #[R ++ `if_pos, R ++ `if_neg]
  rules := rules.filter env.contains
  for r in rules do
    let s ← Meta.saveState
    if let some (p, gs) ← apply? r goal' then
      if ← close rel gs then return ← instantiateMVars p
    (s.restore : MetaM Unit)
  let g ← mkFreshExprSyntheticOpaqueMVar goal
  modify fun s => { s with left := s.left.push g.mvarId! }
  return g

/-- Proves the goals of a rule: the relation's by `prove`, the others by a
hypothesis. The hypotheses first: a rule that lacks one does not apply. -/
partial def close (rel : Expr) (gs : Array Expr) : M Bool := do
  let mut codes := #[]
  for g in gs do
    if ← g.mvarId!.isAssigned then continue
    let ty ← instantiateMVars (← g.mvarId!.getType)
    if ty.getForallBody.getAppFn == rel.getAppFn then
      codes := codes.push (g, ty)
    else if ← isProp ty then
      let some h ← hyp? ty | return false
      g.mvarId!.assign h
    else return false
  for (g, ty) in codes do
    if ty.isForall then
      -- In the context of its hypothesis, which the cache has no part in.
      let cache := (← get).cache
      g.mvarId!.assign <| ← forallTelescope ty fun xs ty => do
        mkLambdaFVars xs (← prove ty.appFn!.appFn! ty.appFn!.appArg! ty.appArg!)
      modify fun s => { s with cache }
    else
      g.mvarId!.assign (← prove ty.appFn!.appFn! ty.appFn!.appArg! ty.appArg!)
  return true

end

/-- Proves `R a b`, of a function's code over a stub and over an
implementation (this module's documentation). -/
elab "fill_code" : tactic => liftMetaTactic fun g => g.withContext do
  let ty ← instantiateMVars (← g.getType)
  let ty ← if ty.getAppFn.isConst && ty.getAppNumArgs ≥ 2 then pure ty else whnfR ty
  unless ty.getAppFn.isConst && ty.getAppNumArgs ≥ 2 do throwError "fill_code: not a relation of two codes: {ty}"
  let (p, s) ← (prove ty.appFn!.appFn! ty.appFn!.appArg! ty.appArg!).run {}
  -- No rule applied.
  if p.isMVar then throwError "fill_code: no rule of the relation applies"
  g.assign p
  return s.left.toList

end VG.FillCode
