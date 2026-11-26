module

public meta import Lean.Elab.Command
public meta import Lean.Meta.AppBuilder
public meta import Lean.Meta.WHNF

/-!
# Proving which `Api`s a registration file's artifacts are of

Untrusted: the kernel checks the theorem it declares, and the emitter's
driver (`#assert_spec_apis`, `TCB/Audit.lean`) what that states.
-/

public meta section

namespace VG.SpecApis

open Lean Elab Command

/-- Whether the constant `c` is declared in a module under `VerifiedGarbage.Spec`. -/
def declaredInSpec (env : Environment) (c : Name) : Bool :=
  match env.getModuleIdxFor? c with
  | some i => (`VerifiedGarbage.Spec).isPrefixOf env.header.moduleNames[i.toNat]!
  | none => false

/-- Whether `e` is an `Api` that `Spec/` declares: a constant of `Spec/`, or a
function of `Spec/` applied to one. -/
def isSpecApi (env : Environment) : Expr → Bool
  | .const c _ => declaredInSpec env c
  | .app (.const f _) (.const c _) => declaredInSpec env f && declaredInSpec env c
  | _ => false

/-- `e` reduced, unfolding nothing `Spec/` declares. -/
def whnfToSpec (e : Expr) : MetaM Expr := do
  let env ← getEnv
  Meta.withCanUnfoldPred (fun _ ci => return !declaredInSpec env ci.name) do
    return (← Meta.whnf e).consumeMData

/-- `e`, an `Api`, as `isSpecApi` wants it, if it can be. -/
def reduceApi (e : Expr) : MetaM Expr := do
  match ← whnfToSpec e with
  | .app f x => return .app f (← whnfToSpec x)
  | e => return e

/-- The elements of the list `e`, as terms. The kernel reduces it, as it will to check
them. -/
partial def listElems (e : Expr) : MetaM (Array Expr) := do
  let rec go (e : Expr) (acc : Array Expr) : MetaM (Array Expr) := do
    let e ← ofExceptKernelException (Kernel.whnf (← getEnv) (← getLCtx) e)
    match e.getAppFnArgs with
    | (``List.cons, #[_, a, as]) => go as (acc.push a)
    | (``List.nil, _) => return acc
    | _ => throwError "not a list of known length:{indentExpr e}"
  go e #[]

/-- `iff.mpr h`, for an `iff` whose right side `h` proves, as the kernel will find. -/
def iffMpr (iff h : Expr) : MetaM Expr := do
  let some (a, b) := (← Meta.inferType iff).iff? | throwError "not an iff:{indentExpr iff}"
  return mkApp4 (mkConst ``Iff.mpr) a b iff h

/-- A proof of `∀ x ∈ es, P x`, for the list of `es`, given one of each `P x`. -/
def forallElems (α P : Expr) (es : Array Expr) (proof : Expr → MetaM Expr) : MetaM Expr := do
  let mut rest ← Meta.mkAppOptM ``List.forall_mem_nil #[α, P]
  let mut l ← Meta.mkListLit α []
  for x in es.reverse do
    let iff ← Meta.mkAppOptM ``List.forall_mem_cons #[α, P, x, l]
    let some (_, b) := (← Meta.inferType iff).iff? | throwError "not an iff:{indentExpr iff}"
    rest ← iffMpr iff (mkApp4 (mkConst ``And.intro) (b.getArg! 0) (b.getArg! 1) (← proof x) rest)
    l ← Meta.mkAppM ``List.cons #[x, l]
  return rest

/-- A proof of `∀ x ∈ e, P x`, for `e : List α`, given one (`leaf`) of `P x` of each `x`
that may be an element of `e`: those of both branches of an `if`, which a registration
may decide by a property of every variant that would take the kernel minutes. It evaluates
a list that `e` maps over, but not `e`. -/
partial def forallProof (α P : Expr) (leaf : Expr → MetaM Expr) (e : Expr) : MetaM Expr := do
  let e := e.consumeMData.headBeta
  let append (a b : Expr) : MetaM Expr := do
    let iff ← Meta.mkAppOptM ``List.forall_mem_append #[α, P, a, b]
    let some (_, r) := (← Meta.inferType iff).iff? | throwError "not an iff:{indentExpr iff}"
    iffMpr iff (mkApp4 (mkConst ``And.intro) (r.getArg! 0) (r.getArg! 1)
      (← forallProof α P leaf a) (← forallProof α P leaf b))
  -- A proof by cases on `c`, where `e = l h` by `eq h` for `h : c`, or `h : ¬ c`.
  let cases (c inst : Expr) (t f : Expr → Expr) (pos neg : Name) : MetaM Expr := do
    let motive ← Meta.withLocalDeclD `l (← Meta.mkAppM ``List #[α]) fun l => do
      Meta.mkLambdaFVars #[l] (← Meta.withLocalDeclD `x α fun x => do
        let mem ← Meta.mkAppM ``Membership.mem #[l, x]
        Meta.mkForallFVars #[x] (← mkArrow mem (mkApp P x)))
    let args := e.getAppArgs
    let case (h : Expr) (l : Expr → Expr) (eq : Name) : MetaM Expr :=
      Meta.withLocalDeclD `h h fun h => do
        let l := (l h).headBeta
        let eq ← Meta.mkAppOptM eq #[c, inst, h, args[0]!, args[3]!, args[4]!]
        Meta.mkLambdaFVars #[h] (mkAppN (mkConst ``Eq.subst [← Meta.getLevel args[0]!])
          #[args[0]!, motive, l, e, ← Meta.mkEqSymm eq, ← forallProof α P leaf l])
    Meta.mkAppOptM ``Decidable.byCases
      #[c, (mkApp motive e).headBeta, inst, ← case c t pos, ← case (mkNot c) f neg]
  match e.getAppFnArgs with
  | (``HAppend.hAppend, #[_, _, _, _, a, b]) => append a b
  | (``Append.append, #[_, _, a, b]) => append a b
  | (``List.append, #[_, a, b]) => append a b
  | (``List.cons, #[_, x, xs]) =>
    let iff ← Meta.mkAppOptM ``List.forall_mem_cons #[α, P, x, xs]
    let some (_, r) := (← Meta.inferType iff).iff? | throwError "not an iff:{indentExpr iff}"
    iffMpr iff (mkApp4 (mkConst ``And.intro) (r.getArg! 0) (r.getArg! 1) (← leaf x)
      (← forallProof α P leaf xs))
  | (``List.nil, _) => Meta.mkAppOptM ``List.forall_mem_nil #[α, P]
  | (``List.map, #[β, _, f, vs]) =>
    let Q ← Meta.withLocalDeclD `v β fun v => Meta.mkLambdaFVars #[v] (mkApp P (mkApp f v))
    iffMpr (← Meta.mkAppOptM ``List.forall_mem_map #[β, α, f, vs, P])
      (← forallElems β Q (← listElems vs) fun v => leaf (mkApp f v).headBeta)
  | (``List.flatMap, #[β, _, f, vs]) =>
    let Q ← Meta.withLocalDeclD `v β fun v => do
      Meta.mkLambdaFVars #[v] (← Meta.withLocalDeclD `x α fun x => do
        let mem ← Meta.mkAppM ``Membership.mem #[mkApp f v, x]
        Meta.mkForallFVars #[x] (← mkArrow mem (mkApp P x)))
    iffMpr (← Meta.mkAppOptM ``List.forall_mem_flatMap #[α, β, P, vs, f])
      (← forallElems β Q (← listElems vs) fun v => forallProof α P leaf (mkApp f v))
  | (``dite, #[_, c, inst, t, f]) =>
    cases c inst (mkApp t ·) (mkApp f ·) ``dite_eq_left ``dite_eq_right
  | (``ite, #[_, c, inst, t, f]) =>
    cases c inst (fun _ => t) (fun _ => f) ``ite_eq_left ``ite_eq_right
  | _ =>
    let e' ← Meta.whnfCore e
    if e' != e then return ← forallProof α P leaf e'
    if let .reduced e' ← Meta.withTransparency .default (Meta.reduceMatcher? e) then
      return ← forallProof α P leaf e'
    if let some e' ← Meta.unfoldDefinition? e then return ← forallProof α P leaf e'
    forallElems α P (← listElems e) leaf

/-- `spec_apis artifacts`, after a registration file's list of artifacts
(`List (Artifact T)`, or a list of `Api`s): declares the theorem `artifacts_specApis` that the `Api` of each is
one of a list of `Api`s that `Spec/` declares (`isSpecApi`). -/
elab "spec_apis " id:ident : command => liftTermElabM do
  let api := mkConst `VG.Api
  let env ← getEnv
  let n ← realizeGlobalConstNoOverloadWithInfo id
  let e := mkConst n
  let (``List, #[α]) := (← instantiateMVars (← Meta.whnf (← Meta.inferType e))).getAppFnArgs
    | throwErrorAt id "not a list"
  let apiOf ← match α.getAppFnArgs with
    | (`VG.Api, #[]) => pure fun a => a
    | (`VG.Artifact, #[T]) => pure fun a => mkApp2 (mkConst `VG.Artifact.api) T a
    | _ => throwErrorAt id "not a list of artifacts or of `Api`s"
  -- The `Api`s its elements have (`specs`), found as it is proven that each is one of them
  -- (`hs`): both to be filled in once all are.
  let specs ← Meta.mkFreshExprSyntheticOpaqueMVar (mkApp (mkConst ``List [1]) api)
  -- What must be proven: `P` of every element of `e`.
  let P ← Meta.withLocalDeclD `a α fun a => do
    Meta.mkLambdaFVars #[a] (← Meta.mkAppM ``Membership.mem #[specs, apiOf a])
  let found ← IO.mkRef (#[] : Array Expr)
  let hs ← IO.mkRef (#[] : Array Expr)
  let proof ← forallProof α P (leaf := fun a => do
    let x ← reduceApi (apiOf a)
    if let some i := (← found.get).findIdx? (· == x) then return (← hs.get)[i]!
    -- Any other is reported, and the proof not used.
    let mut h := mkConst ``True.intro
    if isSpecApi env x then
      let t ← Meta.mkAppM ``Membership.mem #[specs, x]
      h ← Meta.mkFreshExprMVarAt {} {} t .syntheticOpaque
    found.modify (·.push x)
    hs.modify (·.push h)
    return h) e
  let xs ← found.get
  let bad := xs.filter (!isSpecApi env ·)
  unless bad.isEmpty do
    throwErrorAt id m!"these artifacts' `Api`s are not ones `Spec/` declares:{
      MessageData.joinSep (bad.toList.map fun a => m!"{indentExpr a}") ""}"
  specs.mvarId!.assign (← Meta.mkListLit api xs.toList)
  for h : i in [:xs.size] do
    let mut p := mkApp3 (mkConst ``List.Mem.head [1]) api xs[i]
      (← Meta.mkListLit api (xs.toList.drop (i + 1)))
    for j in (List.range i).reverse do
      p := mkApp5 (mkConst ``List.Mem.tail [1]) api xs[i] xs[j]!
        (← Meta.mkListLit api (xs.toList.drop (j + 1))) p
    (← hs.get)[i]!.mvarId!.assign p
  let value ← instantiateMVars proof
  let P ← instantiateMVars P
  let type ← Meta.withLocalDeclD `a α fun a => do
    let mem ← Meta.mkAppM ``Membership.mem #[e, a]
    Meta.mkForallFVars #[a] (← mkArrow mem (mkApp P a).headBeta)
  addDecl <| .thmDecl { name := n.appendAfter "_specApis", levelParams := [], type, value }

end VG.SpecApis
