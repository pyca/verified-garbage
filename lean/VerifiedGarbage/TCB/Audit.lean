module

public meta import Lean
public meta import VerifiedGarbage.TCB.AuditRecords

/-!
# Environment audit

**Trusted.** Three checks the emitter runs (`Emit.driver`) on everything it
imports, besides the axiom audit (`TCB/Axioms.lean`):

* `#assert_no_compiler_overrides all run` fails if the compiler may run
  something other than what the kernel checked in the code the emitter runs.
  The emitter is compiled code: it evaluates the artifacts `all` (their code,
  signatures and documentation) and runs `run`, which prints and checks them
  (`Rust.files`), by running what the compiler made of their definitions.
  So nothing of this project they depend on, transitively, may carry
  `implemented_by`, `extern` or `export`, which substitute other code for a
  definition (or give one to a constant the kernel knows nothing of); what
  Lean and Mathlib implement so is trusted, as Lean is. And no module of this
  project (any that wrote audit records, or is named as one of this project's
  libraries, `AuditRecords.isProjectModule`) may declare a `csimp`
  theorem (or axiom), which the compiler rewrites by in whatever it compiles
  later, or an `init`/`builtin_init` (`initialize`), which runs when the
  emitter imports its module. Any of these could make the emitter write code
  other than the code that was proven, with every proof intact. Code the
  emitter does not run may use them: e.g. a tactic's `unsafe` term, whose
  results the kernel checks.
* `#assert_spec_origin` fails unless every constant named `VG.Spec.…` that
  is not a theorem is declared in a module under `VerifiedGarbage.Spec`. A
  reviewer reads a registration file's `Spec.<Alg>.fooContract` or
  `Spec.<Alg>.fooApi` as the reviewed one in `Spec/`, but a namespace is
  not a directory: an implementation's own files could declare such a name.
  Theorems (e.g. the equation lemmas Lean generates for a `Spec/` definition
  in the module that first unfolds it) carry no data and are exempt.
* `#assert_spec_apis as …` fails unless the kernel checks that each `Api` of
  the lists `as …` (each registration file's artifacts', `Artifact.api`) is one `Spec/` declares: a
  constant declared in a module under `VerifiedGarbage.Spec`, or a function
  declared there applied to one such constant and nothing else (as
  `Spec.Hmac.sha256I.pbkdf2Api`). `#assert_spec_origin` says it of names; this
  says it of what is emitted, whatever name a registration gives it: a
  declaration that its file takes for `Spec.<Alg>.fooApi` (one in a namespace
  that shadows `VG`'s), or a value that a proof builds artifacts with. An `Api`
  that needs anything else, such as a string, is not `Spec/`'s: `Spec/` must
  give it a name.

The first two walk the constants of the file they run in, and take what an imported
constant or module holds from the audit records its module wrote when it was
built (`TCB/AuditRecords.lean`), which saw its proofs and the values of its
definitions: so they run in a module too, which sees what it imports from other
modules without their proofs, and without the values of definitions they do not
expose. A module's records are read whatever its name, and a module of this
project built without the records fails both. The
records' own `initialize` (`TCB/AuditRecords.lean`, which registers them) is the one
this project declares: its module and `TCB/AuditBase.lean` write no records
(`AuditRecords.unrecorded`), so it reaches no audit, and no name is exempt (a
module may declare a constant in any namespace, `VG.AuditRecords` too).
-/

public meta section

namespace VG

open Lean Elab Command

/-- What makes the compiled code of the constants `roots` depend on in `env`
differ from what the kernel checked (see the module docs): one line each. -/
def compilerOverrides (env : Environment) (roots : List Name) : List String :=
  let (_, inits, csimps, _) := AuditRecords.moduleRecordIn env
  ((AuditRecords.overridesIn env roots).map fun (_, n) =>
    -- The attribute, if `env` has the constant's (an imported record of a module it
    -- did not load names it alone).
    if (Compiler.getImplementedBy? env n).isSome then s!"@[implemented_by] on {n}"
    else if isExtern env n then s!"@[extern] on {n}"
    else if (getExportNameFor? env n).isSome then s!"@[export] on {n}"
    else s!"@[implemented_by], @[extern] or @[export] on {n}") ++
  (inits.toList.map fun n => s!"@[init] on {n}") ++
  (csimps.toList.map fun n => s!"@[csimp] {n}") ++
  AuditRecords.unrecordedIn env

elab "#assert_no_compiler_overrides " ids:ident* : command => do
  let roots ← ids.toList.mapM fun id => liftCoreM <| realizeGlobalConstNoOverloadWithInfo id.raw
  let bad := compilerOverrides (← getEnv) roots
  unless bad.isEmpty do
    throwError m!"the compiled code of {roots} is not what the kernel checked:\n\
      {"\n".intercalate bad}"
  logInfo m!"the compiled code of {roots} is what the kernel checked"

/-- The constants named `VG.Spec.…` that are not theorems and are declared outside
`Spec/`, in `env` or a module of this project it loaded or what they import: one
line each, with the modules built without the records. -/
def specOutsideSpec (env : Environment) : List String :=
  let (specs, _, _, _) := AuditRecords.moduleRecordIn env
  let names := env.header.moduleNames
  (specs.toList.map fun n =>
    let m := match env.getModuleIdxFor? n with
      | none => if (env.find? n).isSome then env.mainModule else `«a module not loaded»
      | some i => names[i.toNat]!
    s!"{n} (in {m})") ++ AuditRecords.unrecordedIn env

elab "#assert_spec_origin" : command => do
  let bad := specOutsideSpec (← getEnv)
  unless bad.isEmpty do
    throwError m!"these `VG.Spec` names are not declared in `Spec/`:\n{"\n".intercalate bad}"
  logInfo m!"every `VG.Spec` definition is declared in `Spec/`"

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

/-! ### Finding and proving which `Api`s they are

None of this is trusted: the kernel checks the theorem it proves, whose statement
`#assert_spec_apis` states. -/

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

/-! ### The check -/

/-- `#assert_spec_apis as …`, where each `as` is a registration file's list of artifacts
(`List (Artifact T)`), or a list of `Api`s. For each, it proves `∀ a ∈ as, a.api ∈ specs`,
for a list `specs` of `Api`s each of which is `isSpecApi`, or fails. Each has the limits
of a command to itself. -/
elab "#assert_spec_apis " ts:(ppSpace colGt term:max)* : command => liftTermElabM do
  let api := mkConst `VG.Api
  let env ← getEnv
  let mut bad : Array Expr := #[]
  for t in ts do
    bad := bad ++ (← withCurrHeartbeats do
      let e ← Term.elabTerm t (some (mkApp (mkConst ``List [1]) (← Meta.mkFreshExprMVar (mkSort 2))))
      Term.synthesizeSyntheticMVarsNoPostponing
      let e ← instantiateMVars e
      let (``List, #[α]) := (← instantiateMVars (← Meta.whnf (← Meta.inferType e))).getAppFnArgs
        | throwErrorAt t "not a list"
      let apiOf ← match α.getAppFnArgs with
        | (`VG.Api, #[]) => pure id
        | (`VG.Artifact, #[T]) => pure fun a => mkApp2 (mkConst `VG.Artifact.api) T a
        | _ => throwErrorAt t "not a list of artifacts or of `Api`s"
      -- What must be proven, of the `Api`s `specs`: `P` of every element of `e`.
      let predicate (specs : Expr) : MetaM Expr := Meta.withLocalDeclD `a α fun a => do
        Meta.mkLambdaFVars #[a] (← Meta.mkAppM ``Membership.mem #[specs, apiOf a])
      -- The `Api`s its elements may have, found in a first run, whose proof is not used.
      let found ← IO.mkRef (#[] : Array Expr)
      let P ← predicate (← Meta.mkListLit api [])
      discard <| forallProof α P (leaf := fun a => do
        let x ← reduceApi (apiOf a)
        found.modify fun xs => if xs.contains x then xs else xs.push x
        return mkConst ``True.intro) e
      let xs ← found.get
      let b := xs.filter (!isSpecApi env ·)
      if b.isEmpty then
        let specs ← Meta.mkListLit api xs.toList
        let P ← predicate specs
        let proof ← forallProof α P (leaf := fun a => do
          let x ← reduceApi (apiOf a)
          let some i := xs.findIdx? (· == x) | throwError "not found before:{indentExpr x}"
          let mut p := mkApp3 (mkConst ``List.Mem.head [1]) api x
            (← Meta.mkListLit api (xs.toList.drop (i + 1)))
          for j in (List.range i).reverse do
            p := mkApp5 (mkConst ``List.Mem.tail [1]) api x xs[j]!
              (← Meta.mkListLit api (xs.toList.drop (j + 1))) p
          return p) e
        let type ← Meta.withLocalDeclD `a α fun a => do
          let mem ← Meta.mkAppM ``Membership.mem #[e, a]
          Meta.mkForallFVars #[a] (← mkArrow mem (mkApp P a).headBeta)
        addDecl <| .thmDecl { name := ← mkAuxDeclName `specApis, levelParams := [], type, value := proof }
      return b)
  unless bad.isEmpty do
    throwError m!"these artifacts' `Api`s are not ones `Spec/` declares:{
      MessageData.joinSep (bad.toList.map fun a => m!"{indentExpr a}") ""}"
  logInfo m!"every artifact's `Api` is one `Spec/` declares"

end VG
