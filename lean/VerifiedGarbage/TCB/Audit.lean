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
  give it a name. Each registration file proves it, as a theorem whose
  statement, which the kernel checks, and whose axioms this reads (`declaredApis`).

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

/-- The elements of the list literal `e`. -/
partial def literalElems (e : Expr) (acc : Array Expr := #[]) : MetaM (Array Expr) :=
  match e.getAppFnArgs with
  | (``List.cons, #[_, a, as]) => literalElems as (acc.push a)
  | (``List.nil, _) => return acc
  | _ => throwError "not a literal list:{indentExpr e}"

/-- The theorem `thm`, which depends on no axiom but the standard ones (so that the kernel
has checked its proof: a module that imports it does not see it, nor whether it is
a theorem), is `∀ a ∈ e, apiOf a ∈ specs`, for a literal list `specs`: the elements of it
that are not `isSpecApi`. Where `specs` is found, in the statement of `thm`, is not trusted:
the kernel checks that `thm` proves the statement made here with it. `e` is a list of
elements of type `α`. -/
def declaredApis (e α : Expr) (apiOf : Expr → Expr) (thm : Name) : MetaM (Array Expr) := do
  let env ← getEnv
  unless env.contains thm do throwError "there is no {thm}, which `spec_apis {e}` declares"
  let axs := (AuditRecords.axiomsIn env thm).filter (!AuditRecords.standardAxioms.contains ·)
  unless axs.isEmpty do throwError "{thm} depends on non-standard axioms: {axs.toList}"
  let .forallE _ _ (.forallE _ _ c _) _ ← Meta.inferType (mkConst thm)
    | throwError "{thm} does not state the `Api`s of {e}"
  let (``Membership.mem, #[_, _, _, specs, _]) := c.getAppFnArgs
    | throwError "{thm} does not state the `Api`s of {e}"
  if specs.hasLooseBVars then throwError "{thm} does not state the `Api`s of {e}"
  let type ← Meta.withLocalDeclD `a α fun a => do
    Meta.mkForallFVars #[a] (← mkArrow (← Meta.mkAppM ``Membership.mem #[e, a])
      (← Meta.mkAppM ``Membership.mem #[specs, apiOf a]))
  addDecl <| .thmDecl { name := ← mkAuxDeclName `specApis, levelParams := [], type, value := mkConst thm }
  return (← literalElems specs).filter (!isSpecApi env ·)

/-- `#assert_spec_apis as …`, where each `as` is a registration file's list of artifacts
(`List (Artifact T)`), or a list of `Api`s. For each, it has the kernel check
`∀ a ∈ as, a.api ∈ specs`, for a list `specs` of `Api`s each of which is `isSpecApi`, or
fails: by the theorem `as_specApis` that the file of `as`, a constant, declares
(`declaredApis`; `spec_apis` of `Proof/Framework/SpecApis.lean`, which is not trusted, finds it).
So a registration file need not expose its list, nor what that is of. Each has the limits of a
command to itself. -/
elab "#assert_spec_apis " ts:(ppSpace colGt term:max)* : command => liftTermElabM do
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
      let some n := e.constName? | throwErrorAt t "not a constant"
      declaredApis e α apiOf (n.appendAfter "_specApis"))
  unless bad.isEmpty do
    throwError m!"these artifacts' `Api`s are not ones `Spec/` declares:{
      MessageData.joinSep (bad.toList.map fun a => m!"{indentExpr a}") ""}"
  logInfo m!"every artifact's `Api` is one `Spec/` declares"

end VG
