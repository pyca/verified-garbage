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

/-- `e` reduced, unfolding nothing `Spec/` declares. Not trusted: the kernel checks
what it finds. -/
def whnfToSpec (e : Expr) : MetaM Expr := do
  let env ← getEnv
  Meta.withCanUnfoldPred (fun _ ci => return !declaredInSpec env ci.name) do
    return (← Meta.whnf e).consumeMData

/-- `e`, an `Api`, as `isSpecApi` wants it, if it can be. Not trusted, as `whnfToSpec`. -/
def reduceApi (e : Expr) : MetaM Expr := do
  match ← whnfToSpec e with
  | .app f x => return .app f (← whnfToSpec x)
  | e => return e

/-- The elements of the list `e`, as terms. Not trusted, as `whnfToSpec`. The kernel
reduces it, as it will to check them: a list may be one of those that a decidable
property of many variants chooses between, which Lean's elaborator is too slow to
decide. -/
partial def listElems (e : Expr) : MetaM (Array Expr) := do
  let rec go (e : Expr) (acc : Array Expr) : MetaM (Array Expr) := do
    let e ← ofExceptKernelException (Kernel.whnf (← getEnv) {} e)
    match e.getAppFnArgs with
    | (``List.cons, #[_, a, as]) => go as (acc.push a)
    | (``List.nil, _) => return acc
    | _ => throwError "not a list of known length:{indentExpr e}"
  go e #[]

/-- `#assert_spec_apis as …`, where each `as : List Api` is one a driver lists the
artifacts of a registration file by. Each list is checked by a theorem of its own,
within the limits of one command. -/
elab "#assert_spec_apis " ts:(ppSpace colGt term:max)* : command => liftTermElabM do
  let api := mkConst `VG.Api
  let ty := mkApp (mkConst ``List [1]) api
  let env ← getEnv
  let mut bad : Array MessageData := #[]
  let mut count : Nat := 0
  for t in ts do
    let (b, n) ← withCurrHeartbeats do
      let e ← Term.elabTermEnsuringType t ty
      Term.synthesizeSyntheticMVarsNoPostponing
      let e ← instantiateMVars e
      let apis ← (← listElems e).mapM (reduceApi ·)
      let b := (apis.filter (!isSpecApi env ·)).map fun a => m!"{indentExpr a}"
      if b.isEmpty then
        let rhs ← Meta.mkListLit api apis.toList
        -- The kernel checks that those are the `Api`s of `e`.
        addDecl <| .thmDecl {
          name := ← mkAuxDeclName `specApis
          levelParams := []
          type := mkApp3 (mkConst ``Eq [2]) ty e rhs
          value := mkApp2 (mkConst ``Eq.refl [2]) ty rhs }
      return (b, apis.size)
    bad := bad ++ b
    count := count + n
  unless bad.isEmpty do
    throwError m!"these artifacts' `Api`s are not ones `Spec/` declares:{MessageData.joinSep bad.toList ""}"
  logInfo m!"the `Api`s of the {count} artifacts are ones `Spec/` declares"

end VG
