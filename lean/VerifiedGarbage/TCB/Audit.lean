module

public meta import Lean
public meta import VerifiedGarbage.TCB.AuditRecords

/-!
# Environment audit

**Trusted.** Two checks the emitter runs (`Emit.driver`) on everything it
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
  project (`VerifiedGarbage` or a module under it) may declare a `csimp`
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

Both walk the constants of the file they run in, and take what an imported
constant or module holds from the audit records its module wrote when it was
built (`TCB/AuditRecords.lean`), which saw its proofs and the values of its
definitions: so they run in a module too, which sees what it imports from other
modules without their proofs, and without the values of definitions they do not
expose. A module of this project built without the records fails both. The
records' own `initialize` (`TCB/AuditRecords.lean`, which registers them) is the one
this project declares.
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
  ((inits.toList.filter fun n => !(`VG.AuditRecords).isPrefixOf n).map fun n => s!"@[init] on {n}") ++
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

end VG
