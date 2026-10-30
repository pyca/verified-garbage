module

public meta import Lean

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

Both refuse to run in a module, which sees what it imports from other
modules without their proofs, and without the values of definitions they
do not expose: the emitter's driver is not a module.
-/

public meta section

namespace VG

open Lean Elab Command

/-- The modules of this project, `VerifiedGarbage` and those under it, with
their indices in `env`. -/
def projectModules (env : Environment) : List (ModuleIdx × Name) :=
  -- `moduleNames` builds a new array of every module on each call: read it once.
  let names := env.header.moduleNames
  (List.range names.size).filterMap fun i =>
    let m := names[i]!
    if (`VerifiedGarbage).isPrefixOf m then some (i, m) else none

/-- Whether `env`, whose modules are `names` (`env.header.moduleNames`, which
callers read once), declares `n` in the module being elaborated or in a
module of this project, rather than in Lean or a dependency (whose constants
never depend on this project's). -/
def isProjectConst (env : Environment) (names : Array Name) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | none => true
  | some i => (`VerifiedGarbage).isPrefixOf names[i.toNat]!

/-- The constants of this project (`isProjectConst`) that the compiled code
of the constants `roots` may run in `env`: those their values use,
transitively (including `roots`). Types and proofs are erased from compiled
code, so it follows neither the types of constants nor the values of
theorems (whose names it still includes). -/
def dependencies (env : Environment) (roots : List Name) : NameSet := Id.run do
  let names := env.header.moduleNames
  let mut seen : NameSet := {}
  let mut todo := roots
  -- Visits each constant once, so it ends.
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail
    if seen.contains n || !isProjectConst env names n then continue
    seen := seen.insert n
    if let some ci := env.find? n then
      unless ci matches .thmInfo _ do
        if let some v := ci.value? (allowOpaque := true) then
          todo := v.getUsedConstants.toList ++ todo
  return seen

/-- What makes the compiled code of the constants `roots` depend on in `env`
differ from what the kernel checked (see the module docs): one line each. -/
def compilerOverrides (env : Environment) (roots : List Name) : List String :=
  let deps := (dependencies env roots).toList.mergeSort (·.toString ≤ ·.toString)
  deps.flatMap (fun n =>
    (if (Compiler.getImplementedBy? env n).isSome then [s!"@[implemented_by] on {n}"] else []) ++
    (if isExtern env n then [s!"@[extern] on {n}"] else []) ++
    (if (getExportNameFor? env n).isSome then [s!"@[export] on {n}"] else [])) ++
  (projectModules env).flatMap fun (i, m) =>
    let param {α} (attr : ParametricAttribute α) (what : String) : List String :=
      (attr.ext.getModuleEntries env i).toList.map fun (d, _) => s!"{m}: {what} {d}"
    param regularInitAttr "@[init] on" ++ param builtinInitAttr "@[builtin_init] on" ++
    (Compiler.CSimp.ext.ext.getModuleEntries env i).toList.map fun
      | .global e | .scoped _ e => s!"{m}: @[csimp] {e.thmName}"

elab "#assert_no_compiler_overrides " ids:ident* : command => do
  -- In a module, a definition imported from another module may be opaque,
  -- without its value: `dependencies` would not follow what it runs.
  if (← getEnv).header.isModule then
    throwError "#assert_no_compiler_overrides must run in a file that is not a module"
  let roots ← ids.toList.mapM fun id => liftCoreM <| realizeGlobalConstNoOverloadWithInfo id.raw
  let bad := compilerOverrides (← getEnv) roots
  unless bad.isEmpty do
    throwError m!"the compiled code of {roots} is not what the kernel checked:\n\
      {"\n".intercalate bad}"
  logInfo m!"the compiled code of {roots} is what the kernel checked"

/-- The constants named `VG.Spec.…` in `env` that are not theorems and are
declared outside the modules under `VerifiedGarbage.Spec` (in another
module, or in the one being elaborated), with their modules. -/
def specOutsideSpec (env : Environment) : List (Name × Name) :=
  let names := env.header.moduleNames
  env.constants.fold (init := []) fun acc n c =>
    if !(`VG.Spec).isPrefixOf n || c matches .thmInfo _ then acc else
      let m := match env.getModuleIdxFor? n with
        | none => env.mainModule
        | some i => names[i.toNat]!
      if (`VerifiedGarbage.Spec).isPrefixOf m then acc else (n, m) :: acc

elab "#assert_spec_origin" : command => do
  -- In a module, a theorem imported from another module is an axiom, which
  -- the check would not exempt as one.
  if (← getEnv).header.isModule then
    throwError "#assert_spec_origin must run in a file that is not a module"
  let bad := specOutsideSpec (← getEnv)
  unless bad.isEmpty do
    throwError m!"these `VG.Spec` names are not declared in `Spec/`:\n\
      {"\n".intercalate (bad.map fun (n, m) => s!"{n} (in {m})")}"
  logInfo m!"every `VG.Spec` definition is declared in `Spec/`"

/-! ## Audit digests

The emitter emits each target from a program that is a module, and relies
on that target's audit, a file that is not a module, which `lake build`
built (see "Drivers as modules" in `TCB/Emit.lean`). The audit is of what it
imported when it was built: if some of those modules were built again since
(`lake build +Module`, without the audit), the program would emit code the
audit never saw. So the audit records, as its last command, a digest of
everything it imported (`#record_audit_digest`), and the program, which
imports the same modules, checks before it emits that the digest of what it
imported is the same (`#check_audit_digest`).

The digest is of the modules' names and of Lake's hashes of the contents of
each one's `.olean`, `.olean.server`, `.olean.private` and `.ir`: the
digests of two files that imported the same modules are equal exactly when
every one of those outputs is the same (but for a collision of the 64-bit
hashes, which nothing here could arrange: the outputs are Lean's, of sources
that are reviewed). Lean's own modules, which come with the toolchain and
which Lake does not hash, are in it by name, with the toolchain's version.
An audit that failed records nothing: Lean writes no `.olean` for a file with
an error, so an audit of something else can only have an older digest. -/

/-- One line of the digest: the module `m`'s name and Lake's hashes of its
outputs, or only its name if it is one of Lean's own (in `coreDir`). Fails
if Lake has no hash of its `.olean`. -/
def digestLine (coreDir : String) (m : Name) : IO String := do
  let olean ← findOLean m
  if olean.toString.startsWith coreDir then return s!"{m} core"
  let base := (olean.withExtension "").toString
  let hashOf (part : String) : IO String := do
    let f : System.FilePath := s!"{base}.{part}.hash"
    if ← f.pathExists then return (← IO.FS.readFile f).trimAscii.toString else return "-"
  let o ← hashOf "olean"
  if o == "-" then throw <| IO.userError s!"{m}: Lake has no hash of {olean}"
  return s!"{m} {o} {← hashOf "olean.server"} {← hashOf "olean.private"} {← hashOf "ir"}"

/-- The digest of the modules `env` imported (see above). -/
def auditDigest (env : Environment) : IO String := do
  let coreDir := (← getLibDir (← getBuildDir)).toString ++ "/"
  let names := env.header.moduleNames.qsort (·.toString < ·.toString)
  let mut h : UInt64 := hash versionString
  for m in names do
    h := mixHash h (hash (← digestLine coreDir m))
  return s!"{versionString} {String.ofList (Nat.toDigits 16 h.toNat)}"

/-- `#record_audit_digest d` defines `d : String`, the digest of what the file
imported. An audit runs it after its audits, which it is then the digest of. -/
elab "#record_audit_digest " id:ident : command => do
  if (← getEnv).header.isModule then
    throwError "#record_audit_digest must run in a file that is not a module"
  let d ← auditDigest (← getEnv)
  elabCommand (← `(def $id : String := $(quote d)))

/-- `#check_audit_digest A d ok` defines `ok : Bool`: whether the module `A`,
an audit, defines `d` as the digest of what this file imported. False if
`A` has no `.olean` or no `d`, or if Lake has no hash of an output of a
module this file imported. -/
elab "#check_audit_digest " audit:ident digest:ident ok:ident : command => do
  let env ← getEnv
  let current ← try
      let (mod, _) ← readModuleData (← findOLean audit.getId)
      let recorded := (mod.constants.find? (·.name == digest.getId)).bind fun c =>
        match c.value? with
        | some (.lit (.strVal s)) => some s
        | _ => none
      pure (recorded == some (← auditDigest env))
    catch _ => pure false
  elabCommand (← `(def $ok : Bool := $(quote current)))

end VG
