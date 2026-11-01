module

public meta import Lean
public meta import VerifiedGarbage.TCB.AuditBase

/-!
# Audit records

**Trusted. Prototype.** The emitter's audits (`TCB/Axioms.lean`, `TCB/Audit.lean`)
walk the proofs and definitions of everything the artifacts depend on, so they run
in a file that is not a module, which loads every imported module's private data
(`.olean.private`). This module lets the same audits run in a module, which loads
none: when Lean writes a module's `.olean`, it records, for each constant the module
declares, what the audits need to know of it, computed from the module's own
kernel-checked declarations (proofs included, which the module has in memory then)
and the records of the modules it imports. The audit of the artifacts then combines
the records of what it imports (`problems`), without walking any imported proof.

* `constExt`: for each constant, the axioms its type and value depend on
  (transitively, as `collectAxioms`), and the constants of this project its compiled
  code may run (as `Audit.dependencies`) that carry `implemented_by`, `extern` or
  `export`.
* `moduleExt`: for each module, its constants named `VG.Spec.…` that are not
  theorems, and the `@[init]` declarations and `@[csimp]` theorems it declares. Every
  module that imports this one writes it, even empty: a module of this project
  without it was not built with the records, which `problems` reports.

Records are read from the entries of the imported `.olean` files, as Lean's own
`collectAxioms` reads its data: code running in a module that changed the
extension's state could forge them, as it could overwrite `.olean` files. A constant of Lean or a dependency (not of this project),
which writes no records, contributes the axioms `TCB/AuditBase.lean` lists for it, or
none but itself if it is one of the three standard axioms: that list is checked
against their private data (`lean/VerifiedGarbageAuditBase.lean`) whenever they
change.
-/

public meta section

namespace VG.AuditRecords

open Lean Elab Command

/-- Whether `m` is a module of this project. -/
def isProjectModule (m : Name) : Bool := (`VerifiedGarbage).isPrefixOf m

/-- A constant's record: its name, the axioms it depends on, and the constants of this
project its compiled code may run that carry `implemented_by`, `extern` or
`export`. -/
abbrev ConstRec := Name × Array Name × Array Name

/-- A module's record, of it and everything it imports (transitively, privately too,
as the code compiled in it may depend on any of them): the non-theorem `VG.Spec.…`
constants declared outside `Spec/`, the `@[init]` declarations, the `@[csimp]`
theorems, and the modules of this project written without records. -/
abbrev ModuleRec := Array Name × Array Name × Array Name × Array Name

/-- The module that declares the records: its `initialize` is the one this project may
declare. -/
def recordsModule : Name := `VerifiedGarbage.TCB.AuditRecords

/-- The modules built without the records, as they are what registers them (the
plugin every other library of this project loads, `lakefile.toml`): this one, and the
list it reads (data). -/
def unrecorded : List Name := [recordsModule, `VerifiedGarbage.TCB.AuditBase]



/-- The axioms the audit allows: Lean's `#print axioms` of most proofs. -/
def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- `TCB/AuditBase.lean`'s list, by name. -/
def baseAxioms : NameMap (Array Name) :=
  AuditBase.nonStandard.foldl (init := {}) fun m (c, axs) =>
    m.insert (AuditBase.parseName c) (axs.map AuditBase.parseName)

/-- The axioms a constant of Lean or a dependency depends on, as far as the audit is
concerned: the non-standard ones `TCB/AuditBase.lean` lists, or itself if it is a
standard axiom. -/
def axiomsOfBase (c : Name) : Array Name :=
  match baseAxioms.find? c with
  | some axs => axs
  | none => if standardAxioms.contains c then #[c] else #[]

/-- What `walk` needs of the environment it walks. -/
structure Ctx where
  env : Environment
  names : Array Name
  /-- The records of each imported module of this project, by module index. -/
  records : ModuleIdx → Array ConstRec
  /-- The module whose constants are walked rather than looked up: the one being
  elaborated (`none`), or, to write the records of an already built module
  from its private data, that module. -/
  ownModule : Option ModuleIdx := none
  /-- With `ownModule`: that module's constants, walked even where another module
  declares the same name (Lean realizes some declarations, e.g. equation lemmas, in
  each module that needs them), and every record computed so far, by name. -/
  ownNames : NameSet := {}
  lookup? : Option (Name → Option ConstRec) := none

/-- The record of the imported constant `c` of module `i`, if it has one. -/
def Ctx.find? (ctx : Ctx) (i : ModuleIdx) (c : Name) : Option ConstRec :=
  if let some f := ctx.lookup? then f c else
  (ctx.records i).binSearch (c, #[], #[]) (fun a b => Name.quickLt a.1 b.1)

/-- Where a constant comes from, as the walk sees it. -/
inductive Origin where
  /-- Declared in the environment being elaborated or written: walk its value. -/
  | own
  /-- Declared in an imported module of this project: use its record. -/
  | project (i : ModuleIdx)
  /-- Declared in Lean or a dependency: its compiled code is trusted, and its axioms are `TCB/AuditBase.lean`'s (`axiomsOfBase`). -/
  | other

def Ctx.origin (ctx : Ctx) (c : Name) : Origin :=
  if ctx.ownNames.contains c then .own else
  match ctx.env.getModuleIdxFor? c with
  | none => if ctx.ownModule.isNone then .own else .other
  | some i =>
    if ctx.ownModule == some i then .own
    else if isProjectModule ctx.names[i.toNat]! then .project i else .other

/-- The declaration of `c` in the environment being walked. `Environment.find?` misses
some constants the kernel checked: a declaration realized on another environment
branch under a name that is not reserved, such as the `_sparseCasesOn` helper of a
`match` splitter, which `Environment.find?` looks up only in the realizations of
reserved names. The kernel environment has every one, as `Lean.mkModuleData` relies
on when it writes the module's constants from it. -/
def Ctx.findConst? (ctx : Ctx) (c : Name) : Option ConstantInfo :=
  ctx.env.find? c <|> ctx.env.toKernelEnv.find? c

/-- Whether code may run something other than what the kernel checked for `c`. -/
def overridden (env : Environment) (c : Name) : Bool :=
  (Compiler.getImplementedBy? env c).isSome || isExtern env c || (getExportNameFor? env c).isSome

/-- The sentinel axiom a constant depends on when its record is missing: no standard
axiom, so the audit fails, naming it. -/
def missing (c : Name) : Name := `_missing_audit_record ++ c

structure State where
  axioms : NameMap (Array Name) := {}
  overrides : NameMap (Array Name) := {}

abbrev M := ReaderT Ctx (StateM State)

def sortDedup (xs : Array Name) : Array Name :=
  (xs.foldl (init := ({} : NameSet)) fun s x => s.insert x).toArray.qsort Name.lt

def ModuleRec.union (a b : ModuleRec) : ModuleRec :=
  let (s₁, i₁, c₁, u₁) := a
  let (s₂, i₂, c₂, u₂) := b
  (sortDedup (s₁ ++ s₂), sortDedup (i₁ ++ i₂), sortDedup (c₁ ++ c₂), sortDedup (u₁ ++ u₂))

/-- The axioms `c` depends on: those of its type and value, and, for an inductive, of
its constructors, as `collectAxioms`. -/
partial def axiomsOf (c : Name) : M (Array Name) := do
  if let some r := (← get).axioms.find? c then return r
  let ctx ← read
  let r ← match ctx.origin c with
    | .project i => pure <| match ctx.find? i c with
      | some (_, axs, _) => axs
      | none => #[missing c]
    | .other => pure (axiomsOfBase c)
    | .own =>
      -- Cycles (mutual definitions, inductives and their constructors) see the partial result.
      modify fun s => { s with axioms := s.axioms.insert c #[] }
      match ctx.findConst? c with
      | none => pure #[missing c]
      | some ci =>
        let own : Array Name := if ci matches .axiomInfo _ then #[c] else #[]
        let mut refs := ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then refs := refs ++ v.getUsedConstants
        if let .inductInfo v := ci then refs := refs ++ v.ctors.toArray
        let mut acc := own
        for r in refs do acc := acc ++ (← axiomsOf r)
        pure (sortDedup acc)
  modify fun s => { s with axioms := s.axioms.insert c r }
  return r

/-- The constants of this project the compiled code of `c` may run that carry
`implemented_by`, `extern` or `export`: as `Audit.dependencies`, it follows the
values of everything but theorems, and only into this project. -/
partial def overridesOf (c : Name) : M (Array Name) := do
  if let some r := (← get).overrides.find? c then return r
  let ctx ← read
  let r ← match ctx.origin c with
    | .other => pure #[]
    | .project i => pure <| match ctx.find? i c with
      | some (_, _, ovs) => ovs
      | none => #[missing c]
    | .own =>
      modify fun s => { s with overrides := s.overrides.insert c #[] }
      match ctx.findConst? c with
      | none => pure #[missing c]
      | some ci =>
        let mut acc : Array Name := if overridden ctx.env c then #[c] else #[]
        unless ci matches .thmInfo _ do
          if let some v := ci.value? (allowOpaque := true) then
            for r in v.getUsedConstants do acc := acc ++ (← overridesOf r)
        pure (sortDedup acc)
  modify fun s => { s with overrides := s.overrides.insert c r }
  return r

/-- The records of the constants `own`, which `ctx` walks (`Ctx.ownModule`). -/
def recordsOf (ctx : Ctx) (own : Array Name) : Array ConstRec :=
  let go : M (Array ConstRec) := own.mapM fun c => return (c, ← axiomsOf c, ← overridesOf c)
  let recs := Id.run ((go.run ctx).run' ({} : State))
  recs.qsort fun a b => Name.quickLt a.1 b.1

/-- The records of the constants this environment declares itself. -/
def ownRecords (ctx : Ctx) : Array ConstRec :=
  recordsOf ctx (ctx.env.constants.foldStage2 (fun ns n _ => ns.push n) #[])

/-- The module record (`ModuleRec`) of the constants `own` of `env`, declared in the
module `m`, without its imports'. -/
def moduleRecordOf (env : Environment) (m : Name) (own : Array (Name × ConstantInfo)) : ModuleRec :=
  let specs := if (`VerifiedGarbage.Spec).isPrefixOf m then #[] else own.filterMap fun (n, c) =>
    if (`VG.Spec).isPrefixOf n && !(c matches .thmInfo _) then some n else none
  let inits := own.filterMap fun (n, _) =>
    if (regularInitAttr.getParam? env n).isSome || (builtinInitAttr.getParam? env n).isSome ||
      isIOUnitInitFn env n || isIOUnitBuiltinInitFn env n then some n else none
  let csimps := own.filterMap fun (n, _) =>
    if Compiler.hasCSimpAttribute env n then some n else none
  (sortDedup specs, sortDedup inits, sortDedup csimps, #[])

/-- The union of the records of the modules of this project `env` loaded the data of,
given their entries (`entries i`): with the modules among them that have none. -/
def importedModuleRecord (env : Environment) (entries : ModuleIdx → Array ModuleRec) : ModuleRec := Id.run do
  let names := env.header.moduleNames
  let mut acc : ModuleRec := (#[], #[], #[], #[])
  for h : i in [:names.size] do
    let m := names[i]
    unless isProjectModule m && !unrecorded.contains m do continue
    unless env.header.modules[i]!.hasData do continue
    match (entries i)[0]? with
    | some r => acc := acc.union r
    | none => acc := acc.union (#[], #[], #[], #[m])
  return acc

/-- This environment's module record: its own, and its imports'. -/
def ownModuleRecord (env : Environment) (entries : ModuleIdx → Array ModuleRec) : ModuleRec :=
  (moduleRecordOf env env.mainModule (env.constants.foldStage2 (fun ns n c => ns.push (n, c)) #[])).union
    (importedModuleRecord env entries)

/-- The imported records, by module index: as `Lean.collectAxioms`'s own extension,
the state holds them because the export cannot name the extension it belongs to. -/
abbrev Imported := Array (Array ConstRec)

/-- The records `constExt` writes for `env`, given the imported ones. -/
def exportRecords (env : Environment) (imported : Imported) : Array ConstRec :=
  ownRecords { env, names := env.header.moduleNames, records := fun i => imported[i.toNat]?.getD #[] }

initialize constExt : PersistentEnvExtension ConstRec ConstRec Imported ←
  registerPersistentEnvExtension {
    name := `VG.AuditRecords.constExt
    mkInitial := pure #[]
    addImportedFn := fun mods => pure mods
    addEntryFn := fun s _ => s
    exportEntriesFnEx := fun env imported => .uniform (exportRecords env imported)
  }

initialize moduleExt : PersistentEnvExtension ModuleRec ModuleRec (Array (Array ModuleRec)) ←
  registerPersistentEnvExtension {
    name := `VG.AuditRecords.moduleExt
    mkInitial := pure #[]
    addImportedFn := fun mods => pure mods
    addEntryFn := fun s _ => s
    exportEntriesFnEx := fun env imported =>
      .uniform #[ownModuleRecord env fun i => imported[i.toNat]?.getD #[]]
  }

/-- The walk's view of `env`: imported records from the entries of the imported
`.olean` files. -/
def ctxOf (env : Environment) : Ctx :=
  { env, names := env.header.moduleNames,
    records := fun i => constExt.getModuleEntries env i }

/-- The axioms `c` depends on in `env`, from the records of what it imports (with the
sentinel `missing` for a constant whose record is missing). -/
def axiomsIn (env : Environment) (c : Name) : Array Name :=
  Id.run (((axiomsOf c).run (ctxOf env)).run' ({} : State))

/-- The constants of this project that the compiled code of `roots` may run in `env`
and that carry `implemented_by`, `extern` or `export` (`missing` for a record that
is), with the root that reaches each. -/
def overridesIn (env : Environment) (roots : List Name) : List (Name × Name) :=
  let go : M (List (Name × Name)) := roots.flatMapM fun r => return (← overridesOf r).toList.map (r, ·)
  Id.run ((go.run (ctxOf env)).run' ({} : State))

/-- The module record of `env`: of the constants it declares itself, and of the modules
of this project it loaded, with what they import. -/
def moduleRecordIn (env : Environment) : ModuleRec :=
  ownModuleRecord env fun i => moduleExt.getModuleEntries env i

/-- Lines of `moduleRecordIn`'s modules built without the records (`recordsModule`
aside, which cannot record itself). -/
def unrecordedIn (env : Environment) : List String :=
  (moduleRecordIn env).2.2.2.toList.map fun m => s!"{m}: no audit record (not built with {recordsModule})"

end VG.AuditRecords
