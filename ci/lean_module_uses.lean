import Lean

/-!
For `check_lean_public_imports.py`: the modules whose declarations each given
module's declarations use, as Lean sees them.

  lake env lean --run ../ci/lean_module_uses.lean (public | private | both | names) MOD...

`public`: what Lean checks as public uses, which need a `public import`: the
statements of the declarations an importer sees, and the bodies of exposed
definitions, followed into the auxiliary declarations elaboration splits off
them (a proof field becomes a private `_proof_N`). `lake shake` reads only the
exported data, where those proofs are references to the auxiliary
declarations, and so counts their uses as private. `private`: every
declaration, proofs of theorems too. Prints one JSON object, module ->
modules used (its own declarations' modules left out). `names`: each module's
exported declarations' names, read from its `.olean` alone.
-/

open Lean

def valueOf? : ConstantInfo → Option Expr
  | .defnInfo v => some v.value
  | .thmInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

/-- The constants `ci`'s type uses, and its value's if `body`. -/
def usedBy (ci : ConstantInfo) (body : Bool) : Array Name :=
  ci.type.getUsedConstants ++ (if body then ((valueOf? ci).map (·.getUsedConstants)).getD #[] else #[])

structure Uses where
  ordinary : Array String
  elaboration : Array String

/-- Match compiler-generated matchers to their containing declaration's phase. -/
def isMetaDecl (env : Environment) (name : Name) : Bool :=
  let parent :=
    if name.isStr && (name.getString!.startsWith "match_" || name.getString! == "_unsafe_rec" ||
        name.getString!.startsWith "_proof_") then
      let ancestor := name.getPrefix
      if (env.find? ancestor).isSome then ancestor else (privateToUserName name).getPrefix
    else name
  isMarkedMeta env parent || isDeclMeta env parent

/-- References from one module, preserving both visibility and execution phase. -/
def usesIn (env : Environment) (idx : ModuleIdx) (exp : Array (Name × Bool))
    (publicView : Bool) : Uses := Id.run do
  let exportedNames : Std.HashSet Name := exp.foldl (fun s (c, _) => s.insert c) {}
  let mut todo : Array (Name × Bool × Bool) :=
    if publicView then exp.map fun (c, body) =>
      let phase := isMetaDecl env c
      -- Public meta implementations are public dependencies even when the
      -- exported .olean contains only their signatures, not unfoldable bodies.
      (c, body || phase, phase)
    else env.header.moduleData[idx.toNat]!.constNames.map fun c => (c, true, isMetaDecl env c)
  -- A statement-only visit may later need upgrading to a body visit. The
  -- same auxiliary can also be needed in distinct execution phases.
  let mut seen : Std.HashMap (Name × Bool) Bool := {}
  let mut ordinary : Std.HashSet Name := {}
  let mut elaboration : Std.HashSet Name := {}
  while h : 0 < todo.size do
    let (c, body, phase) := todo.back
    todo := todo.pop
    if let some full := seen[(c, phase)]? then
      if full || !body then continue
    seen := seen.insert (c, phase) body
    let some ci := env.find? c | continue
    for u in usedBy ci body do
      let some j := env.getModuleIdxFor? u | continue
      if j != idx then
        let owner := env.header.moduleNames[j.toNat]!
        -- A meta declaration is already executable at elaboration time;
        -- referencing it requires an ordinary import. A regular definition
        -- referenced by meta code instead requires a meta import.
        if phase && !isMetaDecl env u then elaboration := elaboration.insert owner
        else ordinary := ordinary.insert owner
      else if body && (u.isInternal || !exportedNames.contains u) then
        todo := todo.push (u, true, phase)
  for use in getExtraModUses env idx do
    if (!publicView || use.isExported) && use.module != env.header.moduleNames[idx.toNat]! then
      if use.isMeta then elaboration := elaboration.insert use.module
      else ordinary := ordinary.insert use.module
  return { ordinary := ordinary.toArray.map toString |>.qsort (· < ·)
           elaboration := elaboration.toArray.map toString |>.qsort (· < ·) }

/-- Read both declaration views with one environment import. -/
unsafe def bothUsesOf (mods : Array Name) : IO (Array (Name × Uses × Uses)) := do
  let mut exported : Std.HashMap Name (Array (Name × Bool)) := {}
  for mod in mods do
    -- Names refer into these regions until the process exits.
    let (data, _region) ← readModuleData (← findOLean mod)
    exported := exported.insert mod <| data.constants.map fun ci =>
      (ci.name, (valueOf? ci).isSome && !ci.isTheorem)
  -- Load private data while retaining module-system phase semantics.
  -- importModules(level := .private) otherwise creates a legacy environment,
  -- where isDeclMeta deliberately treats EVERY declaration as meta.
  let imports := mods.map ({ module := · })
  let env ← withImporting do
    let (_, state) ← importModulesCore imports (globalLevel := .private) |>.run
    finalizeImport state imports {} (isModule := true) (level := .private)
      (leakEnv := true) (loadExts := false)
  -- This is a one-shot reader process. Keep regions alive through JSON output:
  -- Name.toString may return a borrowed component for a one-part module name.
  -- The OS reclaims the environment when the bounded process exits.
  let mut result := #[]
  for mod in mods do
    let some idx := env.getModuleIdx? mod | throw <| IO.userError s!"{mod} was not loaded"
    let exp := exported.getD mod #[]
    result := result.push (mod, usesIn env idx exp true, usesIn env idx exp false)
  return result

unsafe def usesOf (mods : Array Name) (publicView : Bool) (metaView : Bool := false) : IO (Array (Name × Array String)) := do
  return (← bothUsesOf mods).map fun (m, pub, priv) =>
    let view := if publicView then pub else priv
    (m, if metaView then view.elaboration else view.ordinary)

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  if args.head? == some "namespace_exports" then
    let mut out : Array (String × Json) := #[]
    for m in args.tail do
      let (data, _region) ← readModuleData (← findOLean m.toName)
      let mut namespaces : Array String := #[]
      for (name, entries) in data.entries do
        -- Lean.Namespace exports PersistentEnvExtension Name Name entries.
        -- Match its private extension name before interpreting the payload;
        -- the toolchain fingerprint versions this metadata representation.
        let key := name.toString
        if key.startsWith "_private.Lean.Namespace." && key.endsWith ".Lean.namespacesExt" then
          for entry in entries do
            let namespaceName : Name := unsafeCast entry
            namespaces := namespaces.push namespaceName.toString
      out := out.push (m, toJson namespaces)
    IO.println (Json.mkObj out.toList).compress
    return 0
  if args.head? == some "effects" then
    -- Read metadata without importing dependencies or running initializers.
    -- Runtime initializers are omitted from module .olean entries and live
    -- in .ir instead. A meta import executes them even when no declaration
    -- reference records the effect. Include macro-generated initializers too.
    let mut out : Array (String × Json) := #[]
    for m in args.tail do
      let path ← findOLean m.toName
      let (data, _region) ← readModuleData path
      let mut entries := data.entries
      if data.isModule then
        let parts ← readModuleDataParts #[path.withExtension "ir.sig", path.withExtension "ir"]
        for (part, _region) in parts do
          entries := entries ++ part.entries
      let effects := entries.filterMap fun (name, entries) =>
        if entries.isEmpty then none else some name.toString
      out := out.push (m, toJson effects)
    IO.println (Json.mkObj out.toList).compress
    return 0
  if args.head? == some "names" then
    let mut out : Array (String × Json) := #[]
    for m in args.tail do
      -- Not freed: the names' strings may point into the module's data
      -- until they are printed.
      let (data, _region) ← readModuleData (← findOLean m.toName)
      out := out.push (m, toJson (data.constNames.map toString))
    IO.println (Json.mkObj out.toList).compress
    return 0
  if args.head? == some "both" then
    let res ← bothUsesOf (args.tail.toArray.map String.toName)
    IO.println (Json.mkObj (res.toList.map fun (m, pub, priv) =>
      (m.toString, Json.mkObj [("public", toJson pub.ordinary), ("private", toJson priv.ordinary),
        ("meta_public", toJson pub.elaboration), ("meta_private", toJson priv.elaboration)]))).compress
    return 0
  let (publicView, metaView) ← match args.head? with
    | some "public" => pure (true, false)
    | some "private" => pure (false, false)
    | some "meta_public" => pure (true, true)
    | some "meta_private" => pure (false, true)
    | _ => throw <| IO.userError "usage: lean_module_uses.lean (public | private | meta_public | meta_private | both | names) MOD..."
  let res ← usesOf (args.tail.toArray.map String.toName) publicView metaView
  IO.println (Json.mkObj (res.toList.map fun (m, us) => (m.toString, toJson us))).compress
  return 0
