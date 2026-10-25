import Lean

/-!
For `lean_split_advice.py`: what each given module's declarations need, one
declaration at a time.

  lake env lean --run ../ci/lean_decl_deps.lean MOD...

Prints one JSON object: `modules`, a table of module names, and for each
given module:

* `decls`: each declaration it exports, with the modules (indices into
  `modules`) owning the constants it uses outside the module, through the
  module's own declarations it uses (auxiliary declarations and proofs
  included): what a module holding that declaration alone would import;
  and the module's other exported declarations it uses so (`with`), which
  would have to move with it;
* `uses`: for each module of the project it uses, the declarations of that
  module its declarations use directly;
* `size`: how many constants it declares.

The modules are loaded together, as `lean_module_uses.lean` does, with their
private data and without running initializers.
-/

open Lean

def valueOf? : ConstantInfo → Option Expr
  | .defnInfo v => some v.value
  | .thmInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

def usedBy (ci : ConstantInfo) : Array Name :=
  ci.type.getUsedConstants ++ ((valueOf? ci).map (·.getUsedConstants)).getD #[]

def sortDedup (xs : Array Nat) : Array Nat := Id.run do
  let xs := xs.qsort (· < ·)
  let mut out := #[]
  for x in xs do
    if out.back? != some x then out := out.push x
  return out

structure Out where
  names : Std.HashMap Name Nat := {}
  table : Array Name := #[]

def Out.intern (o : Out) (m : Name) : Out × Nat :=
  match o.names[m]? with
  | some i => (o, i)
  | none => ({ names := o.names.insert m o.table.size, table := o.table.push m }, o.table.size)

/-- The external owners of each of `mod`'s constants, through its own. -/
def externalOwners (env : Environment) (idx : ModuleIdx) (consts : Array Name)
    (exported : Std.HashMap Name Nat) :
    Std.HashMap Name (Array Nat × Array Nat) := Id.run do
  let mut memo : Std.HashMap Name (Array Nat × Array Nat) := {}
  let mut active : Std.HashSet Name := {}
  for root in consts do
    if memo.contains root then continue
    -- Iterative post-order: a cycle (mutual declarations) sees the partial
    -- result of the declaration it closes on.
    let mut stack : Array (Name × Bool) := #[(root, false)]
    while h : 0 < stack.size do
      let (c, ready) := stack.back
      stack := stack.pop
      if memo.contains c then continue
      let some ci := env.find? c | memo := memo.insert c (#[], #[]); continue
      let used := usedBy ci
      if ready then
        let mut owners : Array Nat := #[]
        let mut within : Array Nat := #[]
        for u in used do
          match env.getModuleIdxFor? u with
          | some j =>
            if j != idx then owners := owners.push j.toNat
            else if u != c then
              let (o, w) := memo.getD u (#[], #[])
              owners := owners ++ o
              within := within ++ w
              if let some k := exported[u]? then within := within.push k
          | none => pure ()
        memo := memo.insert c (sortDedup owners, sortDedup within)
        active := active.erase c
      else
        active := active.insert c
        stack := stack.push (c, true)
        for u in used do
          if env.getModuleIdxFor? u == some idx && !memo.contains u && !active.contains u then
            stack := stack.push (u, false)
  return memo

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let mods := args.toArray.map String.toName
  let mut exported : Std.HashMap Name (Array Name) := {}
  for mod in mods do
    let (data, _region) ← readModuleData (← findOLean mod)
    exported := exported.insert mod data.constNames
  let imports := mods.map ({ module := · })
  let env ← withImporting do
    let (_, state) ← importModulesCore imports (globalLevel := .private) |>.run
    finalizeImport state imports {} (isModule := true) (level := .private)
      (leakEnv := true) (loadExts := false)
  let mut out : Out := {}
  let mut rows : Array (String × Json) := #[]
  for mod in mods do
    let some idx := env.getModuleIdx? mod | throw <| IO.userError s!"{mod} was not loaded"
    let consts := env.header.moduleData[idx.toNat]!.constNames
    let exp := exported.getD mod #[]
    let position : Std.HashMap Name Nat := exp.foldl (init := {}) fun m c => m.insert c m.size
    let memo := externalOwners env idx consts position
    let mut decls : Array (String × Json) := #[]
    for c in exp do
      let mut ids := #[]
      let (owners, within) := memo.getD c (#[], #[])
      for j in owners do
        let (o, i) := out.intern env.header.moduleNames[j]!
        out := o
        ids := ids.push i
      decls := decls.push (c.toString, Json.mkObj [("owners", toJson ids),
        ("with", toJson (within.filterMap fun k => if exp[k]! == c then none else some exp[k]!.toString))])
    let mut uses : Std.HashMap Name (Std.HashSet Name) := {}
    for c in consts do
      let some ci := env.find? c | continue
      for u in usedBy ci do
        let some j := env.getModuleIdxFor? u | continue
        let owner := env.header.moduleNames[j.toNat]!
        if j != idx && owner.getRoot == `VerifiedGarbage then
          uses := uses.insert owner ((uses.getD owner {}).insert u)
    let usesJson := uses.toList.map fun (m, cs) =>
      (m.toString, toJson ((cs.toArray.map toString).qsort (· < ·)))
    rows := rows.push (mod.toString, Json.mkObj [("decls", Json.mkObj decls.toList),
      ("uses", Json.mkObj usesJson), ("size", toJson consts.size)])
  IO.println (Json.mkObj [("modules", toJson (out.table.map toString)),
    ("results", Json.mkObj rows.toList)]).compress
  return 0
