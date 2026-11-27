import Lean.Environment

/-!
Checks that every module of the build can be imported together: that no two
declare the same name in a way Lean refuses ("environment already contains").

  lean --run ../ci/lean_unique_decls.lean .lake/build/lib/lean

Run from `lean/` after a full build. Reads the `.olean` under the directory
of every module whose source file is under `lean/` (but `.lake/`), prints one
line `NAME MODULE MODULE` for each name that two of them declare and that
`importModules` would reject, and fails if there is one. It imports only
`Lean.Environment`, of Lean's own library, so it needs no `lake env`.

Lean accepts a name that two modules declare only as the same theorem, with
the same statement and universe parameters (`subsumesInfo` in
`Lean/Environment.lean`): that is how the equation lemmas each module
generates for itself (`f.eq_1`) are imported together. This check accepts
the same, and also two axioms with the same statement, where Lean also asks
that the statement be a proposition.

No module imports two modules that declare the same name differently, or it
would not build; but `lake check` and `lake comparator` (`lake help check`)
import every module they check together, and refuse the project at the
first. Make one of the two `private`, or give it a name of its own (a
target's definitions in a namespace that all targets share end in the
target's name: `openToResRISCV64`).
-/

open Lean

/-- Whether Lean imports `a` and `b`, of the same name, together. -/
def compatible (a b : ConstantInfo) : Bool :=
  a.type == b.type && a.levelParams == b.levelParams &&
    match a, b with
    | .thmInfo x, .thmInfo y => x.all == y.all
    | .thmInfo x, .axiomInfo y | .axiomInfo y, .thmInfo x => x.all == [y.name] && !y.isUnsafe
    | .axiomInfo x, .axiomInfo y => x.isUnsafe == y.isUnsafe
    | _, _ => false

/-- The module of the source file `src`, a path under `.` (`./A/B.lean`). -/
def moduleOf (src : System.FilePath) : Name :=
  ((src.withExtension "").components.filter (· != ".")).foldl Name.str .anonymous

/-- Each name that a module of `mods` declares in a way Lean does not import
with a module before it, with that module. A pure function, which the
interpreter runs several times faster than the same loop in `IO`. -/
def scan (mods : Array (Name × ModuleData)) : Array (Name × Name) := Id.run do
  let mut seen : Std.HashMap Name ConstantInfo := .emptyWithCapacity (1 <<< 20)
  let mut clashes := #[]
  for (m, md) in mods do
    for c in md.constants do
      match seen[c.name]? with
      | some prev => unless compatible prev c do clashes := clashes.push (c.name, m)
      | none => seen := seen.insert c.name c
  return clashes

/-- The first module of `mods` that declares each of `names`. -/
def firstModules (mods : Array (Name × ModuleData)) (names : Array Name) : Std.HashMap Name Name :=
  Id.run do
    let wanted := Std.HashSet.ofArray names
    let mut first := {}
    for (m, md) in mods do
      for n in md.constNames do
        if wanted.contains n && !first.contains n then first := first.insert n m
    return first

/-- The number of threads that read the `.olean`s. -/
def readers : Nat := 4

unsafe def main (args : List String) : IO UInt32 := do
  let [dir] := args | throw <| .userError "usage: lean_unique_decls.lean DIR"
  let root : System.FilePath := dir
  -- The modules from their source files, not from the build directory, which
  -- holds a dozen other files for each module, and, restored from the cache,
  -- the outputs of modules deleted since, which a pull request's build does
  -- not prune (`lean_shards.py prune`).
  let files ← System.FilePath.walkDir "."
    (enter := fun p => pure !((p.fileName.getD "").startsWith "."))
  let srcs := (files.filter (·.extension == some "lean")).qsort (·.toString < ·.toString)
  let mods ← srcs.filterMapM fun s => do
    let m := moduleOf s
    let olean := (m.components.foldl (fun p c => p / c.toString) root).withExtension "olean"
    return if ← olean.pathExists then some (m, olean) else none
  -- Read on a few threads, each a slice of the modules, kept in their order.
  -- The regions stay mapped: the constants read from them are kept.
  let size := (mods.size + readers - 1) / readers
  let tasks ← (List.range readers).mapM fun i => IO.asTask (prio := .dedicated) do
    mods[i * size:(i + 1) * size].toArray.mapM fun (m, f) => return (m, (← readModuleData f).1)
  let mut read := #[]
  for t in tasks do
    read := read ++ (← IO.ofExcept t.get)
  let clashes := scan read
  let firsts := firstModules read (clashes.map (·.1))
  for (n, m) in clashes do
    IO.println s!"{n} {firsts.getD n .anonymous} {m}"
  IO.eprintln s!"{mods.size} modules, {clashes.size} declarations Lean would not import together"
  return if clashes.isEmpty then 0 else 1
