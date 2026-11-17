import Lean

/-!
Checks that every module of the build can be imported together: that no two
declare the same name in a way Lean refuses ("environment already contains").

  lake env lean --run ../ci/lean_unique_decls.lean .lake/build/lib/lean

Run from `lean/` after a full build. Reads the `.olean` of every module under
the directory whose source file is still there, prints one line
`NAME MODULE MODULE` for each name that two of them declare and that
`importModules` would reject, and fails if there is one.

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

/-- The path of `f`'s module under `root`, without its extension: that of its
source file under `lean/`. -/
def stemOf (root f : System.FilePath) : String :=
  let rel := (f.toString.drop (root.toString.length + 1)).toString
  (rel.dropEnd ".olean".length).toString

unsafe def main (args : List String) : IO UInt32 := do
  let [dir] := args | throw <| .userError "usage: lean_unique_decls.lean DIR"
  let root : System.FilePath := dir
  let files ← root.walkDir
  let oleans := (files.filter (·.toString.endsWith ".olean")).qsort (·.toString < ·.toString)
  -- Only modules that still exist: a build restored from the cache keeps the
  -- outputs of modules deleted since, which a pull request's build does not
  -- prune (`lean_shards.py prune`).
  let oleans ← oleans.filterM fun f => (System.FilePath.mk (stemOf root f ++ ".lean")).pathExists
  let mut seen : Std.HashMap Name (ConstantInfo × Name) := {}
  let mut clashes := 0
  for f in oleans do
    let m := (stemOf root f).splitOn "/" |>.foldl Name.str .anonymous
    -- The regions stay mapped: the constants read from them are kept.
    let (md, _) ← readModuleData f
    for c in md.constants do
      match seen[c.name]? with
      | some (prev, pm) =>
        unless compatible prev c do
          IO.println s!"{c.name} {pm} {m}"
          clashes := clashes + 1
      | none => seen := seen.insert c.name (c, m)
  IO.eprintln s!"{oleans.size} modules, {clashes} declarations Lean would not import together"
  return if clashes == 0 then 0 else 1
