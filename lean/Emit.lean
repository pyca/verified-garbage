import VerifiedGarbage.TCB.Emit

/-!
# The emitter

Renders every artifact (those of each registration file under `VerifiedGarbage/Artifacts/`, and of each
generic file under `VerifiedGarbage/Generic/` for each variant under
`VerifiedGarbage/Variants/`, see `VerifiedGarbage/TCB/Emit.lean`) into Rust: each target's
functions into a crate of its own, `crates/verified-garbage-asm-<target>/src/` (DIR, by
default `../crates`, relative to `lean/`). Run it from `lean/` after
`lake build` (which checks every proof):

* `lake env lean --run Emit.lean [DIR]` writes the files (and deletes stale
  `.rs` files).
* `lake env lean --run Emit.lean --check [DIR]` writes nothing and fails if
  the files on disk differ from what would be generated; CI runs this.

It writes a program for each target directory that imports its
registration files (`.lake/emit/Driver<Target>.lean`, `VG.Emit.parts`) and
runs them at once, as processes with the same arguments, each auditing and
emitting the artifacts of its targets (`VG.Emit.run`'s `--part`); and then,
if they all pass, checks that no target is in two of them and writes or
checks the root module (`VG.Emit.finish`). (They are run by the
interpreter rather than as a `lean_exe` so that CI does not have to compile
Mathlib to native code.) Each program is a module, run with Lake's setup for it
(`lake setup-file`), so Lean reads only the `.olean`, `.olean.server` and IR of
what it imports, not their private data (`.olean.private`), which CI does not
restore: the audits read the audit records instead (`TCB/AuditRecords.lean`).
This file itself, which is not a module, loads only the trusted base and its private
data. The interpreter runs the trusted base, which
does the printing and checking, as the compiled code of the `NativeTCB`
libraries (`lakefile.toml`: one of what no target owns, and one per target),
which `lake build` builds, and so an order of magnitude faster.
-/

/-- A shared library of the trusted base, as the lakefile names it
(`libName`): `VerifiedGarbage_NativeTCB`, followed by the target's name for
a target's. -/
def sharedLib (name : String) : System.FilePath :=
  ".lake" / "build" / "lib" /
    if System.Platform.isWindows then s!"{name}.dll"
    else s!"lib{name}.{if System.Platform.isOSX then "dylib" else "so"}"

/-- The shared libraries of `NativeTCB` and of each target's
(`NativeTCB<Target>`, a target being a directory of `TCB/`), in the order the
driver loads them: what no target owns first, which the others link. -/
def nativeTCB : IO (List System.FilePath) := do
  let dirs ← ("VerifiedGarbage" / "TCB" : System.FilePath).readDir
  let mut targets := #[]
  for e in dirs do
    if ← e.path.isDir then targets := targets.push e.fileName
  return (sharedLib "VerifiedGarbage_NativeTCB") ::
    (targets.qsort (· < ·)).toList.map fun t => sharedLib s!"VerifiedGarbage_NativeTCB{t}"

/-- How many `.olean` files the driver may load: those of this project and
of its packages. -/
partial def oleanCount (dir : System.FilePath) : IO Nat := do
  if !(← dir.isDir) then return 0
  let mut n := 0
  for e in ← dir.readDir do
    if ← e.path.isDir then n := n + (← oleanCount e.path)
    else if e.path.extension == some "olean" then n := n + 1
  return n

/-- On Linux, a process may map at most `vm.max_map_count` regions of memory,
and the driver maps each module it imports. Past the limit, Lean fails with
`failed to read file '….olean'`, naming whichever module it was loading.
When the driver was not a module, and also mapped every private part, it
needed about six regions per `.olean` (80,144 for 13,700); require eight.
`none` if the limit is high enough, or not Linux. -/
def mapCountProblem : IO (Option String) := do
  let limitFile : System.FilePath := "/proc/sys/vm/max_map_count"
  unless System.Platform.isLinux && (← limitFile.pathExists) do return none
  let some limit := (← IO.FS.readFile limitFile).trimAscii.toString.toNat? | return none
  let mut oleans ← oleanCount (".lake" / "build" / "lib" / "lean")
  let packages : System.FilePath := ".lake" / "packages"
  if ← packages.isDir then
    for e in ← packages.readDir do
      oleans := oleans + (← oleanCount (e.path / ".lake" / "build" / "lib" / "lean"))
  let needed := 8 * oleans
  if limit ≥ needed then return none
  return some s!"vm.max_map_count is {limit}, and the driver may map about {needed} \
    regions of memory ({oleans} .olean files): raise it, e.g. \
    `sudo sysctl -w vm.max_map_count=262144` (see lean/README.md)"

/-- Writes Lake's setup for the module `file` (`lake setup-file`, which builds what it
imports) to `out`. -/
def setupFile (file out : System.FilePath) : IO UInt32 := do
  let r ← IO.Process.output { cmd := "lake", args := #["setup-file", file.toString] }
  unless r.exitCode == 0 do
    IO.eprint r.stderr
    return r.exitCode
  IO.FS.writeFile out r.stdout
  return 0

def main (args : List String) : IO UInt32 := do
  let libs ← nativeTCB
  for lib in libs do
    unless ← lib.pathExists do
      IO.eprintln s!"{lib} is missing: run `lake build` first"
      return 1
  if let some problem ← mapCountProblem then
    IO.eprintln problem
    return 1
  let some (check, none, _) := VG.Emit.parseArgs args
    | IO.eprintln VG.Emit.usage; return 2
  let parts ← match VG.Emit.parts (← VG.Emit.registrations)
      (← VG.Emit.genericGroups VG.Emit.genericDir) (← VG.Emit.grouped VG.Emit.variantDir) with
    | .ok parts => pure parts
    | .error e => do IO.eprintln e; return 1
  let emitDir : System.FilePath := ".lake" / "emit"
  IO.FS.createDirAll emitDir
  let lean ← IO.appPath
  -- Each part's driver, and Lake's setup for it (which also loads the trusted base's
  -- shared libraries), all at once.
  let setups ← parts.mapM fun (t, mods, gens, vars) => do
    let driver := emitDir / s!"Driver{t}.lean"
    let text := VG.Emit.driver mods gens vars
    -- Only if it changed, so that Lake does not take it for a new file.
    let old ← if ← driver.pathExists then some <$> IO.FS.readFile driver else pure none
    unless old == some text do IO.FS.writeFile driver text
    IO.asTask (setupFile driver (emitDir / s!"Driver{t}.json"))
  for task in setups do
    match task.get with
    | .ok 0 => pure ()
    | .ok code => return code
    | .error e => throw e
  -- Each part's driver, run at once.
  let mut children : Array (System.FilePath × IO.Process.Child {}) := #[]
  for (t, _) in parts do
    let driver := emitDir / s!"Driver{t}.lean"
    let targets := emitDir / s!"{t}.targets"
    if ← targets.pathExists then IO.FS.removeFile targets
    let partArgs := (if check then ["--check"] else []) ++ ["--part", targets.toString] ++
      (if check then args.drop 1 else args)
    children := children.push (targets, ← IO.Process.spawn
      { cmd := lean.toString,
        args := #["--setup", (emitDir / s!"Driver{t}.json").toString, "--run", driver.toString] ++
          partArgs.toArray })
  let mut code := 0
  for (_, child) in children do
    let c ← child.wait
    if code == 0 then code := c
  unless code == 0 do return code
  let targets ← children.toList.mapM fun (f, _) => do
    let lines := ((← IO.FS.readFile f).splitOn "\n").filter fun (l : String) => !l.isEmpty
    return lines.map fun (l : String) =>
      match l.splitOn "\t" with
      | [t, c] => (t, c)
      | _ => (l, "")
  VG.Emit.finish targets args
