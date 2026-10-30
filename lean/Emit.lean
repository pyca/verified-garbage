import VerifiedGarbage.TCB.Emit

/-!
# The emitter

Renders every artifact (those of each registration file under
`VerifiedGarbage/Artifacts/`, and of each generic file under
`VerifiedGarbage/Generic/` for each variant under `VerifiedGarbage/Variants/`,
see `VerifiedGarbage/TCB/Emit.lean`) into Rust, under `src/asm/` of the crate
(by default `../src/asm`, relative to `lean/`). Run it from `lean/` after
`lake build` (which checks every proof):

* `lake env lean --run Emit.lean [DIR]` writes the files (and deletes stale
  `.rs` files).
* `lake env lean --run Emit.lean --check [DIR]` writes nothing and fails if
  the files on disk differ from what would be generated; CI runs this.

For each target directory (`VG.Emit.parts`) it writes the files of
`VG.Emit.prepare` (see "Drivers as modules" in `TCB/Emit.lean`): a module
that defines the target's artifacts, an audit of them, which `lake build`
builds (the library `VGEmit`, `lakefile.toml`), and a program that emits
them if the audit is of exactly what the program imported (and otherwise
exits with `VG.Emit.staleCode`). It builds the audits of the targets whose
files it changed, or that were never built, with `lake build`. Then it runs
the programs at once, as processes with the same arguments, each emitting
the artifacts of its targets (`VG.Emit.run`'s `--part`); builds the audits
of those whose program found its audit stale, which either audits what is
there now or fails, and runs those again; and then, if they all pass, checks
that no target is in two of them and writes or checks the root module
(`VG.Emit.finish`). (They are run
by the interpreter rather than as a `lean_exe` so that CI does not have to
compile Mathlib to native code.) The interpreter runs the trusted base, which
does the printing and checking, as the compiled code of the `NativeTCB`
libraries (`lakefile.toml`: one of what no target owns, and one per target),
which `lake build` builds, and so an order of magnitude faster.

* `lake env lean --run Emit.lean --prepare` only writes those files: CI runs
  it before `lake build`, so that the build audits every target.
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

/-- On Linux, a process may map at most `vm.max_map_count` regions of memory,
and Lean maps each module it imports with its parts (`.olean.server`,
`.olean.private`, `.ir`): an audit, which is not a module, maps those of
everything it imports, and the programs, which are modules, fewer. Past the
limit, Lean fails with `failed to read file '….olean.private'`, naming
whichever module it was loading. Measured on X86-64, the largest target
(at 27,959 `.olean` files in the build): the audit maps about 54,000
regions and the program about 46,600, under the 65,530 of many
distributions' default. Rather than refuse to start below a guess, this
names the fix after a failure: a hint if the limit is under 262,144 (what
CI sets), `none` otherwise or off Linux. -/
def mapCountHint : IO (Option String) := do
  let limitFile : System.FilePath := "/proc/sys/vm/max_map_count"
  unless System.Platform.isLinux && (← limitFile.pathExists) do return none
  let some limit := (← IO.FS.readFile limitFile).trimAscii.toString.toNat? | return none
  if limit ≥ 262144 then return none
  return some s!"if Lean failed above with `failed to read file '….olean.private'`, \
    vm.max_map_count ({limit}) is too low for it: raise it, e.g. \
    `sudo sysctl -w vm.max_map_count=262144` (see lean/README.md)"

/-- Prints `mapCountHint`, if any, after a failure. -/
def hintMapCount : IO Unit := do
  if let some h ← mapCountHint then IO.eprintln h

/-- The `.olean` of the module `mod` of `VGEmit`, relative to `lean/`. -/
def oleanOf (mod : String) : System.FilePath :=
  (mod.splitOn ".").foldl (· / ·) (".lake" / "build" / "lib" / "lean" : System.FilePath)
    |>.addExtension "olean"

/-- The file a part's program writes its targets to (`VG.Emit.run`'s `--part`). -/
def targetsOf (t : String) : System.FilePath := ".lake" / "emit" / s!"{t}.targets"

/-- Builds the audits of the target directories `ts`, if any (`lake build`,
reporting warnings and errors); whether they built. -/
def buildAudits (ts : Array String) : IO Bool := do
  if ts.isEmpty then return true
  let mods := ts.map VG.Emit.auditModule
  IO.println s!"building {", ".intercalate mods.toList}"
  let child ← IO.Process.spawn { cmd := "lake", args := #["build", "--log-level=warning"] ++ mods }
  return (← child.wait) == 0

/-- Runs the programs of the target directories `ts` at once, with the
shared libraries `libs` and each one's arguments; each one's exit code. -/
def runAll (libs : List System.FilePath) (partArgs : String → Array String)
    (ts : Array String) : IO (Array (String × UInt32)) := do
  let lean ← IO.appPath
  let mut children : Array (String × IO.Process.Child {}) := #[]
  for t in ts do
    if ← (targetsOf t).pathExists then IO.FS.removeFile (targetsOf t)
    children := children.push (t, ← IO.Process.spawn
      { cmd := lean.toString,
        args := (libs.map fun l => s!"--load-dynlib={l}").toArray ++
          #["--run", (VG.Emit.runnerPath t).toString] ++ partArgs t })
  children.mapM fun (t, child) => return (t, ← child.wait)

def main (args : List String) : IO UInt32 := do
  let parts ← match VG.Emit.parts (← VG.Emit.registrations)
      (← VG.Emit.genericGroups VG.Emit.genericDir) (← VG.Emit.grouped VG.Emit.variantDir) with
    | .ok parts => pure parts
    | .error e => do IO.eprintln e; return 1
  if args == ["--prepare"] then
    discard <| VG.Emit.prepare parts
    return 0
  let libs ← nativeTCB
  for lib in libs do
    unless ← lib.pathExists do
      IO.eprintln s!"{lib} is missing: run `lake build` first"
      return 1
  let some (check, none, _) := VG.Emit.parseArgs args
    | IO.eprintln VG.Emit.usage; return 2
  let changed ← VG.Emit.prepare parts
  -- The audits of the targets whose files changed, or never built: the
  -- `lake build` before this audited the others' module drivers as they are.
  let mut stale := #[]
  for (t, _) in parts do
    if changed.contains t || !(← (oleanOf (VG.Emit.auditModule t)).pathExists) then
      stale := stale.push t
  unless ← buildAudits stale do hintMapCount; return 1
  let partArgs (t : String) : Array String :=
    ((if check then ["--check"] else []) ++ ["--part", (targetsOf t).toString] ++
      (if check then args.drop 1 else args)).toArray
  let ts := parts.map (·.1)
  let mut codes ← runAll libs partArgs ts.toArray
  -- A program whose audit is not of what it imported emits nothing: build
  -- those audits, which either audit what is there now or fail, and run
  -- those programs again.
  let staleNow := codes.filterMap fun (t, c) => if c == VG.Emit.staleCode then some t else none
  unless staleNow.isEmpty do
    unless ← buildAudits staleNow do hintMapCount; return 1
    let again ← runAll libs partArgs staleNow
    codes := codes.map fun (t, c) => (t, ((again.find? (·.1 == t)).map (·.2)).getD c)
  if let some (_, c) := codes.find? (·.2 != 0) then
    hintMapCount
    return c
  let targets ← ts.mapM fun t => do
    let f := targetsOf t
    let lines := ((← IO.FS.readFile f).splitOn "\n").filter fun (l : String) => !l.isEmpty
    return lines.map fun (l : String) =>
      match l.splitOn "\t" with
      | [t, c] => (t, c)
      | _ => (l, "")
  VG.Emit.finish targets args
