import VerifiedGarbage.TCB.Emit

/-!
# The emitter

Renders every artifact (those of each registration file under `VerifiedGarbage/Artifacts/`,
see `VerifiedGarbage/TCB/Emit.lean`) into Rust: each target's
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
checks the root module (`VG.Emit.finish`). It prints when the setup
was written and when each part ended, from the start. (They are run by the
interpreter rather than as a `lean_exe` so that CI does not have to compile
Mathlib to native code.) Each program is a module, run with a setup file
(`lean --setup`, `setupJson`) that names, for every built module, its `.olean`,
`.olean.server` and IR, so Lean reads only those of what a program imports, not
their private data (`.olean.private`), which CI does not restore: the audits read
the audit records instead (`TCB/AuditRecords.lean`). The setup is written here,
from the files `lake build` left, not asked of Lake (`lake setup-file`, which
checks again, for each program, that everything it imports is built, as long as
the programs then run): so this reads the build as it is, and is run after
`lake build`, as CI runs it; nothing here checks that the build is current.
This file itself, which is not a module, loads only the trusted base and its private
data. The interpreter runs the trusted base, which
does the printing and checking, as the compiled code of the `NativeTCB`
libraries (`lakefile.toml`: one of what no target owns, and one per target),
which `lake build` builds, and so an order of magnitude faster.
-/

/-- A shared library of compiled modules, as the lakefile names it
(`libName`). -/
def sharedLib (name : String) : System.FilePath :=
  ".lake" / "build" / "lib" /
    if System.Platform.isWindows then s!"{name}.dll"
    else s!"lib{name}.{if System.Platform.isOSX then "dylib" else "so"}"

/-- The shared libraries of the modules the lakefile compiles
(`precompileModules`), in an order in which each comes after those whose code
it calls, the order a program loads them in: the audit records' module, the
trusted base's (`NativeTCB`, then each target's, `NativeTCB<Target>`, a target
being a directory of `TCB/`), and the others, the cleanups' after
`NativeCodeOnce`. -/
def nativeLibs : IO (List System.FilePath) := do
  let dirs ← ("VerifiedGarbage" / "TCB" : System.FilePath).readDir
  let mut targets := #[]
  for e in dirs do
    if ← e.path.isDir then targets := targets.push e.fileName
  return (["VerifiedGarbage_VerifiedGarbage_TCB_AuditRecords", "VerifiedGarbage_NativeTCB"] ++
    (targets.qsort (· < ·)).toList.map (s!"VerifiedGarbage_NativeTCB{·}") ++
    ["VerifiedGarbage_NativeSpec", "VerifiedGarbage_NativeTactics", "VerifiedGarbage_NativeHintSearch",
      "VerifiedGarbage_NativeForward", "VerifiedGarbage_NativeCodeOnce",
      "VerifiedGarbage_NativeScrubX86__64", "VerifiedGarbage_NativeScrubAArch64"]).map sharedLib

/-- The files of each built module under `dir`, the directory of the modules
`module.*` of a directory of built modules (one of `LEAN_PATH`: the project's,
or a dependency's; `module` is empty for the directory itself), after `acc`:
as a setup file names them (`importArts`), the module's name, then its
`.olean` and `.olean.server`, and its IR's signatures and its IR. Not its
`.olean.private`. A directory of modules has no `.` in its name, and every
file has one; `depth` bounds how deep the directories are followed. -/
def moduleFiles (dir : System.FilePath) (module : String) (acc : Array String) :
    (depth : Nat) → IO (Array String)
  | 0 => return acc
  | depth + 1 => do
    let mut acc := acc
    for e in ← dir.readDir do
      let n := e.fileName
      if n.contains '"' || n.contains '\\' then
        throw <| IO.userError s!"{e.path}: a name the setup file would have to escape"
      if !n.contains '.' then
        acc ← moduleFiles e.path (if module.isEmpty then n else module ++ "." ++ n) acc depth
      else if n.endsWith ".olean" then
        let m := (n.dropEnd ".olean".length).toString
        let base := (dir / m).toString
        acc := acc.push <| "\"" ++ (if module.isEmpty then m else module ++ "." ++ m) ++ "\":[[\"" ++
          base ++ ".olean\",\"" ++ base ++ ".olean.server\"],[\"" ++ base ++ ".ir.sig\",\"" ++ base ++
          ".ir\"]]"
    return acc

/-- The setup file of every program (`lean --setup`): a module, which may
import any built module of `LEAN_PATH` (as `lake env` sets it), by the files
`moduleFiles` names, and which loads the shared libraries `libs`. The paths
are written as they are: this and `moduleFiles` fail on one that a JSON
string would have to escape. -/
def setupJson (libs : List System.FilePath) : IO String := do
  let plain (p : System.FilePath) : IO String := do
    let p := (← IO.FS.realPath p).toString
    if p.contains '"' || p.contains '\\' then
      throw <| IO.userError s!"{p}: a path the setup file would have to escape"
    return p
  let roots := System.SearchPath.parse ((← IO.getEnv "LEAN_PATH").getD "")
  let mut files := #[]
  for root in roots do
    if ← root.isDir then files ← moduleFiles (← plain root) "" files 64
  let libs ← libs.mapM fun l => return "\"" ++ (← plain l) ++ "\""
  return "{\"name\":\"_unknown\",\"isModule\":true,\"importArts\":{" ++
    ",".intercalate files.toList ++ "},\"dynlibs\":[" ++ ",".intercalate libs ++
    "],\"plugins\":[],\"options\":{}}\n"

/-- Milliseconds as seconds, to a tenth: `12.3 s`. -/
def seconds (ms : Nat) : String :=
  s!"{ms / 1000}.{ms % 1000 / 100} s"

def main (args : List String) : IO UInt32 := do
  let start ← IO.monoMsNow
  let libs ← nativeLibs
  for lib in libs do
    unless ← lib.pathExists do
      IO.eprintln s!"{lib} is missing: run `lake build` first"
      return 1
  -- A compiled library this does not know would not be loaded, and its modules
  -- then run in the interpreter.
  for e in ← (".lake" / "build" / "lib" : System.FilePath).readDir do
    if e.fileName.startsWith "libVerifiedGarbage_Native" && e.path.extension == (sharedLib "x").extension &&
        !libs.contains e.path then
      IO.eprintln s!"{e.path} is not one of `nativeLibs` (Emit.lean): add it, after the libraries it needs"
      return 1
  let some (check, none, _) := VG.Emit.parseArgs args
    | IO.eprintln VG.Emit.usage; return 2
  let parts ← match VG.Emit.parts (← VG.Emit.registrations) with
    | .ok parts => pure parts
    | .error e => do IO.eprintln e; return 1
  let emitDir : System.FilePath := ".lake" / "emit"
  IO.FS.createDirAll emitDir
  let lean ← IO.appPath
  let setup := emitDir / "Setup.json"
  IO.FS.writeFile setup (← setupJson libs)
  let setUp := (← IO.monoMsNow) - start
  -- Each part's driver, and the arguments of its run.
  let jobs ← parts.mapM fun (t, mods) => do
    let driver := emitDir / s!"Driver{t}.lean"
    let targets := emitDir / s!"{t}.targets"
    IO.FS.writeFile driver (VG.Emit.driver mods)
    if ← targets.pathExists then IO.FS.removeFile targets
    let partArgs := (if check then ["--check"] else []) ++ ["--part", targets.toString] ++
      (if check then args.drop 1 else args)
    return (driver, targets, partArgs)
  -- Each part's driver on a task of its own, all at once: its exit code, and when it
  -- ended.
  let tasks ← jobs.mapM fun (driver, targets, partArgs) => do
    let task ← IO.asTask (prio := .dedicated) do
      let child ← IO.Process.spawn { cmd := lean.toString, args :=
        #["--setup", setup.toString, "--run", driver.toString] ++ partArgs.toArray }
      let code ← child.wait
      return (code, (← IO.monoMsNow) - start)
    return (driver, targets, task)
  let mut results := []
  for (driver, targets, task) in tasks do
    match task.get with
    | .ok r => results := (driver, targets, r) :: results
    | .error e => throw e
  -- When the setup was written and when each part's run ended, from the start: the run
  -- takes as long as the part that ends last.
  let mut code := 0
  IO.println s!"set up at {seconds setUp}"
  for (driver, _, c, ended) in results.reverse do
    IO.println s!"{driver.fileStem.getD ""}: ended at {seconds ended}"
    if code == 0 then code := c
  IO.println s!"all parts: {seconds ((← IO.monoMsNow) - start)}"
  unless code == 0 do return code
  let targets ← results.reverse.mapM fun (_, f, _) => do
    let lines := ((← IO.FS.readFile f).splitOn "\n").filter fun (l : String) => !l.isEmpty
    return lines.map fun (l : String) =>
      match l.splitOn "\t" with
      | [t, c] => (t, c)
      | _ => (l, "")
  VG.Emit.finish targets args
