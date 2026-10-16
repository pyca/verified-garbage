import VerifiedGarbage.TCB.Emit

/-!
# The emitter

Renders every artifact (those of `VerifiedGarbage/Artifacts.lean`, of
each registration file under `VerifiedGarbage/Artifacts/`, and of each
generic file under `VerifiedGarbage/Generic/` for each variant under
`VerifiedGarbage/Variants/`, see `VerifiedGarbage/TCB/Emit.lean`) into Rust, under `src/asm/` of the crate
(by default `../src/asm`, relative to `lean/`). Run it from `lean/` after
`lake build` (which checks every proof):

* `lake env lean --run Emit.lean [DIR]` writes the files (and deletes stale
  `.rs` files).
* `lake env lean --run Emit.lean --check [DIR]` writes nothing and fails if
  the files on disk differ from what would be generated; CI runs this.

It writes a program that imports every registration file and runs it with
the same arguments, as two programs with the same imports and list of
artifacts (`VG.Emit.Part`): `.lake/emit/Audit.lean`, which elaborates only
the audits, and `.lake/emit/Run.lean`, which runs only the emitter. With
`--check`, which writes nothing, they run at once, as two processes, and it
fails if either does; otherwise the audits run first, and the emitter only if
they pass, so that it never writes files from artifacts that fail them. (It
is run by the interpreter rather than as a `lean_exe` so that CI does not
have to compile Mathlib to native code.) The interpreter runs the trusted base, which
does the printing and checking, as the compiled code of the `NativeTCB`
library (`lakefile.toml`), which `lake build` builds, and so an order of
magnitude faster.
-/

/-- The shared library of `NativeTCB`, as Lake names it. -/
def nativeTCB : System.FilePath :=
  ".lake" / "build" / "lib" /
    if System.Platform.isWindows then "VerifiedGarbage_NativeTCB.dll"
    else s!"libVerifiedGarbage_NativeTCB.{if System.Platform.isOSX then "dylib" else "so"}"

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
and the driver maps each module it imports, with its `.olean.server` and
`.olean.private` parts, since it is not a module and sees every module's
private part. Past the limit, Lean fails with `failed to read file
'….olean.private'`, naming whichever module it was loading. The driver
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

def main (args : List String) : IO UInt32 := do
  unless ← nativeTCB.pathExists do
    IO.eprintln s!"{nativeTCB} is missing: run `lake build` first"
    return 1
  if let some problem ← mapCountProblem then
    IO.eprintln problem
    return 1
  let regs ← VG.Emit.registrations
  let gens ← VG.Emit.genericGroups VG.Emit.genericDir
  let vars ← VG.Emit.grouped VG.Emit.variantDir
  let audit : System.FilePath := ".lake" / "emit" / "Audit.lean"
  let run : System.FilePath := ".lake" / "emit" / "Run.lean"
  IO.FS.createDirAll ".lake/emit"
  IO.FS.writeFile audit (VG.Emit.driver regs gens vars .audit)
  IO.FS.writeFile run (VG.Emit.driver regs gens vars .run)
  let lean := (← IO.appPath).toString
  let spawn (cmdArgs : Array String) : IO (IO.Process.Child {}) :=
    IO.Process.spawn { cmd := lean, args := #[s!"--load-dynlib={nativeTCB}"] ++ cmdArgs }
  let auditArgs := #[audit.toString]
  let runArgs := #["--run", run.toString] ++ args.toArray
  if args.head? == some "--check" then
    let auditing ← spawn auditArgs
    let running ← spawn runArgs
    let a ← auditing.wait
    let r ← running.wait
    return if a != 0 then a else r
  let a ← (← spawn auditArgs).wait
  if a != 0 then return a
  (← spawn runArgs).wait
