import VerifiedGarbage.TCB.Emit

/-!
# The emitter, for one algorithm on one target

For iterating on one algorithm: builds only the registration files named on
the command line (and what they import), and emits only their files, rather
than building every module of the library as `Emit.lean` needs. Run it from
`lean/`:

* `lake env lean --run EmitOne.lean Rc2.AArch64 [More.Target …]` builds
  `VerifiedGarbage/Artifacts/Rc2/AArch64.lean`, and writes its files under
  `../crates` (its target's crate's `src/`).
* `lake env lean --run EmitOne.lean --check Rc2.AArch64 …` writes nothing and
  fails if those files on disk differ from what would be generated.

It runs the same trusted printer (`VG.Emit.run`) and the same audits
(`#assert_standard_axioms`, `#assert_no_compiler_overrides`,
`#assert_spec_origin`) as `Emit.lean`. First, on the fast path, on these
artifacts only, into `.lake/emit/one`; then it copies (or compares) each file
it generated but the crate's root `lib.rs` and `mod.rs` files, and each
module's assembly file (`assembly/<module>.s`). Each table of constants has a
file of its own (`consts/<name>.rs` of the crate, which depends only on the
table), so it writes those of its artifacts' tables and leaves the others. So
does each internal function (`internal/<name>.rs`, `VG.Rust.Internal`), but
the module whose file declares it (`VG.Rust.internalOwner`), which the files
calling it name, depends on every module of the target and every module
calling it, which the registration files alone do not show (`ownershipProblems`).

The fast path is only taken when what it would write is what `Emit.lean`
writes, taking the files on disk for what `Emit.lean` wrote for the other
registration files: when the registration files emit alone, every file they
generate exists already (a new module also changes `lib.rs`), has no functions
they do not generate (another registration file emits into it), and declares
the internal functions the same file on disk declares, each declared by that
file alone. Otherwise, before writing or comparing anything, it says why and
runs every registration file of each target directory given, as `Emit.lean`
runs them (`VG.Emit.run`'s `--part`), on the crates themselves: it writes (or
checks) all of those targets' crates, as `Emit.lean` does, which is slower but
exact. It is a convenience while iterating, not a replacement: `Emit.lean
--check`, which CI runs, checks every artifact and every file.
-/

open System

def usage : String := "usage: lake env lean --run EmitOne.lean [--check] <Alg>.<Target> …"

/-- The lines of a generated file that are not indented: its items, but not
those inside them (a dispatcher's `select`, `first` and `CHOSEN`,
`VG.Rust.dispatcher`). -/
def topLines (text : String) : List String :=
  (text.splitOn "\n").filter fun l => !l.startsWith " "

/-- The names of the functions a generated file defines: each line declaring
`extern "<abi>" fn <name>(`, whatever its ABI (`"C"`, `"sysv64"`, …), each
dispatcher, `pub unsafe fn <name>(` (`VG.Rust.dispatcher`), and each other
name of one of them, `pub use self::<f> as <name>;` (`VG.Rust.alias`), or
`pub use crate::<module>::<f> as <name>;` (`VG.Rust.soleDispatcher`), each
not indented (`topLines`). -/
def fnNames (text : String) : List String :=
  (topLines text).filterMap fun line =>
    match line.splitOn "extern \"" with
    | [_, rest] =>
      match rest.splitOn "\" fn " with
      | [_, decl] => some ((decl.splitOn "(").headD "")
      | _ => none
    | _ =>
      if line.startsWith "pub unsafe fn vg_" then
        some ((((line.drop "pub unsafe fn ".length).toString).splitOn "(").headD "")
      else if line.startsWith "pub use self::vg_" || line.startsWith "pub use crate::" then
        match line.splitOn " as " with
        | [_, name] => some ((name.splitOn ";").headD "")
        | _ => none
      else none

/-- Whether a file declares functions, or other names of them, that `fnNames`
does not read: then it cannot tell which functions other registration files
emit into the file, and must not overwrite it. -/
def unreadFns (text : String) : Bool :=
  (fnNames text).length != ((topLines text).filter fun l =>
    l.contains "fn vg_" || l.contains "use self::vg_" || l.contains "pub use crate::").length

/-- The internal functions a generated file declares the modules of
(`VG.Rust.internalDecls`): each `<name>` of a line `#[path = "internal/<name>.rs"]`,
not indented (`topLines`). -/
def internalDecls (text : String) : List String :=
  (topLines text).filterMap fun line =>
    match line.splitOn "#[path = \"internal/" with
    | [_, rest] => match rest.splitOn ".rs\"]" with
      | [name, _] => some name
      | _ => none
    | _ => none

/-- The module of each file of `<crate>/src/` under `root` that is a module's
file (`<module>.rs`, not `lib.rs`), with its text, of each crate `crates`. -/
def moduleFiles (root : FilePath) (crates : List String) :
    IO (List (String × String × String)) := do
  let mut out := []
  for crate in crates do
    let dir := root / crate / "src"
    unless ← dir.isDir do continue
    for e in ← dir.readDir do
      let some m := e.fileName.dropSuffix? ".rs" | continue
      if m.toString == "lib" || (← e.path.isDir) then continue
      out := (crate, m.toString, ← IO.FS.readFile e.path) :: out
  return out

/-- Which module's file declares each internal function (`VG.Rust.Internal.owner`)
depends on every module of the target, and on every module calling it
(`VG.Rust.internalOwner`), so on registration files this run does not load: an
`aes_gcm` registration alone declares in `gcm.rs` the internal functions of
`aes.rs`, which `Emit.lean` declares there. The problems that would make what
this run writes differ from what `Emit.lean` writes, taking the crates `dest`
on disk for what `Emit.lean` wrote for the other registration files: an
internal function that a file of this run declares and that a different file
on disk declares, or that no file on disk declares (a new one), and an
internal function that a file on disk declares and that the same file of this
run does not (another registration file calls it). -/
def ownershipProblems (out dest : FilePath) : IO (List String) := do
  let crates := (← out.readDir).toList.map (·.fileName)
  let generated ← moduleFiles out crates
  let current ← moduleFiles dest crates
  let owners := current.flatMap fun (c, m, text) => (internalDecls text).map fun n => ((c, n), m)
  let mut problems := []
  for (crate, m, text) in generated do
    let file := dest / crate / "src" / s!"{m}.rs"
    let decls := internalDecls text
    -- Each internal function `file` would declare that it is not the one file
    -- on disk to declare, with the other modules whose files on disk declare
    -- it (none for a new one).
    let elsewhere := decls.filterMap fun n =>
      let os := (owners.filter fun (k, _) => k == (crate, n)).map (·.2)
      if os == [m] then none else some (n, os.filter (· != m))
    let new := (elsewhere.filter (·.2.isEmpty)).map (·.1)
    unless new.isEmpty do
      problems := s!"{file} would declare the internal functions {new}, which no file \
        declares as internal functions (new ones, or artifacts of registration files not \
        given)" :: problems
    for o in VG.Rust.dedup ((elsewhere.flatMap (·.2)).mergeSort (· ≤ ·)) do
      let ns := (elsewhere.filter (·.2.contains o)).map (·.1)
      problems := s!"{file} would declare the internal functions {ns}, which {o}.rs \
        declares (Emit.lean chooses the module that declares each from every registration \
        file of the target)" :: problems
    if let some (_, _, now) := current.find? fun (c, m', _) => c == crate && m' == m then
      let others := (internalDecls now).filter (!decls.contains ·)
      unless others.isEmpty do
        problems := s!"{file} also declares the internal functions {others}, which other \
          registration files call" :: problems
  return problems.reverse

/-- Lake's log `log` without its `info:` and `trace:` entries (each a line
that starts with its level, and the lines after it that start with none)
and the modules it replayed (`ℹ`), which `lake setup-file` reports when it
fails to build a module, whatever `--log-level`: the profile each module
records, and the command. -/
def withoutInfo (log : String) : String := Id.run do
  let levels := ["info:", "trace:", "warning:", "error:"]
  let mut keep := true
  let mut out := #[]
  for line in log.splitOn "\n" do
    if let some l := levels.find? (fun (l : String) => line.startsWith l) then
      keep := l != "info:" && l != "trace:"
    -- Lake's own lines: a module it replayed, or built, and the summary of a
    -- failure. Any other line belongs to the entry before it.
    else if line.startsWith "ℹ" then keep := false
    else if ["✖", "⚠", "✔", "Some ", "- ", "Failed "].any (fun (p : String) => line.startsWith p) then
      keep := true
    if keep then out := out.push line
  return "\n".intercalate out.toList

/-- Runs a process, inheriting its output; its exit code. -/
def runProc (cmd : String) (args : Array String) : IO UInt32 := do
  let child ← IO.Process.spawn { cmd, args }
  child.wait

/-- Builds what the driver `driver` (`VG.Emit.driver`) imports, with Lake's
setup for it in `setup` (`Emit.lean`'s `main` says why): the registration
files, what they import, and the trusted base's shared libraries, which it
loads (what no target owns, and their targets'). On a failure, it reports the
warnings and errors, not the profile every module records (`lakefile.toml`),
and gives Lake's exit code. -/
def setUp (driver setup : FilePath) (mods : List String) : IO (Option UInt32) := do
  IO.FS.writeFile driver (VG.Emit.driver mods)
  let r ← IO.Process.output { cmd := "lake", args := #["setup-file", driver.toString] }
  unless r.exitCode == 0 do
    IO.eprint (withoutInfo r.stderr)
    return some r.exitCode
  IO.FS.writeFile setup r.stdout
  return none

/-- The files of the fast path, generated in `out` from the registration
files given alone, to write or compare under `dest`: each but the crates'
`lib.rs` and `mod.rs`, with its module's assembly file; or why they may differ
from what `Emit.lean` writes. -/
def fastPlan (out dest : FilePath) : IO (Except (List String) (List (FilePath × String))) := do
  let mut problems ← ownershipProblems out dest
  let mut pairs := #[]
  for path in ← out.walkDir do
    unless path.extension == some "rs" && path.fileName != some "mod.rs" &&
        path.fileName != some "lib.rs" do continue
    let rel := (path.toString.dropPrefix (out.toString ++ "/")).toString
    let target := dest / rel
    let text ← IO.FS.readFile path
    unless ← target.pathExists do
      problems := problems ++ [s!"{target} does not exist yet (a new module also changes lib.rs)"]
      continue
    let current ← IO.FS.readFile target
    if unreadFns current || unreadFns text then
      problems := problems ++ [s!"{target}: cannot read the names of its functions"]
      continue
    let others := (fnNames current).filter (!(fnNames text).contains ·)
    unless others.isEmpty do
      problems := problems ++ [s!"{target} also has {others}, from other registration files"]
      continue
    -- The file, and its module's assembly file (`Rust.assemblyFile`), which has the
    -- same functions: `assembly/<module>.s`, or `assembly/internal/<name>.s` of an
    -- internal function's, `internal/<name>.rs`.
    pairs := pairs.push (target, text)
    if let [crate, m] := rel.splitOn "/src/" then
      if m.endsWith ".rs" && (!m.contains '/' || m.startsWith "internal/") then
        let l := s!"{crate}/{VG.Rust.assemblyFile (m.dropEnd 3).toString}"
        pairs := pairs.push (dest / l, ← IO.FS.readFile (out / l))
  return if problems.isEmpty then .ok pairs.toList else .error problems

/-- Writes (or, if `check`, compares) the files `pairs`; whether all were up
to date or written. -/
def apply (check : Bool) (pairs : List (FilePath × String)) : IO Bool := do
  let mut ok := true
  for (tgt, text) in pairs do
    let current ← if ← tgt.pathExists then IO.FS.readFile tgt else pure ""
    if current == text then continue
    if check then
      IO.eprintln s!"{tgt} is out of date"
      ok := false
    else
      IO.FS.writeFile tgt text
      IO.println s!"wrote {tgt}"
  return ok

def main (args : List String) : IO UInt32 := do
  let (check, names) := match args with
    | "--check" :: rest => (true, rest)
    | rest => (false, rest)
  if names.isEmpty || names.any (·.startsWith "-") then
    IO.eprintln usage
    return 2
  -- An x86-64 dispatcher may call `vg_mcdt_enter` (`Rust.checkMcdt`), so the
  -- registration that has it comes with every x86-64 one; its files are
  -- compared as the others are.
  let names := if names.any (·.endsWith ".X86_64") && !names.contains "Mcdt.X86_64" then
    names ++ ["Mcdt.X86_64"] else names
  let all ← VG.Emit.registrations
  let regs := all.filter fun m => names.any fun n => m == s!"VerifiedGarbage.Artifacts.{n}"
  for n in names do
    unless regs.contains s!"VerifiedGarbage.Artifacts.{n}" do
      IO.eprintln s!"{n}: no registration file VerifiedGarbage/Artifacts/{n.replace "." "/"}.lean"
      return 2
  let emit : FilePath := ".lake" / "emit"
  let out := emit / "one"
  let dest : FilePath := ".." / "crates"
  IO.FS.createDirAll emit
  if ← out.pathExists then IO.FS.removeDirAll out
  -- The fast path: the registration files given, alone, into `out`.
  let driver := emit / "One.lean"
  let setup := emit / "One.json"
  if let some code ← setUp driver setup regs then return code
  let lean := (← IO.appPath).toString
  let r ← IO.Process.output
    { cmd := lean, args := #["--setup", setup.toString, "--run", driver.toString, out.toString] }
  let plan ← if r.exitCode == 0 then fastPlan out dest else
    pure (.error [s!"the registration files given do not emit alone: \
      {((r.stderr.trimAscii.toString.splitOn "\n").getLastD "").trimAscii}"])
  match plan with
  | .ok pairs =>
    -- The audits' reports, without the files the run wrote into `out`.
    for l in r.stdout.splitOn "\n" do
      unless l.isEmpty || l.startsWith "wrote " do IO.println l
    return if ← apply check pairs then 0 else 1
  | .error problems =>
  -- Otherwise every registration file of each target directory given, as
  -- `Emit.lean` runs them (`VG.Emit.parts`, `VG.Emit.run`'s `--part`), into
  -- `dest`: what it writes or compares is what `Emit.lean` does for those
  -- targets' crates.
  for p in problems do IO.println s!"EmitOne: {p}"
  let dirs := VG.Rust.dedup (regs.filterMap VG.Emit.targetDirOf)
  for t in dirs do
    let mods := all.filter (VG.Emit.targetDirOf · == some t)
    IO.println s!"EmitOne: so it emits every registration file of {t} ({mods.length}), \
      as Emit.lean does"
    let driver := emit / s!"One{t}.lean"
    let setup := emit / s!"One{t}.json"
    if let some code ← setUp driver setup mods then return code
    let code ← runProc lean <|
      #["--setup", setup.toString, "--run", driver.toString] ++
      (if check then #["--check"] else #[]) ++
      #["--part", (emit / s!"One{t}.targets").toString, dest.toString]
    unless code == 0 do return code
  return 0
