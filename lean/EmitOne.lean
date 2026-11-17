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
`#assert_spec_origin`) as `Emit.lean`, on these artifacts only, into
`.lake/emit/one`, and then copies (or compares) each file it generated but the
crate's root `lib.rs` and `consts/mod.rs`, and each module's assembly file
(`assembly/<module>.s`). It refuses a file that does not
exist yet (a new module also changes `lib.rs`) or that has functions it did not generate (another
registration file emits into it): `Emit.lean` handles those. Each table of
constants has a file of its own (`consts/<name>.rs` of the crate, which
depends only on the table), so it writes those of its artifacts' tables and
leaves the others; a new table is a new file. So does each internal function
(`internal/<name>.rs`, `VG.Rust.Internal`), which depends only on its code;
the module whose file declares it depends on all the modules calling it,
which only `Emit.lean` sees. It is a
convenience while iterating, not a replacement: `Emit.lean --check`, which CI
runs, checks every artifact and every file.
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
  let regs := (← VG.Emit.registrations).filter fun m =>
    names.any fun n => m == s!"VerifiedGarbage.Artifacts.{n}"
  for n in names do
    unless regs.contains s!"VerifiedGarbage.Artifacts.{n}" do
      IO.eprintln s!"{n}: no registration file VerifiedGarbage/Artifacts/{n.replace "." "/"}.lean"
      return 2
  let driver : FilePath := ".lake" / "emit" / "One.lean"
  let out : FilePath := ".lake" / "emit" / "one"
  IO.FS.createDirAll ".lake/emit"
  if ← out.pathExists then IO.FS.removeDirAll out
  IO.FS.writeFile driver (VG.Emit.driver regs)
  -- A module, run with Lake's setup for it (`Emit.lean`'s `main` says why),
  -- which builds what it imports: the registration files, what they import,
  -- and the trusted base's shared libraries, which it loads (what no target
  -- owns, and their targets'). On a failure, it reports the warnings and
  -- errors, not the profile every module records (`lakefile.toml`).
  let setup : FilePath := ".lake" / "emit" / "One.json"
  let r ← IO.Process.output { cmd := "lake", args := #["setup-file", driver.toString] }
  unless r.exitCode == 0 do
    IO.eprint (withoutInfo r.stderr)
    return r.exitCode
  IO.FS.writeFile setup r.stdout
  let code ← runProc (← IO.appPath).toString
    #["--setup", setup.toString, "--run", driver.toString, out.toString]
  unless code == 0 do return code
  -- Copy or compare each generated file but the crates' `lib.rs` and `consts/mod.rs`.
  let dest : FilePath := ".." / "crates"
  let mut ok := true
  for path in ← out.walkDir do
    unless path.extension == some "rs" && path.fileName != some "mod.rs" &&
        path.fileName != some "lib.rs" do continue
    let rel := (path.toString.dropPrefix (out.toString ++ "/")).toString
    let target := dest / rel
    let text ← IO.FS.readFile path
    unless ← target.pathExists do
      IO.eprintln s!"{target} does not exist: a new module, run Emit.lean"
      ok := false
      continue
    let current ← IO.FS.readFile target
    if unreadFns current || unreadFns text then
      IO.eprintln s!"{target}: cannot read the names of its functions: run Emit.lean"
      ok := false
      continue
    let others := (fnNames current).filter (!(fnNames text).contains ·)
    unless others.isEmpty do
      IO.eprintln s!"{target} also has {others}, from other registration files: run Emit.lean"
      ok := false
      continue
    -- The file, and its module's assembly file (`Rust.assemblyFile`), which has the
    -- same functions: `assembly/<module>.s`, or `assembly/internal/<name>.s` of an
    -- internal function's, `internal/<name>.rs`.
    let mut pairs := #[(target, text)]
    if let [crate, m] := rel.splitOn "/src/" then
      if m.endsWith ".rs" && (!m.contains '/' || m.startsWith "internal/") then
        let l := s!"{crate}/{VG.Rust.assemblyFile (m.dropEnd 3).toString}"
        pairs := pairs.push (dest / l, ← IO.FS.readFile (out / l))
    for (tgt, text) in pairs do
      let current ← if ← tgt.pathExists then IO.FS.readFile tgt else pure ""
      if current == text then continue
      if check then
        IO.eprintln s!"{tgt} is out of date"
        ok := false
      else
        IO.FS.writeFile tgt text
        IO.println s!"wrote {tgt}"
  return if ok then 0 else 1
