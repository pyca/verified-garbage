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

A name may also be a generic group, `<Iface>.<Target>` (e.g.
`Sha256Compress.AArch64`), or `<Iface₁>.….<Ifaceₙ>.<Target>` for callers of
several interfaces (e.g. `Blake2b.Argon2Compress.X86_64`): its generic files
applied to its variants, as `Emit.lean` emits them.

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

/-- A shared library of the trusted base, as the lakefile names it
(`libName`; see `Emit.lean`). -/
def sharedLib (name : String) : FilePath :=
  ".lake" / "build" / "lib" /
    if System.Platform.isWindows then s!"{name}.dll"
    else s!"lib{name}.{if System.Platform.isOSX then "dylib" else "so"}"

/-- The libraries of the trusted base the driver loads for the named
registration files and groups, each named after its target last: `NativeTCB`
(what no target owns, which the others link) first, then each of their
targets' (`NativeTCB<Target>`), with their shared libraries' paths. -/
def nativeTCB (names : List String) : List (String × FilePath) :=
  let targets := names.foldl (init := ([] : List String)) fun ts n =>
    let t := (n.splitOn ".").getLastD ""
    if ts.contains t then ts else ts ++ [t]
  ("NativeTCB", sharedLib "VerifiedGarbage_NativeTCB") ::
    targets.map fun t => (s!"NativeTCB{t}", sharedLib s!"VerifiedGarbage_NativeTCB{t}")

def usage : String := "usage: lake env lean --run EmitOne.lean [--check] <Alg>.<Target> …"

/-- The names of the functions a generated file defines: each line declaring
`extern "<abi>" fn <name>(`, whatever its ABI (`"C"`, `"sysv64"`, …), and
each other name of one of them, `pub use self::<f> as <name>;`
(`VG.Rust.alias`). -/
def fnNames (text : String) : List String :=
  (text.splitOn "\n").filterMap fun line =>
    match line.splitOn "extern \"" with
    | [_, rest] =>
      match rest.splitOn "\" fn " with
      | [_, decl] => some ((decl.splitOn "(").headD "")
      | _ => none
    | _ =>
      if line.startsWith "pub use self::vg_" then
        match line.splitOn " as " with
        | [_, name] => some ((name.splitOn ";").headD "")
        | _ => none
      else none

/-- Whether a file declares functions, or other names of them, that `fnNames`
does not read: then it cannot tell which functions other registration files
emit into the file, and must not overwrite it. -/
def unreadFns (text : String) : Bool :=
  (fnNames text).length != ((text.splitOn "\n").filter fun l =>
    l.contains "fn vg_" || l.contains "use self::vg_").length

/-- Runs a process, inheriting its output; its exit code. -/
def runProc (cmd : String) (args : Array String) : IO UInt32 := do
  let child ← IO.Process.spawn { cmd, args }
  child.wait

/-- The name of a generic group on the command line, from its interfaces
(`VG.Emit.interfacesOf`): `Sha256Compress.AArch64` for
`["Sha256Compress.AArch64"]`, `Blake2b.Argon2Compress.X86_64` for
`["Blake2b.X86_64", "Argon2Compress.X86_64"]`. -/
def groupName (is : List String) : String :=
  let target := ((is.headD "").splitOn ".").getLastD ""
  ".".intercalate (is.map fun i => (i.splitOn ".").headD "") ++ "." ++ target

def main (args : List String) : IO UInt32 := do
  let (check, names) := match args with
    | "--check" :: rest => (true, rest)
    | rest => (false, rest)
  if names.isEmpty || names.any (·.startsWith "-") then
    IO.eprintln usage
    return 2
  let regs := (← VG.Emit.registrations).filter fun m =>
    names.any fun n => m == s!"VerifiedGarbage.Artifacts.{n}"
  let gens := (← VG.Emit.genericGroups VG.Emit.genericDir).filter fun g =>
    names.contains (groupName g.1)
  let vars := (← VG.Emit.grouped VG.Emit.variantDir).filter fun v =>
    gens.any (·.1.contains v.1)
  for n in names do
    unless regs.contains s!"VerifiedGarbage.Artifacts.{n}" || gens.any (groupName ·.1 == n) do
      IO.eprintln s!"{n}: no registration file VerifiedGarbage/Artifacts/{n.replace "." "/"}.lean \
        and no generic group {n}"
      return 2
  -- Build what the driver imports, and the trusted base's shared libraries
  -- (what no target owns, and their targets'); reporting warnings and
  -- errors, not the profile every module records (`lakefile.toml`), which
  -- Lake replays for each one it finds built.
  let mods := regs ++ gens.flatMap (·.2) ++ vars.flatMap (·.2)
  let libs := nativeTCB names
  let code ← runProc "lake"
    (#["build", "--log-level=warning"] ++ (libs.map fun (l, _) => s!"{l}:shared").toArray ++
      (mods.map ("+" ++ ·)).toArray)
  unless code == 0 do return code
  let driver : FilePath := ".lake" / "emit" / "One.lean"
  let out : FilePath := ".lake" / "emit" / "one"
  IO.FS.createDirAll ".lake/emit"
  if ← out.pathExists then IO.FS.removeDirAll out
  IO.FS.writeFile driver (VG.Emit.driver regs gens vars)
  -- A module, run with Lake's setup for it (`Emit.lean`'s `main` says why).
  let setup : FilePath := ".lake" / "emit" / "One.json"
  let r ← IO.Process.output { cmd := "lake", args := #["setup-file", driver.toString] }
  unless r.exitCode == 0 do
    IO.eprint r.stderr
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
