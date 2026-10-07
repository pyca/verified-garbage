import VerifiedGarbage.TCB.Emit

/-!
# The emitter, for one algorithm on one target

For iterating on one algorithm: builds only the registration files named on
the command line (and what they import), and emits only their files, rather
than building every module of the library as `Emit.lean` needs. Run it from
`lean/`:

* `lake env lean --run EmitOne.lean Rc2.AArch64 [More.Target …]` builds
  `VerifiedGarbage/Artifacts/Rc2/AArch64.lean`, and writes its files under
  `../src/asm`.
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
`mod.rs` files. It refuses a file that does not exist yet (a new module also
changes `mod.rs`) or that has functions it did not generate (another
registration file emits into it): `Emit.lean` handles those. It is a
convenience while iterating, not a replacement: `Emit.lean --check`, which CI
runs, checks every artifact and every file.
-/

open System

def nativeTCB : FilePath :=
  ".lake" / "build" / "lib" /
    if System.Platform.isWindows then "VerifiedGarbage_NativeTCB.dll"
    else s!"libVerifiedGarbage_NativeTCB.{if System.Platform.isOSX then "dylib" else "so"}"

def usage : String := "usage: lake env lean --run EmitOne.lean [--check] <Alg>.<Target> …"

/-- The names of the functions a generated file defines. -/
def fnNames (text : String) : List String :=
  (text.splitOn "\n").filterMap fun line =>
    match line.splitOn "extern \"C\" fn " with
    | [_, rest] => some ((rest.splitOn "(").headD "")
    | _ => none

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
  -- Build what the driver imports, and the trusted base's shared library;
  -- reporting warnings and errors, not the profile every module records
  -- (`lakefile.toml`), which Lake replays for each one it finds built.
  let mods := regs ++ gens.flatMap (·.2) ++ vars.flatMap (·.2)
  let code ← runProc "lake"
    (#["build", "--log-level=warning", "NativeTCB:shared"] ++ (mods.map ("+" ++ ·)).toArray)
  unless code == 0 do return code
  let driver : FilePath := ".lake" / "emit" / "One.lean"
  let out : FilePath := ".lake" / "emit" / "one"
  IO.FS.createDirAll ".lake/emit"
  if ← out.pathExists then IO.FS.removeDirAll out
  IO.FS.writeFile driver (VG.Emit.driver regs gens vars)
  let code ← runProc (← IO.appPath).toString
    #[s!"--load-dynlib={nativeTCB}", "--run", driver.toString, out.toString]
  unless code == 0 do return code
  -- Copy or compare each generated file but `mod.rs`.
  let dest : FilePath := ".." / "src" / "asm"
  let mut ok := true
  for path in ← out.walkDir do
    unless path.extension == some "rs" && path.fileName != some "mod.rs" do continue
    let rel := (path.toString.dropPrefix (out.toString ++ "/")).toString
    let target := dest / rel
    let text ← IO.FS.readFile path
    unless ← target.pathExists do
      IO.eprintln s!"{target} does not exist: a new module, run Emit.lean"
      ok := false
      continue
    let current ← IO.FS.readFile target
    let others := (fnNames current).filter (!(fnNames text).contains ·)
    unless others.isEmpty do
      IO.eprintln s!"{target} also has {others}, from other registration files: run Emit.lean"
      ok := false
      continue
    if current == text then continue
    if check then
      IO.eprintln s!"{target} is out of date"
      ok := false
    else
      IO.FS.writeFile target text
      IO.println s!"wrote {target}"
  return if ok then 0 else 1
