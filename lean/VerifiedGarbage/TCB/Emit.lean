module

public import VerifiedGarbage.TCB.Rust

/-!
# The emitter

**Trusted.** What `Emit.lean` runs: which artifacts are emitted, and how the
generated files are written or checked.

The artifacts emitted are those of every *registration file*: each `.lean` file under `VerifiedGarbage/Artifacts/`,
say `VerifiedGarbage/Artifacts/Sha3/X86_64.lean`, must define the list
`VG.Artifacts.Sha3.X86_64.artifacts : List Artifact`. Adding functions for
an algorithm or a target adds such a file, so that parallel changes don't
all edit one list.

## Variants and generic callers

Some functions have several implementations with the same contract (e.g. a
compression function in scalar code and with the SHA extensions), and other
functions call them. A caller whose proof holds for any implementation is
*generic*: it is emitted once for each implementation, each a direct call
of that implementation. Adding an implementation must not edit its callers,
so both are found by their files:

* a *variant* file, `VerifiedGarbage/Variants/<Iface>/<Target>/<Name>.lean`,
  defines `VG.Variants.<Iface>.<Target>.<Name>.variant`, one implementation
  of the interface `<Iface>` on `<Target>`;
* a *generic* file, `VerifiedGarbage/Generic/<Iface>/<Target>/<Alg>.lean`,
  defines `VG.Generic.<Iface>.<Target>.<Alg>.artifacts`, a function from a
  variant of `<Iface>` on `<Target>` to a list of artifacts.

A caller of functions of several interfaces (e.g. a key derivation calling
both a hash's compression function and a block function, each with its own
implementations) is generic over all of them: its file is
`VerifiedGarbage/Generic/<Iface₁>/…/<Ifaceₙ>/<Target>/<Alg>.lean`, and its
`artifacts` takes a variant of each interface on `<Target>`, in that order.
Variants of different interfaces may have the same suffix (e.g. `_avx2`), so
the instances of such a caller are named by `qualifiedName`: its name, then
for each interface whose variant has a non-empty suffix, in that order, a tag
for the interface and the suffix (`vg_argon2_blake2b_avx2_g_avx512`;
the instance of the baseline variants keeps the plain name, `vg_argon2`).
Callers of one interface append the suffix alone (`vg_sha256_update_shani`).

The artifacts emitted include each generic function applied to each variant
of its interface and target (each combination of a variant of each of its
interfaces), in order of their module names. What a variant is (its type)
is up to the interface, as long as every variant and every generic function
of it agree, which elaboration checks. Nothing here needs trusting beyond
the files found: every artifact carries its own proof, and
the emitter checks its calls and features (`Rust.files`) as for any other.
A variant's own functions (e.g. the implementation itself) are listed in a
registration file as usual.

`Emit.lean` finds the registration, variant and generic files
(`registrations`, `grouped`, `genericGroups`), and for each target directory
(`parts`) writes a module that defines the target's list, a file that checks
that the list depends only on the standard axioms, that what it runs is what
the kernel checked and that the `Spec/` names it uses come from `Spec/`
(`TCB/Audit.lean`), which `lake build` builds, and a program whose `main` runs
`run` on the list (`prepare`, see "Drivers as modules" below), and runs those
programs. `EmitOne.lean` writes a single program that does all three for the
files it is given (`driver`).
-/

@[expose] public section

namespace VG.Emit

open System

/-- The directory of the registration files, relative to `lean/`. -/
def registrationDir : FilePath := "VerifiedGarbage" / "Artifacts"

/-- The module of the Lean file `path` (relative to `lean/`), e.g.
`VerifiedGarbage.Artifacts.Sha3.X86_64`. -/
def moduleOf (path : FilePath) : String :=
  ".".intercalate ((path.withExtension "").components.filter (· != "."))

/-- The directory of the variant files, relative to `lean/`. -/
def variantDir : FilePath := "VerifiedGarbage" / "Variants"

/-- The directory of the generic files, relative to `lean/`. -/
def genericDir : FilePath := "VerifiedGarbage" / "Generic"

/-- The modules of the `.lean` files under `dir`, in order of their names. -/
def modulesUnder (dir : FilePath) : IO (List String) := do
  unless ← dir.pathExists do return []
  let files ← dir.walkDir
  let mods := files.toList.filter (·.extension == some "lean") |>.map moduleOf
  return mods.mergeSort (· ≤ ·)

/-- The registration modules: the `.lean` files under `registrationDir`, in
order of their module names. -/
def registrations : IO (List String) := modulesUnder registrationDir

/-- The interface and target of a variant module `mod`, e.g.
`Sha256Compress.X86_64` for `VerifiedGarbage.Variants.Sha256Compress.X86_64.ShaNi`;
`none` unless it is exactly three levels below the directory. -/
def groupOf (mod : String) : Option String :=
  match mod.splitOn "." with
  | [_, _, i, t, _] => some s!"{i}.{t}"
  | _ => none

/-- The modules under `dir`, grouped by interface and target (`groupOf`), in
order of the groups' names; fails on a module at any other depth. -/
def grouped (dir : FilePath) : IO (List (String × List String)) := do
  let mods ← modulesUnder dir
  let mut groups : List (String × List String) := []
  for m in mods do
    let some g := groupOf m
      | throw <| IO.userError s!"{m} must be at {dir}/<Iface>/<Target>/<Name>.lean"
    groups := match groups.find? (·.1 == g) with
      | some _ => groups.map fun (h, ms) => if h == g then (h, ms ++ [m]) else (h, ms)
      | none => groups ++ [(g, [m])]
  return groups.mergeSort (·.1 ≤ ·.1)

/-- The name of the list a registration module defines:
`VerifiedGarbage.Artifacts.Sha3.X86_64` defines
`VG.Artifacts.Sha3.X86_64.artifacts`. -/
def listOf (mod : String) : String :=
  "VG." ++ (mod.dropPrefix "VerifiedGarbage.").toString ++ ".artifacts"

/-- The variant a variant module defines:
`VerifiedGarbage.Variants.Sha256Compress.X86_64.ShaNi` defines
`VG.Variants.Sha256Compress.X86_64.ShaNi.variant`. -/
def variantOf (mod : String) : String :=
  "VG." ++ (mod.dropPrefix "VerifiedGarbage.").toString ++ ".variant"

/-- The interfaces of a generic module `mod`, each with its target:
`["Sha256Compress.X86_64"]` for
`VerifiedGarbage.Generic.Sha256Compress.X86_64.Pbkdf2`, and
`["Blake2b.X86_64", "Argon2Compress.X86_64"]` for
`VerifiedGarbage.Generic.Blake2b.Argon2Compress.X86_64.Argon2`; `none`
unless there is at least one interface, a target and a name below the
directory. -/
def interfacesOf (mod : String) : Option (List String) :=
  match mod.splitOn "." with
  | _ :: _ :: rest =>
    match rest.reverse with
    | _ :: t :: i :: is => some ((i :: is).reverse.map (· ++ "." ++ t))
    | _ => none
  | _ => none

/-- The modules under `dir` (generic files), grouped by their interfaces
(`interfacesOf`), in order of the groups' names; fails on a module with no
interface. -/
def genericGroups (dir : FilePath) : IO (List (List String × List String)) := do
  let mods ← modulesUnder dir
  let mut groups : List (List String × List String) := []
  for m in mods do
    let some g := interfacesOf m
      | throw <| IO.userError s!"{m} must be at {dir}/<Iface>/…/<Target>/<Name>.lean"
    groups := match groups.find? (·.1 == g) with
      | some _ => groups.map fun (h, ms) => if h == g then (h, ms ++ [m]) else (h, ms)
      | none => groups ++ [(g, [m])]
  return groups.mergeSort fun a b => ".".intercalate a.1 ≤ ".".intercalate b.1

/-- The name of an instance of a generic function of several interfaces
(see above): `base`, then `_<tag><suffix>` for each `(tag, suffix)` of
`parts` (one per interface, in order) whose suffix is not empty. Suffixes
start with `_`, so `qualifiedName "vg_argon2" [("blake2b", "_avx2"),
("g", "")]` is `vg_argon2_blake2b_avx2`. Two variants with the same
suffix in different interfaces give different names, as long as the tags
differ. -/
def qualifiedName (base : String) (parts : List (String × String)) : String :=
  base ++ String.join (parts.map fun (tag, suffix) =>
    if suffix.isEmpty then "" else "_" ++ tag ++ suffix)

/-- The name of the variable bound to a variant of the `i`th interface of a
generic function: `v`, then `v2`, `v3`, …. -/
def varName (i : Nat) : String := if i == 0 then "v" else s!"v{i + 1}"

/-- The artifacts of the generic modules `gens` of the same interfaces and
target, for each combination of a variant module of each interface, in
`vars` (one list per interface, in order): one term of type
`List Artifact`. -/
def instances (gens : List String) (vars : List (List String)) : String :=
  let names := (List.range vars.length).map varName
  let apply (g : String) : String := listOf g ++ String.join (names.map (" " ++ ·))
  let body := "List.flatten [" ++ ", ".intercalate (gens.map apply) ++ "]"
  (names.zip vars).foldr (fun (v, ms) acc =>
    s!"(List.flatMap (fun {v} => {acc}) [" ++ ", ".intercalate (ms.map variantOf) ++ "])") body

/-- The program that emits every artifact (`EmitOne.lean`'s, for the files
it is given): those of each registration
module `mods`, in order, then each generic function of `gens` applied to
each variant of its interface and target in `vars` (each combination of
variants of its interfaces). It fails to elaborate unless each module defines its list
(or variant), with types that agree, unless everything emitted depends
only on the standard axioms (`#assert_standard_axioms`), unless the compiled
code of everything emitted and of `run` is what the kernel checked
(`#assert_no_compiler_overrides`) and unless every `VG.Spec` definition is
declared in `Spec/` (`#assert_spec_origin`). -/
def driver (mods : List String) (gens : List (List String × List String) := [])
    (vars : List (String × List String) := []) : String :=
  let groups := gens.map fun (is, gs) =>
    (gs, is.map fun i => ((vars.find? (·.1 == i)).map (·.2)).getD [])
  "-- Generated by Emit.lean, which runs it. DO NOT EDIT.\n" ++
  "import VerifiedGarbage.TCB.Audit\n" ++
  "import VerifiedGarbage.TCB.Axioms\n" ++
  "import VerifiedGarbage.TCB.Emit\n" ++
  String.join ((mods ++ gens.flatMap (·.2) ++ vars.flatMap (·.2)).map fun m =>
    s!"import {m}\n") ++
  "\nnamespace VG.Emit\n\n" ++
  "def all : List Artifact := List.flatten [\n" ++
  String.join (mods.map fun m => s!"  {listOf m},\n") ++
  String.join (groups.map fun (gs, vs) => s!"  {instances gs vs},\n") ++
  "  []]\n\n" ++
  "#assert_standard_axioms all\n" ++
  "#assert_no_compiler_overrides all run\n" ++
  "#assert_spec_origin\n\n" ++
  "end VG.Emit\n\n" ++
  "def main (args : List String) : IO UInt32 := VG.Emit.run VG.Emit.all args\n"

/-! ## Drivers as modules, audits in the build

`Emit.lean` runs a driver per target directory (`parts`), as above, but
splits it in three files, so that the audits run in `lake build` and are
cached with the rest of the build rather than run again by every emitter run:

* the *module driver* `VGEmit.Driver.<Target>` (`moduleDriver`), a module
  that defines the target's artifacts `VG.Emit.<Target>.all` and nothing
  else. It imports each registration, generic and variant module of the
  target both ways: `public import` for `all`'s statement, and `public meta
  import`, without which a module imports no compiled code of its imports
  but through `import all` (Lean's `importModulesCore`), and running `all`
  needs all of it.
* the *audit* `VGEmit.Audit.<Target>` (`auditFile`), a file that is not a
  module, which imports the module driver and runs the three audits on that
  `all` and on `run`: a file that is not a module imports everything at the
  private level, every proof included (`TCB/Axioms.lean`), and Lake
  rebuilds it whenever anything it imports, transitively, changes, the
  private parts of modules included. Last, it records the digest of what it
  imported (`#record_audit_digest`, `TCB/Audit.lean`).
* the *runner* (`runnerFile`), a module importing the module driver both
  ways, whose `main` runs `run` on that `all`. Being a module, it imports
  far less than the old driver, which was not one (only what the registration
  modules import publicly, and the compiled code of the rest). It imports
  what the audit imports, and emits nothing, exiting with `staleCode`,
  unless the digest of what it imported is the one the audit recorded
  (`#check_audit_digest`): every module it runs is then byte for byte the one
  the audit audited.

The module drivers and audits are the library `VGEmit` (`lakefile.toml`), in
`libDir`, which `prepare` writes; `lake build` builds them with the rest. The
runner and the audit name the same constant of the same module, and the
runner checks that it imported exactly what the audit did, so what is emitted
is what was audited. `Emit.lean` builds the audits itself of the targets
whose files `prepare` changed or that were never built, and of those whose
runner exits with `staleCode`, and then runs those again. -/

/-- The exit code of a runner whose audit is not of what it imported. -/
def staleCode : UInt32 := 3

/-- The directory of the library `VGEmit` (its `srcDir` in `lakefile.toml`),
relative to `lean/`. -/
def libDir : FilePath := ".lake" / "emit" / "src"

/-- The module driver of the target directory `t`. -/
def driverModule (t : String) : String := s!"VGEmit.Driver.{t}"

/-- The audit of the target directory `t`. -/
def auditModule (t : String) : String := s!"VGEmit.Audit.{t}"

/-- The module driver of the target directory `t`, whose registration,
generic and variant modules are `mods`, `gens` and `vars` (as `driver` takes
them): `VG.Emit.<t>.all`, each registration module's list, in order, then
each generic function of `gens` applied to each variant of its interface and
target in `vars` (each combination of variants of its interfaces). -/
def moduleDriver (t : String) (mods : List String) (gens : List (List String × List String))
    (vars : List (String × List String)) : String :=
  let groups := gens.map fun (is, gs) =>
    (gs, is.map fun i => ((vars.find? (·.1 == i)).map (·.2)).getD [])
  "-- Generated by Emit.lean (`VG.Emit.moduleDriver`). DO NOT EDIT.\n" ++
  "module\n\n" ++
  "public import VerifiedGarbage.TCB.Emit\n" ++
  "public meta import VerifiedGarbage.TCB.Emit\n" ++
  String.join ((mods ++ gens.flatMap (·.2) ++ vars.flatMap (·.2)).map fun m =>
    s!"public import {m}\npublic meta import {m}\n") ++
  "\n@[expose] public section\n\n" ++
  s!"namespace VG.Emit.{t}\n\n" ++
  "def all : List Artifact := List.flatten [\n" ++
  String.join (mods.map fun m => s!"  {listOf m},\n") ++
  String.join (groups.map fun (gs, vs) => s!"  {instances gs vs},\n") ++
  "  []]\n\n" ++
  s!"end VG.Emit.{t}\n"

/-- The audit of the target directory `t`: it fails to elaborate unless
`VG.Emit.<t>.all` depends only on the standard axioms
(`#assert_standard_axioms`), the compiled code of it and of `run` is what
the kernel checked (`#assert_no_compiler_overrides`), every `VG.Spec`
definition is declared in `Spec/` (`#assert_spec_origin`); then it records
the digest of what it imported, `VG.Emit.<t>.auditDigest`
(`#record_audit_digest`). -/
def auditFile (t : String) : String :=
  "-- Generated by Emit.lean (`VG.Emit.auditFile`). DO NOT EDIT.\n" ++
  "import VerifiedGarbage.TCB.Audit\n" ++
  "import VerifiedGarbage.TCB.Axioms\n" ++
  s!"import {driverModule t}\n\n" ++
  s!"#assert_standard_axioms VG.Emit.{t}.all\n" ++
  s!"#assert_no_compiler_overrides VG.Emit.{t}.all VG.Emit.run\n" ++
  "#assert_spec_origin\n\n" ++
  s!"#record_audit_digest VG.Emit.{t}.auditDigest\n"

/-- The program that emits the artifacts of the target directory `t`: `run`
on the `all` of its module driver, if the audit of the target recorded the
digest of what this program imported (the module driver and the audit's own
imports, which it imports too, so that the two import the same modules);
otherwise it emits nothing, and exits with `staleCode`. -/
def runnerFile (t : String) : String :=
  "-- Generated by Emit.lean (`VG.Emit.runnerFile`). DO NOT EDIT.\n" ++
  "module\n\n" ++
  s!"public import {driverModule t}\n" ++
  s!"public meta import {driverModule t}\n" ++
  "public import VerifiedGarbage.TCB.Audit\n" ++
  "public meta import VerifiedGarbage.TCB.Audit\n" ++
  "public import VerifiedGarbage.TCB.Axioms\n" ++
  "public meta import VerifiedGarbage.TCB.Axioms\n\n" ++
  "public section\n\n" ++
  s!"#check_audit_digest {auditModule t} VG.Emit.{t}.auditDigest VG.Emit.{t}.audited\n\n" ++
  "def main (args : List String) : IO UInt32 :=\n" ++
  s!"  if VG.Emit.{t}.audited then VG.Emit.run VG.Emit.{t}.all args\n" ++
  "  else do\n" ++
  s!"    IO.eprintln \"{t}: the audit {auditModule t} is not of the modules this program imported\"\n" ++
  s!"    return {staleCode}\n"

/-- The runner of the target directory `t`, relative to `lean/`: outside
`libDir`, as nothing builds it. -/
def runnerPath (t : String) : FilePath := ".lake" / "emit" / s!"Run{t}.lean"

/-- The path of a module of `VGEmit`, relative to `lean/`. -/
def libPath (mod : String) : FilePath :=
  (mod.splitOn ".").foldl (· / ·) libDir |>.addExtension "lean"

/-- The files of the target directories `parts` (`parts`' result): each one's
module driver, audit and runner, as paths relative to `lean/` and their
text, with the target directory each is of. -/
def sources (parts : List (String × List String × List (List String × List String) ×
    List (String × List String))) : List (String × FilePath × String) :=
  parts.flatMap fun (t, mods, gens, vars) =>
    [(t, libPath (driverModule t), moduleDriver t mods gens vars),
     (t, libPath (auditModule t), auditFile t),
     (t, runnerPath t, runnerFile t)]

/-- Writes the files of `parts` (`sources`), each only if its text differs
from what is there, and deletes any other `.lean` file under `libDir`, so
that `VGEmit` has exactly these modules; the target directories one of whose
files it wrote. -/
def prepare (parts : List (String × List String × List (List String × List String) ×
    List (String × List String))) : IO (List String) := do
  let files := sources parts
  let mut changed : List String := []
  for (t, path, text) in files do
    if ← path.pathExists then
      if (← IO.FS.readFile path) == text then continue
    if let some d := path.parent then IO.FS.createDirAll d
    IO.FS.writeFile path text
    unless changed.contains t do changed := changed ++ [t]
  if ← libDir.pathExists then
    let expected := files.map fun (_, p, _) => p.normalize
    for path in ← libDir.walkDir do
      if path.extension == some "lean" && !expected.contains path.normalize then
        IO.FS.removeFile path
  return changed

/-- The target directory a registration, generic or variant module's path
names: `X86_64` for `VerifiedGarbage.Artifacts.Sha3.X86_64`,
`VerifiedGarbage.Generic.Sha256Compress.X86_64.Pbkdf2` and
`VerifiedGarbage.Variants.Sha256Compress.X86_64.ShaNi`. -/
def targetDirOf (mod : String) : Option String :=
  match mod.splitOn "." with
  | ["VerifiedGarbage", "Artifacts", _, t] => some t
  | "VerifiedGarbage" :: d :: rest =>
    if (d == "Generic" || d == "Variants") && rest.length ≥ 3 then rest[rest.length - 2]?
    else none
  | _ => none

/-- The registration modules `mods`, generic modules `gens` and variant
modules `vars` (as `driver` takes them) of each target directory
(`targetDirOf`), in order of its name; fails on a module without one.
`Emit.lean` runs a driver for each (a *part*): where they are split only
decides how much each process does, as `finish` checks that no target's
artifacts are in two parts. -/
def parts (mods : List String) (gens : List (List String × List String))
    (vars : List (String × List String)) :
    Except String (List (String × List String × List (List String × List String) ×
      List (String × List String))) := do
  let dirOf (m : String) : Except String String :=
    match targetDirOf m with
    | some t => pure t
    | none => throw s!"{m} names no target directory"
  let mut dirs : List String := []
  for m in mods ++ gens.flatMap (·.2) ++ vars.flatMap (·.2) do
    let t ← dirOf m
    unless dirs.contains t do dirs := dirs ++ [t]
  dirs.mergeSort (· ≤ ·) |>.mapM fun t => do
    let ms ← mods.filterM fun m => return (← dirOf m) == t
    let gs ← gens.filterMapM fun (is, gs) => do
      let gs ← gs.filterM fun g => return (← dirOf g) == t
      return if gs.isEmpty then none else some (is, gs)
    let vs ← vars.filterMapM fun (i, vs) => do
      let vs ← vs.filterM fun v => return (← dirOf v) == t
      return if vs.isEmpty then none else some (i, vs)
    return (t, ms, gs, vs)

def usage : String := "usage: lake env lean --run Emit.lean [--check] [DIR]"

/-- `[--check] [--part FILE] [DIR]`: whether to check rather than write, the
file a part writes its targets to, and the directory (by default
`../src/asm`). -/
def parseArgs (args : List String) : Option (Bool × Option String × FilePath) :=
  let (check, rest) := match args with
    | "--check" :: rest => (true, rest)
    | rest => (false, rest)
  let (part, rest) := match rest with
    | "--part" :: f :: rest => (some f, rest)
    | rest => (none, rest)
  match rest with
  | [] => some (check, part, "../src/asm")
  | [d] => some (check, part, d)
  | _ => none

/-- Writes `files` (paths relative to `dir` and their contents) under `dir`,
deleting any other `.rs` file under the directories `under` (relative to
`dir`, `""` for all of it) but those of `others`; or, if `check`, writes
nothing and fails if the files on disk differ from `files`. -/
def sync (dir : FilePath) (check : Bool) (files : List (String × String))
    (under others : List String) : IO Bool := do
  let mut ok := true
  unless check do IO.FS.createDirAll dir
  for (name, text) in files do
    let path := dir / name
    if let some parent := path.parent then
      unless check do IO.FS.createDirAll parent
    if check then
      let current ← if ← path.pathExists then IO.FS.readFile path else pure ""
      if current != text then
        IO.eprintln s!"{path} is out of date"
        ok := false
    else
      IO.FS.writeFile path text
      IO.println s!"wrote {path}"
  -- Any other `.rs` file there would be unverified code.
  let expectedPaths := files.map fun (n, _) => (dir / n).normalize
  let otherDirs := others.map fun (o : String) => (dir / o).normalize.toString ++ "/"
  for u in under do
    let d := if u.isEmpty then dir else dir / u
    unless ← d.pathExists do continue
    for path in ← d.walkDir do
      if path.extension == some "rs" && !expectedPaths.contains path.normalize &&
          !otherDirs.any (path.normalize.toString.startsWith ·) then
        if check then
          IO.eprintln s!"{path} is not generated from any artifact"
          ok := false
        else
          IO.FS.removeFile path
          IO.println s!"removed stale {path}"
  return ok

/-- Writes the files generated from `as` under the directory in `args` (by
default `../src/asm`), deleting any other `.rs` file there; or, if `args`
starts with `--check`, writes nothing and fails if the files on disk differ
from what would be generated.

With `--part FILE`, `as` are the artifacts of a part (`parts`): only the
files of their targets, `<target>/…`, are written or checked, and the
other `.rs` files under their directories; then `FILE` gets their targets,
for `finish`, which checks the root module and the rest of the
directory. -/
def run (as : List Artifact) (args : List String) : IO UInt32 := do
  let some (check, part, dir) := parseArgs args | do IO.eprintln usage; return 2
  let files ← match Rust.files as with
    | .ok files => pure files
    | .error e => do IO.eprintln e; return 1
  let targets := Rust.targetsOf as
  let ok ← match part with
    | none => sync dir check files [""] []
    | some _ =>
      let ts := targets.map (·.1)
      sync dir check (files.filter fun (n, _) => ts.any (n.startsWith <| · ++ "/")) ts []
  if !ok then
    IO.eprintln "run `lake build && lake env lean --run Emit.lean` in lean/ and commit the result"
    return 1
  if let some f := part then
    IO.FS.writeFile f (String.join (targets.map fun (t, c) => s!"{t}\t{c}\n"))
  return 0

/-- A target of two of the parts whose targets are `targets`, if any. -/
def inTwoParts (targets : List (List (String × String))) : Option String :=
  let names := targets.flatMap (·.map (·.1))
  names.find? fun t => (names.filter (· == t)).length > 1

/-- After `run` succeeded on every part, given the targets each wrote: no
target is in two parts (so each part generated all of its targets' files,
from all of their artifacts), the root module `mod.rs` is that of all the
targets (`Rust.rootFile`), and no other `.rs` file is outside their
directories. Writes or checks, as `run`. -/
def finish (targets : List (List (String × String))) (args : List String) : IO UInt32 := do
  let some (check, _, dir) := parseArgs args | do IO.eprintln usage; return 2
  if let some t := inTwoParts targets then
    IO.eprintln s!"the artifacts of the target {t} are in two parts"
    return 1
  let all := targets.flatten
  unless ← sync dir check [("mod.rs", Rust.rootFile all)] [""] (all.map (·.1)) do
    IO.eprintln "run `lake build && lake env lean --run Emit.lean` in lean/ and commit the result"
    return 1
  return 0

end VG.Emit
