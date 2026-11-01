module

public import VerifiedGarbage.TCB.Artifact

/-!
# Rendering artifacts as Rust

**Trusted.** Every artifact becomes a Rust naked function whose entire body
is the printed assembly:

```rust
#[unsafe(naked)]
pub unsafe extern "<abi>" fn <name><sig> {
    core::arch::naked_asm!(
        r"<line>
<line>
…",
    )
}
```

A naked function has no compiler-generated prologue or epilogue, so the
machine code that runs is exactly the code that was verified (plus the
final `ret` from the printer). The functions of each target are a crate
of their own, `verified-garbage-asm-<target>` (`crateDir`, under `crates/`;
its `Cargo.toml` is written by hand), one file `<module>.rs` per `module`,
in its `src/` (`codeDir`), compiled only under the target's `cfg` (`targetRoot`), whose
items are therefore `pub`. The library depends on the crate of the target
it is built for and names it `crate::arch` (`Cargo.toml`, `src/lib.rs`).

The functions are in crates of their own, rather than modules of the
library, for the time it takes to compile them: rustc puts naked functions
in LLVM's module-level assembly, and in a release build LLVM's ThinLTO
parses all of a codegen unit's module-level assembly again each time it
imports a function from that unit, which it does for the Rust functions it
shares a unit with. In a crate of their own they share a unit with none.

Artifacts of a module can render to the same function but for its name
(and documentation and constants): the same `cfg` attribute, calling
convention, signature and body, calls and tables included (`sameKey`), as
when a generic caller's instances for two variants of an interface call
none of what tells the variants apart. Only the one with the shortest name
is then emitted as a function, and each other as another name of it
(`alias`), keeping its own documentation, saying so, and its own constants:

```rust
#[allow(unused_imports)]
pub use self::<the function's name> as <name>;
```

Calling it runs that function, whose text is the text the artifact's own
function would have: the same machine code, which its proof verified
against its own contract. Only artifacts of the same module are
compared, so that every file is a function of its own artifacts alone
(which `EmitOne.lean` relies on).

A call (`Code.call name body`) is a call instruction whose operand is the
symbol of the Rust function `name` (a `sym` operand). The model runs `body`
for it, so `files` checks that the function emitted as `name` has printed
code exactly that of `body`, for every call, including the calls in `body`
itself; otherwise nothing is emitted. That function is the artifact `name`
of the same target, if there is one, and otherwise an *internal function*
(`Internal`), which the emitter writes from `body` itself: a function that
only the code of artifacts calls needs no `Api`, contract or proof of its
own, as the proof of every artifact that calls it covers its code. Each is a
naked function of no parameters in a file of its own, `internal/<name>.rs`
of the crate's `codeDir` (its text in `assembly/internal/<name>.s`), a
module that the file of one module calling it declares (`Internal.owner`,
`internalOwner`: that of the algorithm the function's name starts with, so
that changes to different algorithms change different files), `pub(crate)`,
so that only the generated code of the crate can name it:

```rust
// internal/<name>.rs
#[unsafe(naked)]
pub(crate) unsafe extern "<abi>" fn <name>() {
    core::arch::naked_asm!(…)
}

// <owner>.rs
#[rustfmt::skip]
#[path = "internal/<name>.rs"]
pub(crate) mod <name>;
```

Its name comes from code no one reviews (`Impl/`), so `files` checks that
it is a Rust function's (`internalName`); its file, like a table's, depends
on nothing but its name and code, so `EmitOne.lean` writes those its
artifacts call without touching the others (but where it is declared depends
on the modules of the artifacts calling it, all of which `Emit.lean` sees). Every table of constants it
names is one of each artifact that calls it, or one its instructions carry
(`checkInternalTables`): the contract of that artifact, which its proof
assumes when it runs the internal function's code, says the memory holds
its tables (`Abi.withConsts`), as an artifact the artifact calls must.

The documentation of each function is its `doc`, with what its contract
requires of the memory each buffer is valid for and of where its buffers are
added to its `# Safety` section (`fullDoc`, `Sig.validDoc`, `Sig.layoutDoc`):
the latter depends on the target's calling convention and on the stack the
code uses, and both are generated from the same signature, calling
convention, `writeArgs` and `stack` as the contract (`Artifact.ofSig`), so
the `doc` must not state them itself (`checkLayout`).

An artifact that reads tables of constants (`Artifact.consts`, and those
its instructions carry, `Printer.tables`: `tablesOf`) names each
by the name of a `static` holding it, which `files` writes once per target,
each in a file of its own, `consts/<name>.rs` of its crate's `codeDir` (its name in
lowercase), after checking that every artifact of the target with a table of
that name gives the same words and that the code names only its own tables
(`checkConsts`). `consts/mod.rs` declares `Table` and each table's module,
and re-exports its `static`, which the code names as `super::consts::<NAME>`:

```rust
#[repr(C, align(64))]
pub struct Table<const N: usize>(pub [u8; N]);

pub static <NAME>: Table<<8 n>> = Table(*b"\
    <the 8 bytes of word 0, least significant first, as \xHH>\
    …
");
```

A table's file depends on nothing but its name and words, so `EmitOne.lean`
writes those of its artifacts' tables without touching the others.

`Table` holds the bytes of the words at its start (`repr(C)`, one field),
each word little-endian as the contract's memory holds it
(`Abi.constsHeld`), so the static's address is that of word 0. It aligns each table to 64 bytes, a
cache line on every target, so that where a table's entries fall in cache
lines depends only on the table, not on the size of whatever the linker puts
before it (a change to one table would otherwise move the others, and their
functions' timing with them). Its name cannot be a table's (`tableName`).

The code forms a table's address from the static's symbol (a `sym`
operand), on AArch64 by `adrp` and `add` (`Line.sym`), whose operands
`vg_sym_page!` and `vg_sym_pageoff!` (each crate's `lib.rs`, `targetRoot`) write in the syntax
of the object format: `<sym>@PAGE` and `<sym>@PAGEOFF` for Mach-O, on
Apple's platforms, and `<sym>` and `:lo12:<sym>` for ELF and COFF; on
x86-64 by `lea` of the RIP-relative operand `[rip + <sym>]`, which is the
same in every object format (`SymPart.ripRel`); on IA-32, by a call to the
next instruction and an ADD of the difference between its return address
and the static (`SymPart.x86PcRel`, the ADD immediate emitted as `.long`
because LLVM's Intel-syntax operand parser rejects symbol differences); on
ARMv7, by `movw` and `movt` of the difference between the static and the
`pc` an `add` then adds (`SymPart.armPcRel`, the same text in ARM and Thumb
code, and position independent; ELF only, as COFF, for Windows' Thumb
targets, cannot represent the difference, so such code does not assemble
there); on PPC64LE, by `bcl 20, 31` to the next instruction, `mflr` of
the address it leaves in the link register, and `addis` and `addi` of the
high and low halves of the static's distance from there
(`SymPart.ppcHa`, `SymPart.ppcLo`: `(<sym> - 2b)@ha` and `@l`, the
relocations `R_PPC64_REL16_HA` and `R_PPC64_REL16_LO`, position
independent); on RISC-V, by `lla` of the symbol (`SymPart.bare`), which
the assembler expands to `auipc` and `addi` with the relocations
`R_RISCV_PCREL_HI20` and `R_RISCV_PCREL_LO12_I`, position independent. The
linker resolves them to the static's address, which the model gives
(`State.syms`, fixed for the run as a static's address is) and at which the
contract (`Abi.withConsts`) says the memory holds the table, readable,
apart from every writable region and at a multiple of 64 (`Table`'s
alignment): a `static` is a distinct immutable object, at a multiple of its
type's alignment.

An artifact whose code needs CPU features beyond the target's baseline
(`Artifact.features`) also gets a last `# Safety` item saying the CPU must
support them, and a constant of them, for the Rust that checks for them
before calling it: a `Features` set (the crate `verified_garbage_cpu`,
`crates/verified-garbage-cpu/`), the union of the bits
`verified_garbage_cpu::feature::<FEATURE>` of their names in uppercase
(`featureConst`), which does not compile with a name that crate does not
know (a constant it does not define):

```rust
/// The CPU features `<name>` requires (`Artifact.features`).
pub const <NAME>_FEATURES: verified_garbage_cpu::Features =
    verified_garbage_cpu::Features(verified_garbage_cpu::feature::<FEATURE> | …);
```

(rustc evaluates every constant of the crate, and an `|` of constants is a
few steps of its evaluator, where a call of a `const fn` on the names, as
these once were, cost it a tenth of a build of the crate.)

`files` checks that `features` are exactly the features the code requires.
(The functions get no `#[target_feature]` attribute: Rust does not allow one
on naked functions. The x86 assemblers accept every instruction without it;
on AArch64 the printer's `enableFeature`/`disableFeature` directives enable
each feature for the function's body only.) A feature that some of the
target's configurations cannot assemble or must never run has a `cfg`
(`Printer.featureCfg`, ARMv7's `umaal`): the function and its constants are
compiled only under it, `#[cfg(<predicate>)]`.
-/

@[expose] public section

namespace VG.Rust

universe u

/-- Escape a string for a Rust string literal that is also an `asm!`
template: `{`/`}` are template placeholders and must be doubled. -/
def escape (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    match c with
    | '{' => acc ++ "{{"
    | '}' => acc ++ "}}"
    | '\\' => acc ++ "\\\\"
    | '"' => acc ++ "\\\""
    | '\n' => acc ++ "\\n"
    | c => acc.push c

/-- `s` as an `asm!` template: `{`/`}` are placeholders and must be doubled. -/
def escapeBraces (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    match c with
    | '{' => acc ++ "{{"
    | '}' => acc ++ "}}"
    | c => acc.push c

/-- A Rust string literal whose value is `s`: a raw string literal, which
rustc reads faster (it maps each character of an ordinary literal's
template back to the source by unescaping it), `r"…"`, or `r#"…"#` if `s`
has a `"` (`.base64`'s string, `packRun`); an ordinary one if `s` has a
carriage return, which a raw string literal cannot hold, or a `"#`. -/
def literal (s : String) : String :=
  if s.contains '\r' || (s.splitOn "\"#").length > 1 then
    "\"" ++ s.foldl (init := "") (fun acc c =>
      match c with
      | '\\' => acc ++ "\\\\"
      | '"' => acc ++ "\\\""
      | '\n' => acc ++ "\\n"
      | '\r' => acc ++ "\\r"
      | c => acc.push c) ++ "\""
  else if s.contains '"' then "r#\"" ++ s ++ "\"#"
  else "r\"" ++ s ++ "\""

def header : String :=
  "// @generated by lean/Emit.lean. DO NOT EDIT.\n"

def docComment (indent doc : String) : String :=
  String.join ((doc.splitOn "\n").map fun l =>
    if l.isEmpty then s!"{indent}///\n" else s!"{indent}/// {l}\n")

/-- The distinct values of `as`, in first-seen order. -/
def dedup (as : List String) : List String :=
  as.foldl (init := []) fun acc a => if acc.contains a then acc else acc ++ [a]

/-- The text of one line of the `naked_asm!` template (`escapeBraces`): a
call names its function as the operand of the same name. `none` for the
page of a static's address or its offset in the page, which a macro writes
in the syntax of the object format (`line`). -/
def lineText (call : String) : Line → Option String
  | .text l => some (escapeBraces l)
  | .call n => some (escapeBraces call ++ " {" ++ n ++ "}")
  | .sym s .ripRel n => some (escapeBraces s ++ "[rip + {" ++ n ++ "}]")
  | .sym s .x86PcRel n => some (escapeBraces s ++ "{" ++ n ++ "} - 2b")
  | .sym s .armPcRel n => some (escapeBraces s ++ "{" ++ n ++ "} - (2f + 2 * (3f - 2f)))")
  | .sym s .ppcHa n => some (escapeBraces s ++ "{" ++ n ++ "} - 2b)@ha")
  | .sym s .ppcLo n => some (escapeBraces s ++ "{" ++ n ++ "} - 2b)@l")
  | .sym s .bare n => some (escapeBraces s ++ "{" ++ n ++ "}")
  | .sym _ .page _ | .sym _ .pageOff _ => none

/-- One line of the `naked_asm!` template as an argument of its own. -/
def line (call : String) : Line → String
  | .sym s .page n => s!"        concat!(\"{escape s}\", vg_sym_page!(\"" ++ "{" ++ n ++ "}\")),\n"
  | .sym s .pageOff n =>
    s!"        concat!(\"{escape s}\", vg_sym_pageoff!(\"" ++ "{" ++ n ++ "}\")),\n"
  | l => "        " ++ literal ((lineText call l).getD "") ++ ",\n"

/-- The text of a comment line of a printer (`// <text>` on one line: the
text of an instruction that the printer emits as its machine code, in the
directive after it), which is not a line of the assembly: `template` leaves
it out, and the assembly file has it (`assembly`). -/
def commentOf : Line → Option String
  | .text l =>
    if l.startsWith "// " && !l.contains '\n' && !l.contains '\r' then some l else none
  | _ => none

/-- The directive of a printer's encoded instructions, one word each, that
`pushLine` joins: `.inst` (AArch64's, `TCB/AArch64/Encode.lean`), which
marks its words as instructions (the object's mapping symbols), unlike the
data that `packRun` writes. -/
def joinable : List String := [".inst "]

/-- The value of a hexadecimal digit. -/
def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

/-- The value of `n` lowercase hexadecimal digits after `0x`. -/
def hexValue? (n : Nat) (p : String) : Option Nat :=
  match p.toList with
  | '0' :: 'x' :: ds =>
    if ds.length == n then ds.foldlM (fun v c => return v * 16 + (← hexDigit c)) 0 else none
  | _ => none

/-- The bytes of an encoded `.byte` line, as x86's printers emit each
instruction (`TCB/X86/Encode.lean`'s `byteLine`): `.byte ` then bytes of two
lowercase hexadecimal digits each (`0xNN`), separated by commas alone;
`none` for any other line (e.g. `symPush`'s `.byte 0x81, 199`). -/
def byteLine? (l : String) : Option (List Nat) :=
  if l.startsWith ".byte " then ((l.drop 6).toString.splitOn ",").mapM (hexValue? 2) else none

/-- The bytes of an encoded `.long` line, as PPC64LE's printer emits each
instruction (`TCB/PPC64LE/Encode.lean`'s `longLine`): `.long ` then words of
eight lowercase hexadecimal digits each (`0xNNNNNNNN`), separated by commas
alone, each little-endian (GNU as, "`.long`", in the target's byte order,
little-endian on PPC64LE); `none` for any other line (e.g. x86's
`.long {VG_TABLE} - 2b`). -/
def wordLine? (l : String) : Option (List Nat) :=
  if l.startsWith ".long " then
    ((l.drop 6).toString.splitOn ",").flatMapM fun w => do
      let v ← hexValue? 8 w
      return [v % 256, v / 256 % 256, v / 65536 % 256, v / 16777216 % 256]
  else none

/-- The bytes of a line that a printer emits as an instruction's machine
code as data (`byteLine?`, `wordLine?`), if it is one. -/
def dataBytes? (l : String) : Option (List Nat) := (byteLine? l).orElse fun _ => wordLine? l

/-- The base64 encoding of the bytes `bs` (RFC 4648, §4: the standard
alphabet, padded with `=`). -/
def base64 (bs : List Nat) : String :=
  let alphabet := "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".toList
  let digit (n : Nat) : Char := alphabet.getD (n % 64) '='
  String.ofList (go bs digit)
where
  go (bs : List Nat) (digit : Nat → Char) : List Char :=
    match bs with
    | a :: b :: c :: rest =>
      let v := a * 65536 + b * 256 + c
      [digit (v / 262144), digit (v / 4096), digit (v / 64), digit v] ++ go rest digit
    | [a, b] =>
      let v := a * 65536 + b * 256
      [digit (v / 262144), digit (v / 4096), digit (v / 64), '=']
    | [a] => let v := a * 65536; [digit (v / 262144), digit (v / 4096), '=', '=']
    | [] => []

/-- The lines of a run of template lines `ls` as they are written: each run of
consecutive lines of encoded instructions' bytes (`dataBytes?`) as one line,
`.base64 "<their bytes>"` (the assembler's `.base64` directive, which emits
the bytes its string encodes: LLVM 22's, Rust 1.95's assembler, the
workspace's `rust-version`), so that rustc and the assembler read about 1.3
characters a byte, not one directive an instruction; any other line as it
is. -/
def packRun (ls : List String) : List String :=
  go ls []
where
  /-- The lines for `ls`, after the bytes `acc` (reversed) of the run of
  encoded lines before it. -/
  go : List String → List (List Nat) → List String
    | [], acc => flush acc
    | l :: ls, acc => match dataBytes? l with
      | some bs => go ls (bs :: acc)
      | none => flush acc ++ l :: go ls []
  flush : List (List Nat) → List String
    | [] => []
    | acc => [".base64 \"" ++ base64 acc.reverse.flatten ++ "\""]

/-- The template line `t` added to the run of lines `run` (reversed): joined
to the line before it if both are lines of the same `joinable` directive, of
one word (`t`) and of fewer than 8 (the line before), as
`<directive> <words>,<word>`, which the assembler reads as the same words in
turn (GNU as, "`.inst`": "one or more expressions"); else a line of its own.
So a run of encoded instructions is a few lines for rustc and the assembler
to read, not one per instruction. -/
def pushLine (t : String) : List String → List String
  | p :: run =>
    match joinable.find? (t.startsWith ·) with
    | some d =>
      let w := (t.drop d.length).toString
      if p.startsWith d && !w.contains ',' && (p.splitOn ",").length < 8 then
        (p ++ "," ++ w) :: run
      else t :: p :: run
    | none => t :: p :: run
  | [] => [t]

/-- The arguments of `naked_asm!` for the template lines `ls`: each run of
lines that are text alone (`lineText`) as one string literal (`literal`) of
those lines separated by newlines, the others as arguments of their own
(`line`).
`naked_asm!` joins its arguments with newlines, so the template is the same
as with one argument per line. A function's template is then a few tokens
for rustc to parse and expand, not one per line.
A comment line (`commentOf`) is not part of the template, nor of the Rust
code: the assembly file has it (`assembly`), so that neither rustc nor the
assembler reads it. Consecutive lines of an encoded instruction's directive
are joined (`pushLine`), and encoded bytes written as `.base64`
(`packRun`). -/
def template (call : String) (ls : List Line) : String :=
  go (ls.filter (commentOf · |>.isNone)) []
where
  /-- The arguments for `ls`, after the run of text lines `run` (reversed). -/
  go : List Line → List String → String
    | [], run => flush run
    | l :: ls, run => match lineText call l with
      | some t => go ls (pushLine t run)
      | none => flush run ++ line call l ++ go ls []
  /-- The run of text lines `run` as one string literal (reversed). -/
  flush : List String → String
    | [] => ""
    | run => "        " ++ literal ("\n".intercalate (packRun run.reverse)) ++ ",\n"

/-- A line of a function's assembly file (`assembly`): a line of text as it is, a
call or the address of a static as `lineText` writes it, the static's name
an operand of `naked_asm!` (`{NAME}`). -/
def assemblyLine (call : String) : Line → String
  | .text l => l
  | .sym s _ n => s ++ "{" ++ n ++ "}"
  | l => (lineText call l).getD ""

/-- Whether a printed line is a directive: the machine code of the
instruction a comment before it is the text of. -/
def isDirective : Line → Bool
  | .text l => l.startsWith "."
  | _ => false

/-- The assembly file of the printed lines `ls` of a function: each line of its
assembly as text (`assemblyLine`), but for an instruction a printer emits as
its machine code, whose comment (`commentOf`) is its text, in place of the
directive after it. -/
def assembly (call : String) (ls : List Line) : List String :=
  go ls false
where
  /-- The assembly file of `ls`, after a comment if `after`, whose directive the
  first line of `ls` then is if it is one. -/
  go : List Line → Bool → List String
    | [], _ => []
    | l :: ls, after =>
      if after && isDirective l then go ls false
      else match commentOf l with
        | some c => (c.drop 3).toString :: go ls true
        | none => assemblyLine call l :: go ls false

/-- `fs` as an English list of code spans: "`a`, `b` and `c`". -/
def codeList : List String → String
  | [] => ""
  | [f] => s!"`{f}`"
  | [f, g] => s!"`{f}` and `{g}`"
  | f :: fs => s!"`{f}`, " ++ codeList fs

/-- `doc`, with the CPU features `fs` added as the last item of its
`# Safety` section (which `checkFeatures` requires it to end with). -/
def featureDoc (doc : String) : List String → String
  | [] => doc
  | fs => doc ++ s!"\n* The CPU must support the {codeList fs} target \
    feature{if fs.length == 1 then "" else "s"}."

/-- The name of the constant of the bit of the CPU feature `f` in a
`Features` (`src/cpu.rs`'s `feature` module): `f` in uppercase, with `_` for
each character that is not a letter or a digit (`sse4.1`'s is `SSE4_1`). -/
def featureConst (f : String) : String :=
  f.toUpper.map fun c => if c.isAlphanum then c else '_'

/-- The constant of the CPU features `fs` that the function `name`
requires: the union of their bits (`featureConst`), of visibility `vis`, its
documentation naming the field `field` that gives them; nothing if there are
none. -/
def featuresConst (name gate : String) (fs : List String) (vis : String := "pub")
    (field : String := "Artifact.features") : String :=
  match fs with
  | [] => ""
  | fs =>
    s!"/// The CPU features `{name}` requires (`{field}`).\n" ++ gate ++
    s!"{vis} const {name.toUpper}_FEATURES: verified_garbage_cpu::Features = \
      verified_garbage_cpu::Features(" ++
    " | ".intercalate (fs.map fun f => s!"verified_garbage_cpu::feature::{featureConst f}") ++ ");\n\n"

/-- The name of the constant of how much of its parameter `param` the
function `name` writes (`Artifact.written`). -/
def writtenName (name param : String) : String := s!"{name.toUpper}_{param.toUpper}_WRITTEN"

/-- The constants of how much of its parameters the function `name` writes
(`Artifact.written`), one per parameter; nothing if there are none. -/
def writtenConsts (name gate : String) (written : List (String × Nat)) : String :=
  String.join (written.map fun (p, n) =>
    s!"/// The bytes of `{p}` that `{name}` may write: it changes no byte of `{p}` at this \
      offset or beyond (`Artifact.written`).\n" ++ gate ++
    s!"pub const {writtenName name p}: usize = {n};\n\n")

/-- The paragraphs documenting how much of its parameters the function `name`
writes (`Artifact.written`). -/
def writtenDoc (name : String) (written : List (String × Nat)) : List String :=
  written.map fun (p, n) =>
    s!"It writes at most the first {n} bytes of `{p}` (`{writtenName name p}`): no byte of \
      `{p}` beyond them changes."

/-- The features that the function `name`, with documentation `doc`, declares
(`declared`) are exactly those its code requires (`required`, with
repetitions); and if there are any, `doc` ends with its `# Safety`
section, for `featureDoc` to add them to. -/
def featureCheck (name doc : String) (required declared : List String) :
    Except String Unit := do
  let required := dedup required
  for f in required do
    unless declared.contains f do
      throw s!"{name} requires the CPU feature {f} but does not declare it"
  for f in declared do
    unless required.contains f do
      throw s!"{name} declares the CPU feature {f}, which none of its code requires"
  unless declared.isEmpty do
    match doc.splitOn "\n# " with
    | [_] => throw s!"{name} needs CPU features but its doc has no `# Safety` section"
    | parts => unless parts.getLast!.startsWith "Safety\n" do
        throw s!"{name} needs CPU features but its doc does not end with its `# Safety` section"

/-- The value of `f` on the code of each call of `calls` (`Code.calls`), in
order, but for a call whose value is that of the first call of the same
function.

`calls` holds a function once per call of it, through every function that
calls it, and its code is usually the same value in memory at each of them:
`withPtrEq` finds that at once, without computing `f` again (which, on the
code of every call, was most of the time of the checks using this). -/
def distinctCalls {I C β : Type} [BEq β] [LawfulBEq β] (f : Code I C → β)
    (calls : List (String × Code I C)) : List β := Id.run do
  -- The first call of each function so far, with its code and its value.
  let mut first : List {p : String × Code I C × β // p.2.2 = f p.2.1} := []
  let mut values : List β := []
  for (n, body) in calls do
    match first.find? (·.1.1 == n) with
    | some ⟨(_, body₀, v₀), h₀⟩ =>
      unless withPtrEq body body₀ (fun _ => f body == v₀) (fun h => by simp_all) do
        values := f body :: values
    | none =>
      let v := f body
      first := ⟨(n, body, v), rfl⟩ :: first
      values := v :: values
  return values.reverse

/-- The features that the instructions of `c` require, but not those of the
functions it calls, each once, in first-seen order after those of `acc`. -/
def ownRequires {I C : Type} (req : I → List String) : List String → Code I C → List String
  | acc, .block is => is.foldl (fun acc i => add acc (req i)) acc
  | acc, .seq a b => ownRequires req (ownRequires req acc a) b
  | acc, .ite _ t e => ownRequires req (ownRequires req acc t) e
  | acc, .loop b _ => ownRequires req acc b
  | acc, .call _ _ => acc
  | acc, .frame i b j => add (ownRequires req (add acc (req i)) b) (req j)
where
  add (acc fs : List String) : List String :=
    fs.foldl (fun acc f => if acc.contains f then acc else acc ++ [f]) acc

/-- The features that the instructions of `c`, and of the functions it
calls, require (`Code.requires`), each once: those of the instructions of
`c` outside its calls (`ownRequires`), then those of the code of each call
(`Code.calls`, which has every call, those in the code of a call too),
skipping a call whose code requires what the first call of the same
function's does (`distinctCalls`). These are the features of
`dedup (c.requires req)`, without building the list with repetitions or
going through the code of a function once per call of it. -/
def requiresDedup {I C : Type} (req : I → List String) (c : Code I C) : List String :=
  (distinctCalls (ownRequires req []) c.calls).foldl ownRequires.add (ownRequires req [] c)

/-- The first `some` of `f` over the instructions of `c`, but not those of
the functions it calls. -/
def ownFirstSome? {I C : Type} (f : I → Option String) : Code I C → Option String
  | .block is => is.findSome? f
  | .seq a b => ownFirstSome? f a <|> ownFirstSome? f b
  | .ite _ t e => ownFirstSome? f t <|> ownFirstSome? f e
  | .loop b _ => ownFirstSome? f b
  | .call _ _ => none
  | .frame i b j => f i <|> ownFirstSome? f b <|> f j

/-- A `some` of `f` over the instructions of `c`, and of the functions it
calls, if there is one: the first of those of `c` outside its calls
(`ownFirstSome?`), or else that of the code of the first call that has one
(`Code.calls`, which has every call, those in the code of a call too). A
call whose value is the first call of the same function's is skipped
(`distinctCalls`): that value is `none`, or the first call's was found. -/
def firstSome? {I C : Type} (f : I → Option String) (c : Code I C) : Option String :=
  ownFirstSome? f c <|> (distinctCalls (ownFirstSome? f) c.calls).findSome? id

/-- `doc` with the paragraphs `notes` inserted before its `# Safety` section. -/
def insertNotes (doc : String) : List String → String
  | [] => doc
  | notes =>
    let sep := "\n\n# Safety\n\n"
    match (doc.splitOn sep).reverse with
    | safety :: rest@(_ :: _) =>
      sep.intercalate rest.reverse ++ String.join (notes.map ("\n\n" ++ ·)) ++ sep ++ safety
    | _ => doc

/-- `doc` with the items `items` first in its `# Safety` section (after
`"\n\n# Safety\n\n"`, which `checkLayout` requires it to have if there are
any), which may have no items of its own. -/
def prependSafety (doc : String) : List String → String
  | [] => doc
  | items =>
    let sep := "\n\n# Safety\n\n"
    match (doc.splitOn sep).reverse with
    | safety :: rest@(_ :: _) =>
      sep.intercalate rest.reverse ++ sep ++ "\n".intercalate (items.map ("* " ++ ·)) ++
        (if safety.isEmpty then "" else "\n" ++ safety)
    | _ => doc

/-- The documentation of `a` as emitted: its `doc`, with what its signature's
contract requires of the memory each buffer is valid for and of where its
buffers are (`Sig.layoutNote` before its `# Safety` section, `Sig.validDoc`
first in it and `Sig.layoutDoc` at the end), and the CPU features it needs
(`featureDoc`). -/
def fullDoc (a : Artifact) : String :=
  let A := a.target.abi
  let items := Sig.layoutDoc A a.sig a.writeArgs a.stack
  featureDoc (prependSafety (insertNotes a.doc
      (Sig.layoutNote A a.sig a.writeArgs ++ writtenDoc a.name a.written))
    (Sig.validDoc A a.sig) ++ String.join (items.map ("\n* " ++ ·))) a.features

/-- If the emitter adds anything to the documentation of `a` from its
signature (`fullDoc`), `doc` ends with its `# Safety` section, which starts
with `"\n\n# Safety\n\n"`; and `doc` does not itself state what memory a
buffer must be valid for, which the emitter generates (`Sig.validDoc`). -/
def checkLayout (a : Artifact) : Except String Unit := do
  if (a.doc.splitOn "valid for").length > 1 then
    throw s!"{a.target.name}: {a.name}'s doc states what memory a buffer must be valid for, \
      which the emitter generates from its signature (`Sig.validDoc`)"
  let A := a.target.abi
  if (Sig.layoutDoc A a.sig a.writeArgs a.stack).isEmpty &&
      (Sig.layoutNote A a.sig a.writeArgs).isEmpty && (Sig.validDoc A a.sig).isEmpty then return
  let ok := match a.doc.splitOn "\n# " with
    | [_] => false
    | parts => parts.getLast!.startsWith "Safety\n" &&
        (a.doc.splitOn "\n\n# Safety\n\n").length > 1
  unless ok do
    throw s!"{a.target.name}: {a.name} has buffers but its doc does not end with its \
      `# Safety` section"

/-- The attribute compiling an item only under every predicate of `cs`
(`Printer.featureCfg` of the features a function needs); nothing if there
are none. -/
def cfgGate : List String → String
  | [] => ""
  | [c] => s!"#[cfg({c})]\n"
  | cs => s!"#[cfg(all({", ".intercalate cs}))]\n"

/-- Assembler directives that open, and close, the text of every function
of the target named `t`: the first and last lines of its template, so that
they apply to all of it and to nothing after it.

On RISC-V (`riscv64`), `.option push` and `.option arch, +m, +c`, then
`.option pop`, enable the M and C extensions for the function alone. The model's
multiplies, `mul` and `mulhu`, are M's (`TCB/RISCV64/Isa.lean`), and the
target compiles them only where Rust enables it (`target_feature = "m"`,
`TCB/RISCV64/Target.lean`'s `rustCfg`), but rustc does not always tell the
assembler: in a release build with several codegen units, LLVM assembles
some units' module-level assembly (where naked functions go) without M,
rejecting `mul` as needing `Zmmul`. The RISC-V Assembly Programmer's Manual
(riscv-non-isa/riscv-asm-manual), ".option": `arch` enables "specific ISA
extensions for the following code regions, but without changing the arch
attribute and `EF_RISCV_RVC` in the ELF flags", and `push`/`pop` "Push/pop
current options to/from the options stack", the manual's recommended way to
bound an `.option arch, +` ("We recommend `.option arch, +` and
`.option arch, -` are used with `.option push`/`.option pop`"). So the
options after the function are what they were before it. The directives
emit no bytes and change no instruction: the assembler accepts the `mul` and
`mulhu` that the model describes, the only instructions of M the printer
emits. `+c` likewise enables the C extension, whose compressed encodings
the printer emits as `.insn 2, …` (`TCB/RISCV64/Encode.lean`'s `compress`),
which the assembler accepts only with it, and which the target compiles only
where Rust enables it (`target_feature = "c"`). (They are keyed on the target here, rather than being a field of its
`Printer`, so that adding them did not change what every proof imports.) -/
def funcOptions : String → List String × List String
  | "riscv64" => ([".option push", ".option arch, +m, +c"], [".option pop"])
  | _ => ([], [])

/-- The `cfg` attribute of `a`'s function and constants (`cfgGate` of
`Printer.featureCfg` of its features). -/
def gateOf (a : Artifact) : String := cfgGate (a.features.filterMap a.target.printer.featureCfg)

/-- The lines of a function on the target `T` whose code needs the CPU
features `features`, given its printed code `lines`: the target's opening
`funcOptions`, the directives enabling its features, `lines`, the directives
disabling them, the printer's `funcAlign`, and the closing `funcOptions`. -/
def bodyLines (T : Target) (features : List String) (lines : List Line) : List Line :=
  let P := T.printer
  let (start, stop) := funcOptions T.name
  start.map .text ++ (features.flatMap P.enableFeature).map .text ++ lines ++
    (features.flatMap P.disableFeature).map .text ++ P.funcAlign.map .text ++ stop.map .text

/-- The lines of `a`'s function, given its printed code `lines` (`bodyLines`
of its features). -/
def bodyOf (a : Artifact) (lines : List Line) : List Line :=
  bodyLines a.target a.features lines

/-- The `naked_asm!` of a function of the target `T` whose lines are `body`:
its template, then the `sym` operand of each function it calls, at the path
`<root>::<module>::<name>` (`moduleOf` gives the module), and of each table
of constants it names, at `<root>::consts::<name>`; `root` is the path of the
crate's root from the function's file. -/
def asmOf (T : Target) (body : List Line) (moduleOf : String → String) (root : String) :
    String :=
  let callees := dedup (body.filterMap fun | .call n => some n | _ => none)
  let syms := dedup (body.filterMap fun | .sym _ _ n => some n | _ => none)
  "    core::arch::naked_asm!(\n" ++
  template T.printer.call body ++
  String.join (callees.map fun n => s!"        {n} = sym {root}::{moduleOf n}::{n},\n") ++
  String.join (syms.map fun n => s!"        {n} = sym {root}::consts::{n},\n") ++
  "    )\n"

/-- The text of `a`'s function after its name, given `a`'s printed code
`lines`: its signature and its body, the `naked_asm!` of its code
(`function`, `asmOf`). -/
def codeOf (a : Artifact) (lines : List Line) (moduleOf : String → String) : String :=
  s!"{a.sig.rust} " ++ "{\n" ++ asmOf a.target (bodyOf a lines) moduleOf "super" ++ "}\n"

/-- Clippy's `missing_safety_doc`, which asks every `pub unsafe fn` for a
`# Safety` section, allowed for a function whose documentation `doc` has
none (as one with no buffers and no requirements, `vg_selftest_add`, does
not: its contract asks nothing of the caller); nothing for any other. -/
def safetyAllow (doc : String) : String :=
  if (doc.splitOn "# Safety\n").length > 1 then "" else "#[allow(clippy::missing_safety_doc)]\n"

/-- One artifact as a Rust naked function; `moduleOf` gives the module of
each function it calls. The printer's `funcAlign` comes after the return
(`Printer.function`) and any directives that follow it, and only the
target's closing `funcOptions` after that, which close what its opening
ones, the first lines, opened. -/
def function (a : Artifact) (moduleOf : String → String) : String :=
  functionOf a (a.target.printer.function a.code) moduleOf
where
  /-- `function a`, given `a`'s printed code `lines`
  (`a.target.printer.function a.code`). -/
  functionOf (a : Artifact) (lines : List Line) (moduleOf : String → String) : String :=
  withCode a (codeOf a lines moduleOf)
  /-- `function a`, given the text of its function after its name, `code`
  (`codeOf`). -/
  withCode (a : Artifact) (code : String) : String :=
  let gate := gateOf a
  let doc := fullDoc a
  featuresConst a.name gate a.features ++
  writtenConsts a.name gate a.written ++
  docComment "" doc ++
  gate ++
  safetyAllow doc ++
  "#[unsafe(naked)]\n" ++
  s!"pub unsafe extern \"{a.target.rustAbi}\" fn {a.name}" ++ code

/-- What makes two functions of a module the same function: their `cfg`
attribute, calling convention, signature and body (`gateOf`, `codeOf`),
everything of `function`'s text but the name, the documentation and the
constants. -/
def sameKey (a : Artifact) (code : String) : String :=
  gateOf a ++ "\n" ++ a.target.rustAbi ++ "\n" ++ code

/-- `a`'s function as another name of the function `canon` of the same
module, whose text but for its name, documentation and constants is the
text `a`'s would have (`sameKey`): a `use` of it as `a`'s name, under `a`'s
`cfg` attribute, with `a`'s documentation (saying so) and constants. -/
def alias (a : Artifact) (canon : String) : String :=
  let gate := gateOf a
  let note := s!"The machine code of this function is that of `{canon}`, which is emitted once \
    and named both ways: the two are the same function."
  let doc := fullDoc a
  let doc := if (doc.splitOn "\n\n# Safety\n\n").length > 1 then insertNotes doc [note]
    else doc ++ "\n\n" ++ note
  featuresConst a.name gate a.features ++
  writtenConsts a.name gate a.written ++
  docComment "" doc ++
  gate ++
  "#[allow(unused_imports)]\n" ++
  s!"pub use self::{canon} as {a.name};\n"

/-- The tables of constants of `a`: those its contract gives it
(`Artifact.consts`) and those its instructions carry (`Printer.codeTables`,
x86-64's `aluTbl`). -/
def tablesOf (a : Artifact) : List (String × List (BitVec 64)) :=
  a.consts ++ a.target.printer.codeTables a.code

/-- The distinct values of `f` over `as`, in first-seen order. -/
def distinct (as : List Artifact) (f : Artifact → String) : List String :=
  dedup (as.map f)

/-- The first of `calls` (`Code.calls`: the name of each function called and
the code the model runs for it) that is not of a function `printed` gives the
printed code of (`some (n, false)`), or whose code `P` does not print as that
(`some (n, true)`); `none` if every call is of the code it runs.

A function can be called hundreds of times in one artifact's `calls`, so
only the first call of each name is printed and compared with `printed`;
every later one is compared with the first one's code, by equal printed
code, which `withPtrEq` returns at once if the two are the same value in
memory, as they usually are. -/
def badCall {M : ISA} (P : Printer M) (printed : String → Option (List Line))
    (calls : List (String × Prog M)) : Option (String × Bool) := Id.run do
  -- The first call of each function checked so far, with its code.
  let mut first : List (String × Prog M) := []
  for (n, body) in calls do
    match first.find? (·.1 == n) with
    | some (_, body₀) =>
      unless withPtrEq body body₀ (fun _ => P.function body == P.function body₀)
          (fun h => by simp [h]) do
        return some (n, true)
    | none =>
      match printed n with
      | none => return some (n, false)
      | some lines =>
        unless P.function body == lines do return some (n, true)
        first := (n, body) :: first
  return none

/-- An artifact with what the checks read of it more than once, each computed
once: its printed code (`Printer.function`, which a call of it is checked
against in every function that calls it, `checkCalls`) and its tables of
constants (`tablesOf`, which every artifact of the target is checked
against, `checkConsts`). -/
structure Prepared where
  art : Artifact
  lines : List Line
  tables : List (String × List (BitVec 64))
  lines_eq : lines = art.target.printer.function art.code
  tables_eq : tables = tablesOf art

def Prepared.of (a : Artifact) : Prepared := ⟨a, _, _, rfl, rfl⟩

/-- The functions of a module, the artifacts of `ps` in order: each with the
text of its function after its name (`codeOf`) and the name of the function
it is emitted as: of those with the same `sameKey`, the one with the
shortest name (the first of them, if several are as short). -/
def moduleItems (moduleOf : Artifact → String → String) (ps : List Prepared) :
    List (Prepared × String × String) :=
  let items := ps.map fun p =>
    let code := codeOf p.art p.lines (moduleOf p.art)
    let key := sameKey p.art code
    (p, code, hash key, key)
  -- The function each key's artifacts are emitted as.
  let canon (h : UInt64) (key : String) : String :=
    (items.filter fun (_, _, h', k) => h' == h && k == key).foldl (init := none)
      (fun best (p, _) => match best with
        | some b => if p.art.name.length < b.length then some p.art.name else some b
        | none => some p.art.name) |>.getD ""
  items.map fun (p, code, h, key) => (p, code, canon h key)

/-- The text of the functions of a module (`moduleItems`): each as `function`
writes it, if it is emitted as itself, else the `alias` of the function it
is emitted as. -/
def moduleText (items : List (Prepared × String × String)) : String :=
  String.join (items.map fun (p, code, c) =>
    "\n" ++ if c == p.art.name then function.withCode p.art code else alias p.art c)

/-- The assembly file of the functions of a module (`moduleItems`), which the
crate does not compile: each function emitted as itself as its name, then
its lines (`assembly`), each indented but its labels; each other as a line
naming the function it is. -/
def moduleAssembly (items : List (Prepared × String × String)) : String :=
  String.join (items.map fun (p, _, c) =>
    if c == p.art.name then functionAssembly p.art.target p.art.name (bodyOf p.art p.lines)
    else s!"\n// {p.art.name}: the function `{c}`\n")
where
  /-- The function `name` of the target `T`, whose lines are `body`, in an
  assembly file: its name, then its lines (`assembly`), each indented but its
  labels. -/
  functionAssembly (T : Target) (name : String) (body : List Line) : String :=
    s!"\n{name}:\n" ++ String.join ((assembly T.printer.call body).map fun l =>
      if l.endsWith ":" && !l.contains ' ' then l ++ "\n" else "\t" ++ l ++ "\n")

/-- `p`'s artifact declares exactly the CPU features its code requires
(`featureCheck`). -/
def checkFeatures (p : Prepared) : Except String Unit :=
  let a := p.art
  featureCheck s!"{a.target.name}: {a.name}" a.doc (requiresDedup a.target.isa.requires a.code)
    a.features

/-- The target's printer can encode every instruction of the code of `p`'s
artifact, and of the functions it calls, as the model describes it
(`Printer.unencodable`). -/
def checkEncodable (p : Prepared) : Except String Unit :=
  let a := p.art
  match firstSome? a.target.printer.unencodable a.code with
  | none => pure ()
  | some e => throw s!"{a.target.name}: {a.name}: {e}"

/-- The artifact carries the contract of the `Api` it is made from
(`Artifact.contracts`), which it is proven against (`Artifact.ofApi`): so its
name, signature and documentation are those `Spec/` gives that contract. -/
def checkApi (a : Artifact) : Except String Unit :=
  unless a.contracts.isSome do
    throw s!"{a.target.name}: {a.name} is not made from an `Api` with a contract \
      (`Api.contracts`)"

/-- Each bound of `a.written` names a writable array parameter of its
signature, no parameter twice, and is at most the parameter's size in bytes:
so the constant `writtenConsts` exports for it is a bound on the bytes of
that buffer the function may change. -/
def checkWritten (a : Artifact) : Except String Unit := do
  let names := a.written.map (·.1)
  for (p, n) in a.written do
    unless (names.filter (· == p)).length == 1 do
      throw s!"{a.target.name}: {a.name} bounds what it writes of `{p}` more than once"
    match a.sig.params.lookup p with
    | some (.array true e k) =>
      unless n ≤ k * e.size do
        throw s!"{a.target.name}: {a.name} bounds what it writes of `{p}` by {n} bytes, \
          more than its {k * e.size}"
    | some _ =>
      throw s!"{a.target.name}: {a.name} bounds what it writes of `{p}`, which is not a \
        writable array"
    | none => throw s!"{a.target.name}: {a.name} bounds what it writes of `{p}`, which is not \
        one of its parameters"

/-- No two artifacts of a target have the same name. -/
def checkUnique (as : List Artifact) : Except String Unit :=
  as.forM fun a =>
    unless (as.filter fun b => b.target.name == a.target.name && b.name == a.name).length == 1 do
      throw s!"{a.target.name}: {a.name} is defined more than once"

/-- A table's name is a Rust constant's starting with `VG_`: `VG_`, then
uppercase ASCII letters, digits and underscores; so its lowercase, the
module of its file, is never a Rust keyword or `mod`. -/
def tableName (n : String) : Bool :=
  match n.toList with
  | 'V' :: 'G' :: '_' :: c :: cs => (c :: cs).all fun c => ('A' ≤ c && c ≤ 'Z') || c.isDigit || c == '_'
  | _ => false

/-- Tables of the same name in `cs` and `ds` have the same words.

Every artifact of a target is checked against every other (`checkConsts`),
and a table of hundreds of kilobytes is usually the same value in memory in
each artifact that has it (`files` shares them): `withPtrEq` finds that at
once, without comparing its words again. -/
def consistent (cs ds : List (String × List (BitVec 64))) : Bool :=
  cs.all fun (n, ws) => ds.all fun (m, vs) =>
    m != n || withPtrEq vs ws (fun _ => vs == ws) (fun h => by simp [h])

/-- The tables of constants of `a` (`Artifact.consts`) have distinct names,
and so do those its instructions carry but for repeats of the same table;
every name is a Rust constant's, none is named `consts` or the module of an
artifact; every artifact of the target with a table of one of these names,
given or carried, gives the same words; its code names only these tables;
and its target's code can name a `static` (`Abi.sym`), if it has any. Of
`p`'s artifact, checked against the artifacts of `ps`. -/
def checkConsts (ps : List Prepared) (p : Prepared) : Except String Unit := do
  let a := p.art
  let ts := p.tables
  unless ts.isEmpty || a.target.abi.sym.isSome do
    throw s!"{a.target.name}: {a.name} reads tables of constants, which its target's code cannot name"
  let names := a.consts.map (·.1)
  unless (dedup names).length == names.length do
    throw s!"{a.target.name}: {a.name} has two tables of constants of the same name"
  for (n, _) in ts do
    unless tableName n do
      throw s!"{a.target.name}: {a.name}'s table of constants {n} is not named as a Rust constant starting with `VG_`"
  unless consistent ts ts do
    throw s!"{a.target.name}: {a.name} gives a table of constants two lists of words"
  for q in ps do
    unless q.art.target.name != a.target.name || consistent ts q.tables do
      throw s!"{a.target.name}: {a.name} and {q.art.name} give a table of constants different words"
  if (ps.any fun q => q.art.target.name == a.target.name && q.art.module == "consts") then
    throw s!"{a.target.name}: an artifact's module is `consts`, the module of the tables of constants"
  let used := p.lines.filterMap fun | .sym _ _ n => some n | _ => none
  for n in used do
    unless (ts.map (·.1)).contains n do
      throw s!"{a.target.name}: {a.name} names the table {n}, which it does not have \
        (`Artifact.consts`) or carry"

/-! ## Internal functions -/

/-- An *internal function* of a target: a function that the code of an
artifact calls (`Code.call name body`), or the code of a function it calls,
that is not an artifact of the target. It needs no `Api`, contract or proof
of its own: it is only ever run by a call in the code of an artifact (it is
`pub(crate)` in a module of its own of the target's crate, which has no other
code, and nothing outside the crate can name it), for which the model runs
its code, so the artifact's proof covers it, as it covers the code of every
function the artifact calls. `files` checks that every call of `name` runs the
code the function is emitted with (`checkCalls`).

Its fields are what the emitter reads of it: its target, name and code, its
printed code (`Printer.function`), the CPU features its code, and that of
the functions it calls, requires (`requiresDedup`), which its function's
body enables and its `cfg` attribute follows, as an artifact's
(`bodyLines`, `gateOf`); the tables of constants its instructions carry
(`Printer.codeTables`), and the tables its printed code names. -/
structure Internal where
  target : Target
  name : String
  /-- The module whose file declares the internal function's (`internalOwner`). -/
  owner : String
  code : Prog target.isa
  lines : List Line
  features : List String
  tables : List (String × List (BitVec 64))
  syms : List String
  lines_eq : lines = target.printer.function code
  features_eq : features = requiresDedup target.isa.requires code
  tables_eq : tables = target.printer.codeTables code
  syms_eq : syms = dedup (lines.filterMap fun | .sym _ _ n => some n | _ => none)

/-- The internal function `name` of the target `T`, whose code is `code`, declared
by the module `owner`. -/
def Internal.of (T : Target) (name owner : String) (code : Prog T.isa) : Internal :=
  ⟨T, name, owner, code, _, _, _, _, rfl, rfl, rfl, rfl⟩

/-- The module whose file declares the internal function `name`: of the
modules `modules` of its target, the longest whose name `name` starts with,
after `vg_` and before `_` (`sha256` for `vg_sha256_compress`), or else the
first, in order of their names, of the modules `callers` of the artifacts
that call it. It only
decides where the function's module is declared, so that a change to the
internal functions of one algorithm changes the files of that algorithm's
modules rather than a list every algorithm's changes edit; what the function
is does not depend on it. -/
def internalOwner (name : String) (modules callers : List String) : String :=
  let sorted := callers.mergeSort (· ≤ ·)
  let named := modules.filter fun m => name.startsWith s!"vg_{m}_"
  match named.foldl (init := none) fun best m => match best with
    | some b => if m.length > b.length then some m else some b
    | none => some m with
  | some m => m
  | none => sorted.headD ""

/-- The names of the functions that `calls` (`Code.calls`) calls, each once,
in first-seen order: its first call of each. -/
def firstCalls {I C : Type} (calls : List (String × Code I C)) : List (String × Code I C) :=
  Id.run do
  let mut names : List String := []
  let mut out : List (String × Code I C) := []
  for (n, body) in calls do
    unless names.contains n do
      names := n :: names
      out := (n, body) :: out
  return out.reverse

/-- The internal functions of the artifacts of `ps` (`Internal`): of each
target, every function the code of one of its artifacts calls (`Code.calls`,
those in the code of the functions it calls too) that is not an artifact of
the target, once, with the code of the first call of it, in order of the
artifacts and of their calls. `checkCalls` checks that every other call of
it is of that code. -/
def internalsOf (ps : List Prepared) : List Internal := Id.run do
  -- Each internal function found so far: its target and name, the code of its
  -- first call, and the modules of the artifacts that call it.
  let mut found : List (String × String × Σ T : Target, Prog T.isa) := []
  let mut callers : List ((String × String) × List String) := []
  for p in ps do
    let a := p.art
    let t := a.target.name
    for (n, body) in firstCalls a.code.calls do
      if ps.any fun q => q.art.target.name == t && q.art.name == n then continue
      unless found.any (fun (t', n', _) => t' == t && n' == n) do
        found := (t, n, ⟨a.target, body⟩) :: found
      callers := match callers.find? (·.1 == (t, n)) with
        | some _ => callers.map fun (k, ms) =>
            if k == (t, n) && !ms.contains a.module then (k, a.module :: ms) else (k, ms)
        | none => ((t, n), [a.module]) :: callers
  return found.reverse.map fun (t, n, ⟨T, body⟩) =>
    let modules := Rust.dedup ((ps.filter (·.art.target.name == t)).map (·.art.module))
    Internal.of T n (internalOwner n modules (((callers.find? (·.1 == (t, n))).map (·.2)).getD [])) body

/-- The internal function of `hs` that a call of `name` in an artifact of the
target `t` calls, if there is one. -/
def internal? (hs : List Internal) (t name : String) : Option Internal :=
  hs.find? fun h => h.target.name == t && h.name == name

/-- An internal function's name is a Rust function's starting with `vg_`:
`vg_`, then lowercase ASCII letters, digits and underscores; so it is never
a Rust keyword, and is the name of its module (`<owner>::<name>`) too. Its
code, and so its name, is not reviewed (`Impl/`), and the emitter writes the
name into Rust code: nothing else may be written there. -/
def internalName (n : String) : Bool :=
  match n.toList with
  | 'v' :: 'g' :: '_' :: c :: cs => (c :: cs).all fun c =>
      ('a' ≤ c && c ≤ 'z') || c.isDigit || c == '_'
  | _ => false

/-- The internal function `h` (of `hs`, of the artifacts of `ps`) is named as
`internalName` requires; the tables of constants its instructions carry are
named as `tableName` requires, and every artifact and every other internal
function of its target with a table of one of their names gives the same
words (`consistent`); and its target's code can name a `static`
(`Abi.sym`), if it names any. -/
def checkInternal (ps : List Prepared) (hs : List Internal) (h : Internal) :
    Except String Unit := do
  let t := h.target.name
  unless internalName h.name do
    throw s!"{t}: the internal function {h.name} is not named as a Rust function starting \
      with `vg_` (lowercase letters, digits and underscores)"
  unless h.syms.isEmpty || h.target.abi.sym.isSome do
    throw s!"{t}: the internal function {h.name} reads tables of constants, which its target's \
      code cannot name"
  for (n, _) in h.tables do
    unless tableName n do
      throw s!"{t}: the internal function {h.name}'s table of constants {n} is not named as a \
        Rust constant starting with `VG_`"
  unless consistent h.tables h.tables do
    throw s!"{t}: the internal function {h.name} gives a table of constants two lists of words"
  for q in ps do
    unless q.art.target.name != t || consistent h.tables q.tables do
      throw s!"{t}: the internal function {h.name} and {q.art.name} give a table of constants \
        different words"
  for g in hs do
    unless g.target.name != t || consistent h.tables g.tables do
      throw s!"{t}: the internal functions {h.name} and {g.name} give a table of constants \
        different words"

/-- Every table of constants that an internal function the code of `p`'s
artifact calls names is one of the artifact's (`Prepared.tables`: those its
contract gives it, `Artifact.consts`, and those its instructions carry) or
one the internal function's instructions carry: the artifact's contract
says where the memory holds the tables it gives (`Abi.withConsts`), which is
what its proof, which runs the internal function's code, assumes of them,
and every artifact with a table of a name gives the same words
(`checkConsts`). No artifact's module is `internal`, the directory of the
internal functions' files. -/
def checkInternalTables (hs : List Internal) (p : Prepared) : Except String Unit := do
  let a := p.art
  let t := a.target.name
  if a.module == "internal" then
    throw s!"{t}: {a.name}'s module is `internal`, the directory of the internal functions' files"
  let own := p.tables.map (·.1)
  for (n, _) in firstCalls a.code.calls do
    let some h := internal? hs t n | continue
    for s in h.syms do
      unless own.contains s || (h.tables.map (·.1)).contains s do
        throw s!"{t}: {a.name} calls the internal function {n}, which names the table {s}, \
          which {a.name} does not have (`Artifact.consts`) or carry"

/-- Every call in the code of `p`'s artifact, and in the code of the functions
it calls, is of an artifact of `ps` of the same target, or of an internal
function of `hs` (`internalsOf`), whose printed code is that of the called
code (`badCall`). -/
def checkCalls (ps : List Prepared) (hs : List Internal) (p : Prepared) : Except String Unit :=
  let a := p.art
  let t := a.target.name
  let printed (n : String) : Option (List Line) :=
    match ps.find? fun q => q.art.target.name == t && q.art.name == n with
    | some q => some q.lines
    | none => (internal? hs t n).map (·.lines)
  match badCall a.target.printer printed a.code.calls with
  | none => pure ()
  | some (n, false) =>
    throw s!"{t}: {a.name} calls {n}, which is neither an artifact nor an internal function"
  | some (n, true) =>
    throw s!"{t}: {a.name} calls {n}, whose code is not what the call runs"

/-- The macros that write the page of a static's address and its offset in
the page in the syntax of the object format (`Line.sym`): Mach-O's on
Apple's platforms, ELF's (which COFF's is too) elsewhere. -/
def symMacros : String :=
  "\n/// The page of a `static`'s address, in the assembler syntax of the object format.\n" ++
  "#[cfg(target_vendor = \"apple\")]\n#[allow(unused_macros)]\n" ++
  "macro_rules! vg_sym_page {\n    ($s:literal) => {\n        concat!($s, \"@PAGE\")\n    };\n}\n" ++
  "#[cfg(not(target_vendor = \"apple\"))]\n#[allow(unused_macros)]\n" ++
  "macro_rules! vg_sym_page {\n    ($s:literal) => {\n        $s\n    };\n}\n" ++
  "\n/// The offset of a `static`'s address in its page, in the assembler syntax of the object format.\n" ++
  "#[cfg(target_vendor = \"apple\")]\n#[allow(unused_macros)]\n" ++
  "macro_rules! vg_sym_pageoff {\n    ($s:literal) => {\n        concat!($s, \"@PAGEOFF\")\n    };\n}\n" ++
  "#[cfg(not(target_vendor = \"apple\"))]\n#[allow(unused_macros)]\n" ++
  "macro_rules! vg_sym_pageoff {\n    ($s:literal) => {\n        concat!(\":lo12:\", $s)\n    };\n}\n"

/-- The tables of constants of the artifacts `arts`, and those the
instructions of the internal functions `hs` carry (`Internal.tables`), by
name, each once. -/
def tables (arts : List Artifact) (hs : List Internal := []) : List (String × List (BitVec 64)) :=
  let all := arts.flatMap tablesOf ++ hs.flatMap (·.tables)
  ((dedup (all.map (·.1))).mergeSort (· ≤ ·)).filterMap fun n => all.find? (·.1 == n)

/-- The byte `b < 256` as an escape of a Rust byte string literal, `\xHH`. -/
def byteEscape (b : Nat) : String :=
  let hex (d : Nat) : Char := Nat.digitChar d
  "\\x" ++ (String.singleton (hex (b / 16))) ++ (String.singleton (hex (b % 16)))

/-- The word `w` as the escapes of its 8 bytes, least significant first. -/
def wordBytes (w : BitVec 64) : String :=
  String.join ((List.range 8).map fun i => byteEscape (w.toNat / 2 ^ (8 * i) % 256))

/-- The module of a table of constants, its name in lowercase. -/
def tableModule (n : String) : String := n.toLower

/-- The file of the table `n`: its words, as the memory holds them
(`Abi.constsHeld`: little-endian), in a byte string literal, one word per
line (each line of the literal ends with `\`, which continues it on the next
line without the newline and the indentation). rustc evaluates a byte string
literal at once, faster than an array of a word per element. -/
def tableFile (t n : String) (ws : List (BitVec 64)) : String :=
  header ++ s!"//! The table of constants `{n}` of the verified functions for `{t}` (`Artifact.consts`).\n" ++
  "#![allow(dead_code)]\n" ++
  "\nuse super::Table;\n" ++
  s!"\n/// The table of constants `{n}` (`Artifact.consts`).\n" ++
  s!"pub static {n}: Table<{8 * ws.length}> = Table(*b\"\\\n" ++
  String.join (ws.map fun w => "    " ++ wordBytes w ++ "\\\n") ++ "\");\n"

/-- The module of a target's tables of constants, `consts/mod.rs`: `Table`,
and each table's module, whose `static` it re-exports. -/
def tablesMod (t : String) (ts : List (String × List (BitVec 64))) : String :=
  header ++ s!"//! The tables of constants of the verified functions for `{t}` (`Artifact.consts`).\n" ++
  "#![allow(dead_code, unused_imports)]\n" ++
  "\n/// A table of constants, aligned to a cache line.\n" ++
  "#[repr(C, align(64))]\npub struct Table<const N: usize>(pub [u8; N]);\n" ++
  String.join (ts.map fun (n, _) =>
    s!"\n#[rustfmt::skip]\nmod {tableModule n};\npub use {tableModule n}::{n};\n")

/-- `mod` declarations for generated child modules (never reformatted by rustfmt). -/
def modDecls (ms : List String) (cfg : String → Option String) : String :=
  String.join (ms.map fun m =>
    let c := match cfg m with
      | some c => s!"#[cfg({c})]\n"
      | none => ""
    s!"\n{c}#[rustfmt::skip]\npub mod {m};\n")

/-- How many tasks `files` checks the artifacts on: the CPUs of CI's
runners. The checks, and `render`, are pure functions of the artifacts, so
running them on tasks (`Task.spawn`) changes how long they take, never what
they return. -/
def tasks : Nat := 4

/-- `as.forM check` on `tasks` tasks, each checking every `tasks`-th
artifact: the error of the first artifact of `as` that fails, as `forM`
gives it, or none. -/
def forMPar {α : Type u} (as : List α) (check : α → Except String Unit) : Except String Unit :=
  let indexed := as.zipIdx
  let parts := (List.range tasks).map fun j => Task.spawn fun _ =>
    (indexed.filter (·.2 % tasks == j)).findSome? fun (a, i) =>
      match check a with
      | .error e => some (i, e)
      | .ok _ => none
  let first := (parts.filterMap Task.get).foldl (init := none) fun
    | some m, e => if e.1 < m.1 then some e else some m
    | none, e => some e
  match first with
  | some (_, e) => throw e
  | none => pure ()

/-- `as.map Prepared.of`, on `tasks` tasks, each preparing a run of consecutive
artifacts. -/
def prepareAll (as : List Artifact) : List Prepared :=
  let size := (as.length + tasks - 1) / tasks
  let parts := (List.range tasks).map fun j =>
    Task.spawn fun _ => ((as.drop (j * size)).take size).map Prepared.of
  (parts.map Task.get).flatten

/-- The targets of the artifacts `as`, each once, with its Rust `cfg`
(`Target.rustCfg`), in first-seen order. -/
def targetsOf (as : List Artifact) : List (String × String) :=
  (distinct as (·.target.name)).map fun t =>
    (t, ((as.find? (·.target.name == t)).map (·.target.rustCfg)).getD "")

/-- The directory of the target `t`'s crate, under `crates/`: its name. -/
def crateDir (t : String) : String := s!"verified-garbage-asm-{t}"

/-- The directory of the target `t`'s generated files, under `crates/`: its
crate's (`crateDir`) `src/`, which the crate compiles. -/
def codeDir (t : String) : String := crateDir t ++ "/src"

/-- The directories of the target `t`'s generated files, under `crates/`: its
code (`codeDir`) and its assembly files (`assemblyFile`). -/
def generatedDirs (t : String) : List String := [codeDir t, crateDir t ++ "/assembly"]

/-- The assembly file of a module `m` (`moduleAssembly`), in its crate: `assembly/<m>.s`. -/
def assemblyFile (m : String) : String := s!"assembly/{m}.s"

/-- The first lines of the assembly file of the module `m` of the target `t`. -/
def assemblyHeader (t m : String) : String :=
  s!"// The functions of `src/{m}.rs` of `{crateDir t}`, as text: generated from\n" ++
  "// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.\n" ++
  "// Each instruction the printer encodes is here as its text, and in\n" ++
  "// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`\n" ++
  "// gives.\n"

/-- The root module of the target `t`'s crate, `lib.rs` (in its `codeDir`): the macros its
modules use (`symMacros`) and a `mod`
declaration of each of its modules `mods`, each compiled only under the
target's Rust `cfg` `cfg` (so that a build for any other target, of every
crate of the workspace, compiles none of them). The `cfg` is on the
declarations, rather than the crate (`#![cfg]`), as `#[rustfmt::skip]`
keeps rustfmt from rewriting their attributes, which the crate's cannot
be. -/
def targetRoot (t cfg : String) (mods : List String) : String :=
  header ++
  s!"//! Verified functions for `{t}`: the crate `{crateDir t}`.\n" ++
  "//!\n" ++
  "//! Every function in these modules is the direct rendering of an `Artifact`\n" ++
  "//! whose machine code has been proven correct, memory safe and constant time\n" ++
  "//! against its contract. See `lean/README.md`.\n" ++
  "\n#![no_std]\n" ++
  symMacros ++
  modDecls mods (fun _ => some cfg)

/-- The module of the internal function `h` (`Internal`), under the crate's
root: `<owner>::<name>`, the file `internal/<name>.rs` of its `codeDir`, which
the file of the module `owner` declares (`internalDecls`). -/
def internalModule (h : Internal) : String := s!"{h.owner}::{h.name}"

/-- The declarations of the modules of the internal functions `hs` in the file
of the module that declares each (`Internal.owner`): each the file
`internal/<name>.rs` (a `path` relative to the directory of that file,
`codeDir`), `pub(crate)`, so that the generated code of the crate can name
them and nothing outside it can. -/
def internalDecls (hs : List Internal) : String :=
  String.join (hs.map fun h =>
    s!"\n#[rustfmt::skip]\n#[path = \"internal/{h.name}.rs\"]\npub(crate) mod {h.name};\n")

/-- The documentation of every internal function. -/
def internalDoc : String :=
  "An internal function of the verified functions of this crate (`VG.Rust.Internal`): code \
  that they call, which is not itself an artifact. It has no contract of its own: the proof of \
  each function that calls it covers its code, which the model runs for the call \
  (`Code.call`), and the emitter checks that every call of it is of this code.\n\n\
  # Safety\n\n\
  * Only the verified functions of this crate may call it, as their code does: it is not \
  visible outside the crate."

/-- The file of the internal function `h`, `internal/<name>.rs`: the constant of
the CPU features its code needs (`featuresConst`, for the checks of the
generated code, `ci/check_variants.py`), and the function, a naked function
of no parameters, `pub(crate)`, with the `cfg` attribute of those features
(`Printer.featureCfg`), whose body enables them (`bodyLines`); `moduleOf` gives the module of each function it calls,
from the crate's root (`internalModule` for an internal function). -/
def internalFile (h : Internal) (moduleOf : String → String) : String :=
  let T := h.target
  let gate := cfgGate (h.features.filterMap T.printer.featureCfg)
  header ++ s!"//! The internal function `{h.name}` for `{T.name}`, whose text is in\n" ++
  s!"//! `{assemblyFile s!"internal/{h.name}"}`.\n" ++
  "#![allow(dead_code)]\n\n" ++
  featuresConst h.name gate h.features "pub(crate)" "VG.Rust.Internal.features" ++
  docComment "" internalDoc ++
  gate ++
  "#[unsafe(naked)]\n" ++
  s!"pub(crate) unsafe extern \"{T.rustAbi}\" fn {h.name}() " ++ "{\n" ++
  asmOf T (bodyLines T h.features h.lines) moduleOf "crate" ++ "}\n"

/-- The generated files of the artifacts of `ps`, given the module of each
function each artifact calls; each artifact's code as `ps` printed it
(`Prepared.lines`). -/
def render (ps : List Prepared) (hs : List Internal) (moduleOf : String → String → String) :
    List (String × String) :=
  let as := ps.map (·.art)
  let targets := distinct as (·.target.name)
  let perTarget (t : String) : List (String × String) :=
    let arts := ps.filter (·.art.target.name == t)
    -- In order of their names, wherever their artifacts or calls come in the lists.
    let hs := (hs.filter (·.target.name == t)).mergeSort (·.name ≤ ·.name)
    let modules := (distinct (arts.map (·.art)) (·.module)).mergeSort (· ≤ ·)
    let ts := tables (arts.map (·.art)) hs
    let mods := if ts.isEmpty then modules else (modules ++ ["consts"]).mergeSort (· ≤ ·)
    let cfg := ((targetsOf (arts.map (·.art))).map (·.2)).headD ""
    let src := codeDir t
    (s!"{src}/lib.rs", targetRoot t cfg mods) ::
    (if ts.isEmpty then [] else
      (s!"{src}/consts/mod.rs", tablesMod t ts) ::
        ts.map fun (n, ws) => (s!"{src}/consts/{tableModule n}.rs", tableFile t n ws)) ++
    (hs.map fun h => Task.spawn fun _ =>
      let m := s!"internal/{h.name}"
      [(s!"{src}/{m}.rs", internalFile h (moduleOf t)),
       (s!"{crateDir t}/{assemblyFile m}", assemblyHeader t m ++
         moduleAssembly.functionAssembly h.target h.name (bodyLines h.target h.features h.lines))]).flatMap
      Task.get ++
    -- Each module's files on a task of their own: a part (`Emit.run`) has one target.
    ((modules.map fun m => Task.spawn fun _ =>
      let items := moduleItems (fun a => moduleOf a.target.name) (arts.filter (·.art.module == m))
      [(s!"{src}/{m}.rs",
        header ++ s!"//! Verified `{m}` functions for `{t}`, whose text is in\n" ++
        s!"//! `{assemblyFile m}`.\n" ++
        "#![allow(dead_code)]\n" ++
        moduleText items ++ internalDecls (hs.filter (·.owner == m))),
       (s!"{crateDir t}/{assemblyFile m}", assemblyHeader t m ++ moduleAssembly items)]).map
      Task.get).flatten
  -- Each target's files on a task of their own.
  ((targets.map fun t => Task.spawn fun _ => perTarget t).map Task.get).flatten

/-- The generated files, as paths relative to `crates/` and their contents:
for each target, its crate's `lib.rs`, one `<module>.rs` per module and one
`internal/<name>.rs` per internal function (`internalsOf`), in its `codeDir`;
an error if an artifact is not made from an `Api` with a
contract (`checkApi`), two artifacts of a target have the same name
(`checkUnique`), a call is not of the code it runs (`checkCalls`), its
tables of constants, or an internal function's name or tables, are not as
`checkConsts`, `checkInternal` and `checkInternalTables` require, an
artifact's features are not those its code requires (`checkFeatures`), its
code has an instruction its target's printer cannot encode
(`checkEncodable`), its doc has no `# Safety` section at its end for what
`fullDoc` adds to it (`checkLayout`) or a bound on what it writes is not of a
writable array parameter, at most its size (`checkWritten`). Each check of
every artifact runs on `tasks` tasks (`forMPar`), one check after the other,
so the error is the
one checking them in order would give; what they read of an artifact more
than once is computed once, on `tasks` tasks (`Prepared`, `prepareAll`). -/
def files (as : List Artifact) : Except String (List (String × String)) := do
  -- The same artifacts, with equal parts the same value in memory
  -- (`ShareCommon.shareCommon'` returns its argument): the code of every call
  -- of a function in an artifact is then the same value as its first call's,
  -- which `badCall` and `distinctCalls` skip at once. Most calls' code was
  -- an equal value made again, not the same one. First, as sharing values
  -- that tasks have read takes several times longer.
  let as := ShareCommon.shareCommon' as
  forMPar as checkApi
  checkUnique as
  let ps := prepareAll as
  let hs := internalsOf ps
  forMPar ps (checkCalls ps hs)
  forMPar ps (checkConsts ps)
  forMPar hs (checkInternal ps hs)
  forMPar ps (checkInternalTables hs)
  forMPar ps checkFeatures
  forMPar ps checkEncodable
  forMPar as checkLayout
  forMPar as checkWritten
  return render ps hs fun t n =>
    match as.find? fun b => b.target.name == t && b.name == n with
    | some b => b.module
    | none => ((internal? hs t n).map internalModule).getD ""

end VG.Rust
