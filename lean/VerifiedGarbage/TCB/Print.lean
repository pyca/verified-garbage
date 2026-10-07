import VerifiedGarbage.TCB.Code

/-!
# Lowering structured code to assembly text

**Trusted.** Structured control flow is lowered to local labels and
conditional branches:

* `ite c t e`  ⟶  `b<c> Lthen; e; b Lend; Lthen: t; Lend:`
* `loop body c` ⟶  `Ltop: body; b<c> Ltop`
* `call name body` ⟶  `<call> name` (the call instruction, e.g. `call` or
  `bl`, of the function `name`, which is emitted separately: see
  `VG.Rust.files`)
* an instruction naming a `static` (`Printer.symLines`) ⟶ lines with the
  page of its address or the offset in that page (`Line.sym`), which
  `VG.Rust.files` writes in the syntax of the object format
* `frame push body pop` ⟶  `push; body; pop`

where `b<c> L` is the conditional branch to `L`, which on some targets is
more than one instruction (e.g. a comparison, then the branch).

Structured-control-flow labels are numeric local labels (`N:`, referenced
as `Nf` forward or `Nb` backward), the only kind Rust allows in inline
assembly (the `named_asm_labels` lint). Each has a distinct number, so each
reference has exactly one target. The numbers are `20`, `21`, `22`, …
(`2` followed by a counter): a number of only `0`s and `1`s could be read as a
binary literal in Intel syntax.
IA-32's `symPush` reserves label `2` for its adjacent call/address pair;
its references use the nearest `2f`/`2b`, even with several such pairs.

A printer's `funcAlign` is an assembler alignment directive (e.g.
`.p2align 6`) that `VG.Rust.function` emits after everything else in the
function, so that where the function's code lies relative to the processor's
fetch blocks and decoded-instruction cache lines depends on the function
alone, not on the size of the code the linker happens to place before it.
The directive raises the alignment of the function's section, so the
function's first instruction lies on the boundary (`naked_asm!` gives each
function a section of its own on ELF and COFF targets). Whatever padding the
assembler inserts at the directive comes after the return that ends the
function (`Printer.function`), so it is never executed: the printed code is
the same instructions, at the same distances from one another.

Together with each ISA's instruction printer this is part of the trusted
base; it is small enough to check by inspection and is covered by the golden
tests in `VerifiedGarbageTest/Print.lean`.
-/

namespace VG

/-- The part of a `static`'s address a line names: its 4 KB page, or its
offset in that page (AArch64's `adrp` and `add`), or the whole address as a
RIP-relative memory operand, `[rip + <sym>]` (x86-64's `lea`). -/
inductive SymPart
  | page
  | pageOff
  | ripRel
  /-- IA-32 displacement from the local instruction-pointer label `2`. -/
  | x86PcRel
  deriving DecidableEq, Repr

/-- A line of assembly: text, a call instruction of the function it names,
or text followed by the page or the offset in its page of the address of the
`static` it names, or by a RIP-relative operand of that address. -/
inductive Line
  | text (s : String)
  | call (name : String)
  | sym (s : String) (part : SymPart) (name : String)
  deriving DecidableEq, Repr

structure Printer (M : ISA) where
  /-- Assembly text for one instruction (may be several lines). -/
  instr : M.Instr → List String
  /-- Conditional branch to a label, taken when the condition is true (one or
  more lines, e.g. a comparison and a branch). -/
  branch : M.Cond → String → List String
  /-- Unconditional branch to a label. -/
  jump : String → String
  /-- Return to the caller. -/
  ret : List String
  /-- The mnemonic of the call instruction whose operand is a function's
  symbol (`ISA.call`), e.g. `call` or `bl`. -/
  call : String
  /-- The lines of an instruction that names a `static` (`Line.sym`); `none`
  for the others, whose lines are `instr`'s text. -/
  symLines : M.Instr → Option (List Line) := fun _ => none
  /-- Assembler directives before, and after, the body of a function that
  needs the CPU feature `f` (`Artifact.features`), for an assembler that
  rejects the instructions of a feature the target does not enable: they
  enable it for that function only. -/
  enableFeature : String → List String := fun _ => []
  disableFeature : String → List String := fun _ => []
  /-- Why the assembler cannot encode an instruction as the model describes
  it (e.g. an x86-64 displacement too wide for its field, which some
  assemblers silently truncate), or `none` if it can. The emitter refuses
  code containing such an instruction (`Rust.checkEncodable`). -/
  unencodable : M.Instr → Option String := fun _ => none
  /-- Assembler directives after the end of each function, aligning its
  start (see the module docs). They come after its return, so any padding
  they insert is never executed. -/
  funcAlign : List String := []

variable {M : ISA} (P : Printer M)

/-- The number of the `n`-th label of a function. -/
def labelNum (n : Nat) : String := s!"2{n}"

/-- Lower code to lines of assembly, using labels `labelNum n`; returns the
next unused label number. -/
def Printer.lower : Code M.Instr M.Cond → Nat → List Line × Nat
  | .block is, n => (is.flatMap fun i => (P.symLines i).getD ((P.instr i).map .text), n)
  | .seq c₁ c₂, n =>
    let (l₁, n) := lower c₁ n
    let (l₂, n) := lower c₂ n
    (l₁ ++ l₂, n)
  | .ite c t e, n =>
    let lThen := labelNum n
    let lEnd := labelNum (n + 1)
    let (le, n) := lower e (n + 2)
    let (lt, n) := lower t n
    ((P.branch c (lThen ++ "f")).map .text ++ le ++ [.text (P.jump (lEnd ++ "f")), .text (lThen ++ ":")] ++
      lt ++ [.text (lEnd ++ ":")], n)
  | .loop body c, n =>
    let lTop := labelNum n
    let (lb, n) := lower body (n + 1)
    ([.text (lTop ++ ":")] ++ lb ++ (P.branch c (lTop ++ "b")).map .text, n)
  | .call name _, n => ([.call name], n)
  | .frame i body j, n =>
    let (lb, n) := lower body n
    ((P.symLines i).getD ((P.instr i).map .text) ++ lb ++
      (P.symLines j).getD ((P.instr j).map .text), n)

/-- The complete body of a function: the lowered code followed by the return. -/
def Printer.function (body : Code M.Instr M.Cond) : List Line :=
  (P.lower body 0).1 ++ P.ret.map .text

end VG
