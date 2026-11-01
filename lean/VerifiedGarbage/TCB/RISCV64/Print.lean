module

public import VerifiedGarbage.TCB.RISCV64.Encode
public import VerifiedGarbage.TCB.Print

/-!
# Printer for the 64-bit RISC-V model

**Trusted.** Emits the GNU/LLVM assembler syntax used by Rust's
`asm!`/`naked_asm!` on RISC-V.

Each straight-line instruction, and the return, is printed as its machine
code (`Encode.lean`), one `.insn 4, <word>` per base instruction, each after
a line `// <the instruction's text>`, which the emitter writes in the module's listing, not in its code
(`Rust.listing`): the assembler only copies the words. The text
(`Instr.asm`) is the base instruction the model's semantics describes, with
registers written by their ABI names (`a0`, `sp`, `zero`); a frame of 2048
bytes or more (`alloc`, `free`) is its two `addi`s (see `push` in
`Isa.lean`).

The branches (`beqz`, `bnez`, `beq`, `bne`, `bltu`, `bgeu`), the jump (`j`)
and `call`, whose bytes depend on where their target is, are printed as
text for the assembler and linker to lay out, as is `lla` (see `Isa.lean`),
whose operand is the static's symbol (`SymPart.bare`), which the assembler
expands to `auipc` and `addi` with their relocations. `call` and the
branches on zero are pseudoinstructions of one instruction each, but for
`call`'s `auipc` and `jalr` (see `Isa.lean`).
-/

@[expose] public section

namespace VG.RISCV64

def Reg.name : Reg → String
  | .ra => "ra" | .t0 => "t0" | .t1 => "t1" | .t2 => "t2" | .s0 => "s0" | .s1 => "s1"
  | .a0 => "a0" | .a1 => "a1" | .a2 => "a2" | .a3 => "a3" | .a4 => "a4" | .a5 => "a5"
  | .a6 => "a6" | .a7 => "a7" | .s2 => "s2" | .s3 => "s3" | .s4 => "s4" | .s5 => "s5"
  | .s6 => "s6" | .s7 => "s7" | .s8 => "s8" | .s9 => "s9" | .s10 => "s10" | .s11 => "s11"
  | .t3 => "t3" | .t4 => "t4" | .t5 => "t5" | .t6 => "t6"

def LogicOp.name : LogicOp → String
  | .and => "and" | .or => "or" | .xor => "xor"

def ShiftOp.name : ShiftOp → String
  | .sll => "sll" | .srl => "srl" | .sra => "sra"

/-- The mnemonic of a load: zero-extending. -/
def Width.load : Width → String
  | .b => "lbu" | .h => "lhu" | .w => "lwu" | .d => "ld"

def Width.store : Width → String
  | .b => "sb" | .h => "sh" | .w => "sw" | .d => "sd"

def Instr.asm : Instr → List String
  | .add d n m => [s!"add {d.name}, {n.name}, {m.name}"]
  | .sub d n m => [s!"sub {d.name}, {n.name}, {m.name}"]
  | .addw d n m => [s!"addw {d.name}, {n.name}, {m.name}"]
  | .subw d n m => [s!"subw {d.name}, {n.name}, {m.name}"]
  | .sltu d n m => [s!"sltu {d.name}, {n.name}, {m.name}"]
  | .mul d n m => [s!"mul {d.name}, {n.name}, {m.name}"]
  | .mulhu d n m => [s!"mulhu {d.name}, {n.name}, {m.name}"]
  | .logic op d n m => [s!"{op.name} {d.name}, {n.name}, {m.name}"]
  | .addi d n imm => [s!"addi {d.name}, {n.name}, {imm}"]
  | .addiw d n imm => [s!"addiw {d.name}, {n.name}, {imm}"]
  | .logicImm op d n imm => [s!"{op.name}i {d.name}, {n.name}, {imm}"]
  | .li d imm => [s!"addi {d.name}, zero, {imm}"]
  | .lui d imm => [s!"lui {d.name}, {imm.toNat}"]
  | .shift op .d d n sh => [s!"{op.name}i {d.name}, {n.name}, {sh}"]
  | .shift op .w d n sh => [s!"{op.name}iw {d.name}, {n.name}, {sh}"]
  | .shiftReg op .d d n m => [s!"{op.name} {d.name}, {n.name}, {m.name}"]
  | .shiftReg op .w d n m => [s!"{op.name}w {d.name}, {n.name}, {m.name}"]
  | .load wd t n off => [s!"{wd.load} {t.name}, {off}({n.name})"]
  | .store wd t n off => [s!"{wd.store} {t.name}, {off}({n.name})"]
  | .push r => ["addi sp, sp, -16", s!"sd {r.name}, 8(sp)"]
  | .pop r => [s!"ld {r.name}, 8(sp)", "addi sp, sp, 16"]
  | .alloc bytes =>
    if bytes < 2048 then [s!"addi sp, sp, -{bytes}"]
    else ["addi sp, sp, -2032", s!"addi sp, sp, -{bytes - 2032}"]
  | .free bytes =>
    if bytes < 2048 then [s!"addi sp, sp, {bytes}"]
    else [s!"addi sp, sp, {bytes - 2032}", "addi sp, sp, 2032"]
  | .addSp d imm => [s!"addi {d.name}, sp, {imm}"]
  | .lla d name => [s!"lla {d.name}, {name}"]

/-- The lines of an instruction: each of its base instructions' text
(`asm`) as a comment, then that instruction's word (`encode`); its text if
it has no encoding (`lla`, printed by `symLines`, or an instruction that
`unencodable` reports, which the emitter refuses). -/
def Instr.code (i : Instr) : List String :=
  match i.encode with
  | some ws => (i.asm.zip ws).flatMap fun (t, w) => [s!"// {t}", insnLine w]
  | none => i.asm

/-- Why `i` has no encoding (`encode`): an operand that does not fit its
field; `none` for `lla`, which is text. -/
def Instr.unencodable : Instr → Option String
  | .lla .. => none
  | i => if i.encode.isNone then some "an operand does not fit its field" else none

def Cond.asm (c : Cond) (l : String) : String :=
  match c with
  | .zero r => s!"beqz {r.name}, {l}"
  | .nonzero r => s!"bnez {r.name}, {l}"
  | .eq a b => s!"beq {a.name}, {b.name}, {l}"
  | .ne a b => s!"bne {a.name}, {b.name}, {l}"
  | .ltu a b => s!"bltu {a.name}, {b.name}, {l}"
  | .geu a b => s!"bgeu {a.name}, {b.name}, {l}"

def printer : Printer isa where
  instr := Instr.code
  branch c l := [c.asm l]
  jump l := s!"j {l}"
  ret := ["// ret", insnLine retWord]
  call := "call"
  symLines
    | .lla d name => some [.sym s!"lla {d.name}, " .bare name]
    | _ => none
  unencodable := Instr.unencodable

end VG.RISCV64
