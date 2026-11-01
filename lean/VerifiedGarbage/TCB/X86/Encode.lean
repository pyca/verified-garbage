module

public import VerifiedGarbage.TCB.X86.Isa

/-!
# Machine code of the x86 (32-bit) model's instructions

**Trusted.** The bytes of each straight-line instruction of the model
(`Instr`), and of the return: what the printer (`Print.lean`) emits, as
`.byte <bytes>`, in place of the instruction's text, so that what runs is
these bytes, not the assembler's reading of a mnemonic. The branches (`jcc`,
`jmp`), the call and the address of a static (`symPush`), whose bytes
depend on where their target is, are still printed as text for the
assembler and linker to lay out.

The encodings are those of the Intel 64 and IA-32 Architectures Software
Developer's Manual, Volume 2: the instruction format of chapter 2 (prefixes,
opcode, ModR/M, SIB, displacement, immediate; Table 2-2, "32-Bit Addressing
Forms with the ModR/M Byte", and Table 2-3, "32-Bit Addressing Forms with
the SIB Byte"), with each instruction's opcode from its page in chapters 3
to 6, by the name in each definition's docs. Where an instruction has more
than one encoding, the one here is the assembler's choice for the printed
text, so the bytes are those it produced:
* between two registers, the form whose ModR/M `r/m` field is the
  destination (`89 /r` for `mov r32, r32`; `01 /r`, `29 /r`, … for the
  ALU instructions; `85 /r` for `test`);
* an immediate that fits a sign-extended byte, the `83 /digit ib` form; a
  wider one, `EAX`'s one-byte-shorter form (`05 id`, …, `A9 id`) for
  `EAX`, else `81 /digit id` (`F7 /0 id` for `test`, which has no `ib`
  form); `mov r32, imm32` is `B8+rd id`;
* a shift by 1, `D1 /digit`, else `C1 /digit ib`;
* a memory operand `[base + disp]`, the shortest ModR/M: no displacement
  for 0 (but with `EBP`, whose `mod = 00` encoding means no base, which
  takes a zero byte), a byte for `disp < 128`, else 4 bytes; with `ESP` a
  SIB byte (`24`: base `ESP`, no index).

`encode` is `none` for an instruction whose operand does not fit its field
(a displacement of 2³² or more, a shift count of 32 or more), which the
printer reports as unencodable (`Printer.unencodable`) and the emitter
refuses (`Rust.checkEncodable`), rather than truncating it; and for
`symPush`, which is text.
-/

@[expose] public section

namespace VG.X86

namespace Enc

/-- The register number in ModR/M and opcode fields (SDM Vol. 2, Table
3-1): `EAX` 0 to `EDI` 7, `Reg`'s order. -/
def reg (r : Reg) : Nat := r.ctorIdx

def xreg (r : XReg) : Nat := r.ctorIdx

def mreg (r : MReg) : Nat := r.ctorIdx

/-- The little-endian bytes of the `n`-byte value `v`. -/
def le (n v : Nat) : List Nat := (List.range n).map fun i => (v >>> (8 * i)) % 256

/-- The bytes of a signed 8-bit value. -/
def i8 (v : Int) : Nat := (v % 256).toNat

/-- ModR/M with `mod = 11`: `reg` (bits 5–3), `rm` (2–0). -/
def rr (regField rm : Nat) : List Nat := [0xC0 ||| regField <<< 3 ||| rm]

/-- ModR/M, SIB and displacement of `[base + disp]` with `reg` field
`regField`, `disp` a signed displacement: the shortest form (see the module
docs); `none` if `disp` is not a 32-bit value. -/
def memSigned (regField : Nat) (base : Reg) (disp : Int) : Option (List Nat) :=
  if -(2 ^ 31 : Int) ≤ disp ∧ disp < 2 ^ 32 then
    let b := reg base
    let sib := if base == .esp then [0x24] else []
    if disp == 0 ∧ base != .ebp then
      some ([regField <<< 3 ||| b] ++ sib)
    else if -128 ≤ disp ∧ disp < 128 then
      some ([0x40 ||| regField <<< 3 ||| b] ++ sib ++ [i8 disp])
    else
      some ([0x80 ||| regField <<< 3 ||| b] ++ sib ++ le 4 (disp % 2 ^ 32).toNat)
  else none

/-- `[base + disp]` of a `MemOp`. -/
def mem (regField : Nat) (m : MemOp) : Option (List Nat) := memSigned regField m.base m.disp

/-- Whether `v` is a sign-extended byte. -/
def fitsI8 (v : BitVec 32) : Bool := -128 ≤ v.toInt && v.toInt < 128

/-- The `/digit` of an ALU instruction's `81`/`83` forms, and the opcode of
its `r/m32, r32` form (whose `r32, r/m32` form is 2 more), and of `EAX`'s
`imm32` form; `test`'s are `F7 /0`, `85` and `A9`. -/
def aluDigit : AluOp → Nat
  | .add => 0 | .or => 1 | .adc => 2 | .sbb => 3 | .and => 4 | .sub => 5 | .xor => 6 | .cmp => 7
  | .test => 0

def aluRm : AluOp → Nat
  | .add => 0x01 | .or => 0x09 | .adc => 0x11 | .sbb => 0x19 | .and => 0x21 | .sub => 0x29
  | .xor => 0x31 | .cmp => 0x39 | .test => 0x85

def aluEax : AluOp → Nat
  | .add => 0x05 | .or => 0x0D | .adc => 0x15 | .sbb => 0x1D | .and => 0x25 | .sub => 0x2D
  | .xor => 0x35 | .cmp => 0x3D | .test => 0xA9

end Enc

open Enc in
/-- The bytes of a legacy SSE instruction (SDM chapters 3–5, by mnemonic). -/
def XOp.encode : XOp → Option (List Nat)
  | .bin op d s =>
    let opc : List Nat := match op with
      | .movdqa => [0x66, 0x0F, 0x6F] | .paddd => [0x66, 0x0F, 0xFE] | .pxor => [0x66, 0x0F, 0xEF]
      | .por => [0x66, 0x0F, 0xEB] | .pand => [0x66, 0x0F, 0xDB] | .pandn => [0x66, 0x0F, 0xDF]
      | .punpckldq => [0x66, 0x0F, 0x62] | .punpckhdq => [0x66, 0x0F, 0x6A]
      | .punpcklqdq => [0x66, 0x0F, 0x6C] | .punpckhqdq => [0x66, 0x0F, 0x6D]
      | .pshufb => [0x66, 0x0F, 0x38, 0x00] | .sha256msg1 => [0x0F, 0x38, 0xCC]
      | .sha256msg2 => [0x0F, 0x38, 0xCD] | .aesenc => [0x66, 0x0F, 0x38, 0xDC]
      | .aesenclast => [0x66, 0x0F, 0x38, 0xDD] | .paddq => [0x66, 0x0F, 0xD4]
      | .sha1msg1 => [0x0F, 0x38, 0xC9] | .sha1msg2 => [0x0F, 0x38, 0xCA]
      | .sha1nexte => [0x0F, 0x38, 0xC8] | .aesdec => [0x66, 0x0F, 0x38, 0xDE]
      | .aesdeclast => [0x66, 0x0F, 0x38, 0xDF] | .aesimc => [0x66, 0x0F, 0x38, 0xDB]
    some (opc ++ rr (xreg d) (xreg s))
  -- "PSLLD/PSLLQ" (66 0F 72 /6 ib, 66 0F 73 /6 ib), "PSRLD/PSRLQ" (66 0F 72 /2
  -- ib, 66 0F 73 /2 ib), "PSLLDQ" (66 0F 73 /7 ib), "PSRLDQ" (66 0F 73 /3 ib).
  | .shift op d n =>
    let (o, digit) := match op with
      | .pslld => (0x72, 6) | .psrld => (0x72, 2) | .psllq => (0x73, 6) | .psrlq => (0x73, 2)
      | .pslldq => (0x73, 7) | .psrldq => (0x73, 3)
    some ([0x66, 0x0F, o] ++ rr digit (xreg d) ++ [n.toNat])
  | .pshufd d s o => some ([0x66, 0x0F, 0x70] ++ rr (xreg d) (xreg s) ++ [o.toNat])
  | .pshuflw d s o => some ([0xF2, 0x0F, 0x70] ++ rr (xreg d) (xreg s) ++ [o.toNat])
  | .pshufhw d s o => some ([0xF3, 0x0F, 0x70] ++ rr (xreg d) (xreg s) ++ [o.toNat])
  | .palignr d s n => some ([0x66, 0x0F, 0x3A, 0x0F] ++ rr (xreg d) (xreg s) ++ [n.toNat])
  -- "SHA256RNDS2" (NP 0F 38 CB /r, `XMM0` implicit), "SHA1RNDS4" (NP 0F 3A CC
  -- /r ib).
  | .sha256rnds2 d s => some ([0x0F, 0x38, 0xCB] ++ rr (xreg d) (xreg s))
  | .sha1rnds4 d s n => some ([0x0F, 0x3A, 0xCC] ++ rr (xreg d) (xreg s) ++ [n.toNat])
  -- "MOVD" (66 0F 6E /r).
  | .movd d r => some ([0x66, 0x0F, 0x6E] ++ rr (xreg d) (reg r))
  -- "AESKEYGENASSIST" (66 0F 3A DF /r ib), "PCLMULQDQ" (66 0F 3A 44 /r ib).
  | .aeskeygenassist d s n => some ([0x66, 0x0F, 0x3A, 0xDF] ++ rr (xreg d) (xreg s) ++ [n.toNat])
  | .pclmulqdq d s n => some ([0x66, 0x0F, 0x3A, 0x44] ++ rr (xreg d) (xreg s) ++ [n.toNat])

open Enc in
/-- The bytes of an MMX instruction (SDM chapters 3–5, by mnemonic). -/
def MOp.encode : MOp → Option (List Nat)
  | .bin op d s =>
    let o := match op with
      | .paddq => 0xD4 | .pxor => 0xEF | .por => 0xEB | .pand => 0xDB | .pandn => 0xDF
    match s with
    | .reg r => some ([0x0F, o] ++ rr (mreg d) (mreg r))
    | .mem m => (mem (mreg d) m).map ([0x0F, o] ++ ·)
  -- "PSLLQ" (NP 0F 73 /6 ib), "PSRLQ" (NP 0F 73 /2 ib).
  | .shift op d n => some ([0x0F, 0x73] ++ rr (match op with | .psllq => 6 | .psrlq => 2) (mreg d) ++ [n.toNat])
  -- "MOVQ" (NP 0F 6F /r).
  | .movq d s => match s with
    | .reg r => some ([0x0F, 0x6F] ++ rr (mreg d) (mreg r))
    | .mem m => (mem (mreg d) m).map ([0x0F, 0x6F] ++ ·)
  -- "PUNPCKLDQ" (NP 0F 62 /r), "MOVD" (NP 0F 6E /r), "MOVQ2DQ" (F3 0F D6 /r),
  -- "MOVDQ2Q" (F2 0F D6 /r).
  | .punpckldq d s => some ([0x0F, 0x62] ++ rr (mreg d) (mreg s))
  | .movd d r => some ([0x0F, 0x6E] ++ rr (mreg d) (reg r))
  | .movq2dq d s => some ([0xF3, 0x0F, 0xD6] ++ rr (xreg d) (mreg s))
  | .movdq2q d s => some ([0xF2, 0x0F, 0xD6] ++ rr (mreg d) (xreg s))

open Enc in
/-- The bytes of each instruction `Instr.asm` (`Print.lean`) names, in
order; `none` if an operand does not fit its field (see the module docs),
or for `symPush`, which is text. -/
def Instr.encode : Instr → Option (List (List Nat))
  -- "MOV": `89 /r` (between registers), `B8+rd id`, `8B /r` (a load), `89 /r`
  -- (a store).
  | .mov d (.reg s) => some [[0x89] ++ rr (reg s) (reg d)]
  | .mov d (.imm v) => some [[0xB8 + reg d] ++ le 4 v.toNat]
  | .mov d (.mem m) => (mem (reg d) m).map fun b => [[0x8B] ++ b]
  | .store m r => (mem (reg r) m).map fun b => [[0x89] ++ b]
  -- The ALU instructions (see `aluRm`, `aluDigit`, `aluEax`).
  | .alu op d (.reg s) => some [[aluRm op] ++ rr (reg s) (reg d)]
  | .alu op d (.mem m) =>
    -- `r32, r/m32` (the `r/m32, r32` opcode + 2), but `test`'s one form, `85 /r`.
    (mem (reg d) m).map fun b => [[if op == .test then 0x85 else aluRm op + 2] ++ b]
  | .alu op d (.imm v) =>
    if op != .test && fitsI8 v then some [[0x83] ++ rr (aluDigit op) (reg d) ++ [v.toNat % 256]]
    else if d == .eax then some [[aluEax op] ++ le 4 v.toNat]
    else some [[if op == .test then 0xF7 else 0x81] ++ rr (aluDigit op) (reg d) ++ le 4 v.toNat]
  -- "ROR" (`/1`), "SHR" (`/5`): `D1 /digit` by 1, else `C1 /digit ib`.
  | .shift op d n =>
    let digit := match op with | .ror => 1 | .shr => 5
    if n == 1 then some [[0xD1] ++ rr digit (reg d)]
    else if n < 32 then some [[0xC1] ++ rr digit (reg d) ++ [n]]
    else none
  -- "BSWAP" (`0F C8+rd`), "MOVZX" (`0F B6 /r`), "MOV" (`88 /r`, a byte store).
  | .bswap d => some [[0x0F, 0xC8 + reg d]]
  | .movzx8 d m => (mem (reg d) m).map fun b => [[0x0F, 0xB6] ++ b]
  | .store8 m r => (mem (reg r.reg) m).map fun b => [[0x88] ++ b]
  -- "PUSH" (`50+rd`), "POP" (`58+rd`).
  | .push rs => some (rs.map fun r => [0x50 + reg r])
  | .pop r k => some (List.replicate k [0x58 + reg r])
  -- "LEA" (`8D /r`) of `[esp - bytes]`, `[esp + bytes]`.
  | .alloc bytes => (memSigned (reg .esp) .esp (-(bytes : Int))).map fun b => [[0x8D] ++ b]
  | .free bytes => (memSigned (reg .esp) .esp bytes).map fun b => [[0x8D] ++ b]
  -- "MUL" (`F7 /4`).
  | .mul r => some [[0xF7] ++ rr 4 (reg r)]
  -- "MOVDQU" (`F3 0F 6F /r`, `F3 0F 7F /r`), "MOVQ" (`F3 0F 7E /r`, a load;
  -- `66 0F D6 /r`, a store).
  | .movdquLoad d m => (mem (xreg d) m).map fun b => [[0xF3, 0x0F, 0x6F] ++ b]
  | .movdquStore m r => (mem (xreg r) m).map fun b => [[0xF3, 0x0F, 0x7F] ++ b]
  | .movqLoad d m => (mem (xreg d) m).map fun b => [[0xF3, 0x0F, 0x7E] ++ b]
  | .movqStore m r => (mem (xreg r) m).map fun b => [[0x66, 0x0F, 0xD6] ++ b]
  | .xop op => op.encode.map ([·])
  | .mop op => op.encode.map ([·])
  -- "MOVQ" (`NP 0F 7F /r`, a store from an MMX register).
  | .mmxStore m r => (mem (mreg r) m).map fun b => [[0x0F, 0x7F] ++ b]
  | .mmxEnter => some []
  -- "EMMS" (`NP 0F 77`), "PMULUDQ" (`66 0F F4 /r`).
  | .emms => some [[0x0F, 0x77]]
  | .pmuludq d s => some [[0x66, 0x0F, 0xF4] ++ rr (xreg d) (xreg s)]
  -- Intel's MCDT prologue and epilogue (`Isa.lean`): `lea esp, [esp-12]`,
  -- "STMXCSR" (`0F AE /3`), `mov r32, imm32`, `mov [esp], r32`, "LDMXCSR"
  -- (`0F AE /2`), "LFENCE" (`0F AE E8`); then `lfence`, `ldmxcsr`, `lea`.
  | .mcdtEnter r => do
    let lea ← memSigned (reg .esp) .esp (-12)
    let st ← memSigned 3 .esp 4
    let mv ← memSigned (reg r) .esp 0
    let ld ← memSigned 2 .esp 0
    return [[0x8D] ++ lea, [0x0F, 0xAE] ++ st, [0xB8 + reg r] ++ le 4 0x1FBF, [0x89] ++ mv,
      [0x0F, 0xAE] ++ ld, [0x0F, 0xAE, 0xE8]]
  | .mcdtLeave => do
    let ld ← memSigned 2 .esp 4
    let lea ← memSigned (reg .esp) .esp 12
    return [[0x0F, 0xAE, 0xE8], [0x0F, 0xAE] ++ ld, [0x8D] ++ lea]
  | .symPush .. => none

/-- `ret` ("RET", `C3`). -/
def retBytes : List Nat := [0xC3]

/-- `b` as two hexadecimal digits, after `0x`. -/
def hex8 (b : Nat) : String :=
  let ds := Nat.toDigits 16 (b % 256)
  "0x" ++ String.ofList (List.replicate (2 - ds.length) '0' ++ ds)

/-- The assembler directive emitting the bytes `bs`: `.byte` of each, as
two hexadecimal digits, separated by commas alone (the form the emitter
joins and packs, `Rust.pushLine`). -/
def byteLine (bs : List Nat) : String := ".byte " ++ ",".intercalate (bs.map hex8)

end VG.X86
