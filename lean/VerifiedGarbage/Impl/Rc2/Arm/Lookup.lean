module

public import VerifiedGarbage.TCB.Arm.Isa

/-! # RC2 selection on ARMv7

Every candidate is visited in a fixed order. Secret indices are used only
in arithmetic masks, never as addresses or branch conditions. (Key
expansion's scan of PITABLE is in `ExpandKey.lean`.)

`keyLookup` visits the whole 128-byte key schedule at `r0`, its 32 words of
two 16-bit entries each, as eight rows of four words, at addresses that
depend on nothing. Each row has a bit that is 1 exactly when the (secret)
index is one of its eight entries; each of its words times that bit is
added to the register of its column (`mla`), and then the index's column
among the four, and its half of that word, are chosen with multiplications
by bits of the index.
-/

@[expose] public section

namespace VG.Impl.Rc2.Arm

open VG.Arm

def rr (dst src : Reg) : Instr := .mov dst (.reg src)
def imm (dst : Reg) (n : Nat) : Instr := .movw dst (BitVec.ofNat 16 n)

def mask (r : Reg) (n : Nat) : List Instr :=
  [.mov r (.shifted r .lsl (32 - n)), .mov r (.shifted r .lsr (32 - n))]

def loadKey (i : Nat) : List Instr :=
  [.ldrb .r8 .r0 (2 * i), .ldrb .r9 .r0 (2 * i + 1),
   .mov .r9 (.shifted .r9 .ror 24), .dp .orr .r8 .r8 (.reg .r9)]

/-- Row `r` of the key schedule, its entries `8 r … 8 r + 7`: `r3` is 1 iff
the index in `r12` (below 64) is one of them (`(r12 ^ 8 r) - 8` is negative
exactly then), and each of the row's four words, times that bit, is added
to its column's register: `r9`, `r10`, `r11` and `lr`. -/
def keyRow (r : Nat) : List Instr :=
  [.dp .eor .r3 .r12 (.imm (BitVec.ofNat 32 (8 * r))), .dp .sub .r3 .r3 (.imm 8),
   .mov .r3 (.shifted .r3 .lsr 31),
   .ldr .r8 .r0 (16 * r), .mla .r9 .r8 .r3 .r9, .ldr .r8 .r0 (16 * r + 4), .mla .r10 .r8 .r3 .r10,
   .ldr .r8 .r0 (16 * r + 8), .mla .r11 .r8 .r3 .r11, .ldr .r8 .r0 (16 * r + 12), .mla .lr .r8 .r3 .lr]

/-- The index's word of the four of its row, by bits 2 and 1 of the index,
then its half of that word, by bit 0, into `r12`: each choice between `a`
and `b` by a bit is `(b - a) * bit + a`. -/
def keySelect : List Instr :=
  [.mov .r3 (.shifted .r12 .lsl 29), .mov .r3 (.shifted .r3 .lsr 31),
   .dp .sub .r11 .r11 (.reg .r9), .mla .r9 .r11 .r3 .r9,
   .dp .sub .lr .lr (.reg .r10), .mla .r10 .lr .r3 .r10,
   .mov .r3 (.shifted .r12 .lsl 30), .mov .r3 (.shifted .r3 .lsr 31),
   .dp .sub .r10 .r10 (.reg .r9), .mla .r9 .r10 .r3 .r9,
   .dp .and .r3 .r12 (.imm 1), .mov .r10 (.shifted .r9 .lsr 16),
   .dp .sub .r10 .r10 (.reg .r9), .mla .r9 .r10 .r3 .r9,
   .mov .r12 (.shifted .r9 .lsl 16), .mov .r12 (.shifted .r12 .lsr 16)]

/-- The index in `r12`, below 64, and the four columns zero. -/
def keyStart : List Instr :=
  [.dp .and .r12 .r12 (.imm 63), imm .r9 0, imm .r10 0, imm .r11 0, imm .lr 0]

/-- `r12 := schedule[r12 & 63]`. Clobbers `r3`, `r8`–`r11` and `lr`. -/
def keyLookup : Prog isa :=
  .block (keyStart ++ (List.range 8).flatMap keyRow ++ keySelect)

end VG.Impl.Rc2.Arm
