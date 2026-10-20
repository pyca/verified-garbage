module

public import VerifiedGarbage.TCB.Arm.Isa

/-! # RC2 selection on ARMv7

Every candidate is visited in a fixed order. Secret indices are used only
in arithmetic masks, never as addresses or branch conditions. (Key
expansion's scan of PITABLE is in `ExpandKey.lean`.)

`keyLookup` scans the whole 128-byte key schedule at `r0`: a loop over its
32 words, two 16-bit entries each, four words (eight entries) at a time, at
addresses that depend only on the iteration (`lr`), counted by `r9`. Each
pair of words, the entries `4b … 4b + 3`, is multiplied by a bit that is 1
exactly when the (secret) index is one of them, and ORed into `r3` and
`r11`; then the index's word among the two, and its half of that word, are
selected with multiplications by bits of the index.
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

/-- The index plus 8 in `r12`, both accumulators zero, the counter `r9` at
64 and `lr` at the last eight entries. -/
def keyStart : List Instr :=
  [.dp .and .r12 .r12 (.imm 63), .dp .add .r12 .r12 (.imm 8), imm .r3 0, imm .r11 0,
   imm .r9 64, .dp .add .lr .r0 (.imm 112)]

/-- With `r10` holding `z`, which is below 4 exactly when the index is one
of four entries: the bit `(z - 4) >> 31` times the pair of words of those
entries, the first loaded into `r8` already and the second at `lr + off +
4`, ORed into `r3` and `r11`. -/
def keyPair (off : Nat) : List Instr :=
  [.dp .sub .r10 .r10 (.imm 4), .mov .r10 (.shifted .r10 .lsr 31),
   .mul .r8 .r8 .r10, .dp .orr .r3 .r3 (.reg .r8),
   .ldr .r8 .lr (off + 4), .mul .r8 .r8 .r10, .dp .orr .r11 .r11 (.reg .r8)]

/-- Eight entries, from `lr`: with `z` the index plus 8 XOR the counter
(a multiple of 8), the first four are the index's iff `z < 4`, the other
four iff `z ^ 4 < 4`; then on to the eight before (Z set after the first
eight). -/
def keyBody : List Instr :=
  ([.ldr .r8 .lr 0, .dp .eor .r10 .r12 (.reg .r9)] : List Instr) ++ keyPair 0 ++
    ([.ldr .r8 .lr 8, .dp .eor .r10 .r12 (.reg .r9), .dp .eor .r10 .r10 (.imm 4)] : List Instr) ++
    keyPair 8 ++ ([.dp .sub .lr .lr (.imm 16), .subs .r9 .r9 (.imm 8)] : List Instr)

/-- The index's word, from `r3` and `r11` by bit 1 of the index, then its
half of that word, by bit 0, into `r12`. -/
def keySelect : List Instr :=
  [.dp .eor .r11 .r11 (.reg .r3), .mov .r10 (.shifted .r12 .lsr 1), .dp .and .r10 .r10 (.imm 1),
   .mul .r11 .r11 .r10, .dp .eor .r3 .r3 (.reg .r11),
   .dp .eor .r11 .r3 (.shifted .r3 .lsr 16), .dp .and .r10 .r12 (.imm 1),
   .mul .r11 .r11 .r10, .dp .eor .r3 .r3 (.reg .r11),
   .mov .r12 (.shifted .r3 .lsl 16), .mov .r12 (.shifted .r12 .lsr 16)]

/-- `r12 := schedule[r12 & 63]`. Clobbers `r3`, `r8`–`r11` and `lr`. -/
def keyLookup : Prog isa :=
  .seq (.block keyStart) (.seq (.loop (.block keyBody) .ne) (.block keySelect))

end VG.Impl.Rc2.Arm
