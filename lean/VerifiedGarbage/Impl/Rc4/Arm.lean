module

public import VerifiedGarbage.TCB.Arm.Isa

/-!
# RC4 on ARMv7

The 256-byte table at `r12` is visited as 64 words at fixed addresses, 32
rows of two. The row of a secret index, its high five bits, is a one-hot
word in `r10` (`oneHot`), and each row has a selector from its bit, 1 for the
index's row and 0 for the others (`rowSel`). A lookup adds each word times
its row's selector to the register of its column, `r7` or `r8`, and chooses
between the two by the index's bit 2 (`gatherWord`), then takes the index's
byte of that word by two conditional shifts (`pickByte`); a conditional step
is a multiplication by a bit of the index and an addition (`mla`). A
replacement makes the difference between the word with its byte replaced and
the word (`deltaWord`), and adds to each word of the table, stored back, its
row's selector times that difference, or times zero in the other column
(`splitDelta`, `scatterRow`). Only the word addresses, the PRGA index `i`,
the key offset, the pointers and the lengths are public.

Registers: the table at `r12`, all ones in `r10` between lookups (for the
key offset's mask; a lookup keeps its one-hot word there and sets it back),
the public index `i` in `r4`, `j` in `r5`, the secret index of a lookup or
replacement in `r6`, its result in `r7`; `r8`, `r9` and `r11` are scratch.
Initialization keeps the key at `r0`, its length in `r1` and the key offset
in `r2`; the stream function the count of bytes done in `r0`, the data at
`r1` and its length in `r2`. `scratch` stays in `r3`: our caller's
`r4`–`r11` are saved in its first 32 bytes and restored from there at the
end. No stack is used.
-/

@[expose] public section

namespace VG.Impl.Rc4.Arm

open VG.Arm

/-- An immediate. -/
def imm (n : Nat) : Op2 := .imm (BitVec.ofNat 32 n)

/-- `r10` := all ones. -/
def ones : List Instr := [.movw .r10 0xFFFF, .movt .r10 0xFFFF]

/-- `d` := bit `k` (below 31) of `src`: 0 or 1. -/
def bit (d src : Reg) (k : Nat) : List Instr :=
  [.mov d (.shifted src .lsl (31 - k)), .mov d (.shifted d .lsr 31)]

/-- A step of the one-hot word: `r10` shifted left by `2 ^ b` if bit `3 + b`
of the index `r6` is set. -/
def ohStep (b : Nat) : List Instr :=
  bit .r11 .r6 (3 + b) ++ ([.mov .r9 (.shifted .r10 .lsl (2 ^ b)), .dp .sub .r9 .r9 (.reg .r10),
    .mla .r10 .r9 .r11 .r10] : List Instr)

/-- `r10` := the one-hot word of the row of the index `r6` (below 256):
bit `r6 >> 3`. Clobbers `r9` and `r11`. -/
def oneHot : List Instr :=
  bit .r11 .r6 3 ++ ([.dp .add .r10 .r11 (imm 1)] : List Instr) ++ ohStep 1 ++ ohStep 2 ++ ohStep 3 ++ ohStep 4

/-- `d` := the selector of row `r`: bit `r` of the one-hot word `r10`. -/
def rowSel (d : Reg) (r : Nat) : List Instr :=
  if r = 31 then [.mov d (.shifted .r10 .lsr 31)] else bit d .r10 r

/-- Row `r` of a lookup: its two words, times its selector, added to `r7`
and `r8`. -/
def gatherRow (r : Nat) : List Instr :=
  rowSel .r11 r ++ ([.ldr .r9 .r12 (8 * r), .mla .r7 .r9 .r11 .r7, .ldr .r9 .r12 (8 * r + 4),
    .mla .r8 .r9 .r11 .r8] : List Instr)

/-- `r7` := the word of the table that holds the byte at the index `r6`.
Leaves the index's one-hot word in `r10`; clobbers `r8`, `r9` and `r11`. -/
def gatherWord : List Instr :=
  oneHot ++ ([.mov .r7 (imm 0), .mov .r8 (imm 0)] : List Instr) ++ (List.range 32).flatMap gatherRow ++
    bit .r11 .r6 2 ++ ([.dp .sub .r8 .r8 (.reg .r7), .mla .r7 .r8 .r11 .r7] : List Instr)

/-- `r7` := byte `r6 & 3` of the word in `r7`: shifted right by 8 if bit 0
of `r6` is set, by 16 if bit 1 is. Clobbers `r9` and `r11`. -/
def pickByte : List Instr :=
  bit .r11 .r6 0 ++ ([.mov .r9 (.shifted .r7 .lsr 8), .dp .sub .r9 .r9 (.reg .r7), .mla .r7 .r9 .r11 .r7] :
    List Instr) ++ bit .r11 .r6 1 ++
    ([.mov .r9 (.shifted .r7 .lsr 16), .dp .sub .r9 .r9 (.reg .r7), .mla .r7 .r9 .r11 .r7,
      .dp .and .r7 .r7 (imm 255)] : List Instr)

/-- The byte of the table at `r12` indexed by the low byte `r6`, into `r7`.
Clobbers `r8`, `r9` and `r11`; `r10` is all ones again afterwards. -/
def lookup : List Instr := gatherWord ++ pickByte ++ ones

/-- `r11` := the byte at the public index `r4` of the table. -/
def loadI : List Instr := [.dp .add .r9 .r12 (.reg .r4), .ldrb .r11 .r9 0]

/-- With the word of the index `r6` in `r7`: `r8` := the difference between
that word with its byte `r6 & 3` replaced by the byte at the public index
`r4`, and the word. `2 ^ (8 L)` for `L = r6 & 3` is made in `r8`, the byte
times it and 255 times it in `r11` and `r9`. -/
def deltaWord : List Instr :=
  bit .r11 .r6 0 ++ ([.mov .r8 (.shifted .r11 .lsl 8), .dp .sub .r8 .r8 (.reg .r11), .dp .add .r8 .r8 (imm 1)] :
    List Instr) ++ bit .r11 .r6 1 ++
    ([.mov .r9 (.shifted .r11 .lsl 16), .dp .sub .r9 .r9 (.reg .r11), .dp .add .r9 .r9 (imm 1),
      .mul .r8 .r8 .r9] : List Instr) ++ loadI ++
    ([.mul .r11 .r11 .r8, .mov .r9 (.shifted .r8 .lsl 8), .dp .sub .r9 .r9 (.reg .r8),
      .dp .bic .r8 .r7 (.reg .r9), .dp .orr .r8 .r8 (.reg .r11), .dp .sub .r8 .r8 (.reg .r7)] : List Instr)

/-- The difference `r8` to the index's column: `r11` := it if bit 2 of `r6`
is set, else 0, and `r8` the rest. -/
def splitDelta : List Instr :=
  bit .r9 .r6 2 ++ ([.mul .r11 .r8 .r9, .dp .sub .r8 .r8 (.reg .r11)] : List Instr)

/-- Row `r` of a replacement: its two words, each plus its column's
difference times the row's selector, stored back. -/
def scatterRow (r : Nat) : List Instr :=
  rowSel .r9 r ++ ([.ldr .r6 .r12 (8 * r), .mla .r6 .r8 .r9 .r6, .str .r6 .r12 (8 * r),
    .ldr .r6 .r12 (8 * r + 4), .mla .r6 .r11 .r9 .r6, .str .r6 .r12 (8 * r + 4)] : List Instr)

/-- Replace the byte of the table at `r12` indexed by the low byte of `r6`
with the byte at the public index `r4`, returning its original value in
`r7`. Clobbers `r6`, `r8`, `r9` and `r11`; `r10` is all ones again
afterwards. -/
def replace : List Instr :=
  gatherWord ++ deltaWord ++ pickByte ++ splitDelta ++ (List.range 32).flatMap scatterRow ++ ones

/-! ## Our caller's registers -/

/-- Where our caller's `r4`–`r11` are kept in `scratch`. -/
def saved : List (Reg × Nat) :=
  [(.r4, 0), (.r5, 4), (.r6, 8), (.r7, 12), (.r8, 16), (.r9, 20), (.r10, 24), (.r11, 28)]

/-- Save them, through `r3`. -/
def save : List Instr := saved.map fun p => .str p.1 .r3 p.2

/-- Restore them, through `r3`. -/
def restore : List Instr := saved.map fun p => .ldr p.1 .r3 p.2

/-! ## Initialization: `vg_rc4_init(key = r0, key_len = r1, ctx = r2, scratch = r3)` -/

/-- Store the identity permutation, a byte at a time. -/
def identityStep : List Instr :=
  [.dp .add .r9 .r12 (.reg .r4), .strb .r4 .r9 0, .dp .add .r4 .r4 (imm 1), .cmp .r4 (imm 256)]

/-- `j += S[i] + key[off]`, the swap (`S[i]` stored last), the next key
offset (0 at the key length, by a mask: both are public), and `i`. -/
def scheduleStep : List Instr :=
  loadI ++ ([.dp .add .r5 .r5 (.reg .r11), .dp .add .r9 .r0 (.reg .r2), .ldrb .r9 .r9 0,
    .dp .add .r5 .r5 (.reg .r9), .dp .and .r5 .r5 (imm 255), .mov .r6 (.reg .r5)] : List Instr) ++
    replace ++
    ([.dp .add .r2 .r2 (imm 1), .cmp .r2 (.reg .r1), .adc .r9 .r10 (imm 0),
      .dp .and .r2 .r2 (.reg .r9), .dp .add .r9 .r12 (.reg .r4), .strb .r7 .r9 0,
      .dp .add .r4 .r4 (imm 1), .cmp .r4 (imm 256)] : List Instr)

/-- Key scheduling after the key-length check. -/
def initValid : Prog isa :=
  .seq (.block (save ++ ([.mov .r12 (.reg .r2), .mov .r4 (imm 0)] : List Instr)))
    (.seq (.loop (.block identityStep) .ne)
      (.seq (.block (([.mov .r4 (imm 0), .mov .r2 (imm 0), .mov .r5 (imm 0)] : List Instr) ++ ones))
        (.seq (.loop (.block scheduleStep) .ne)
          (.block (([.mov .r9 (imm 0), .strb .r9 .r12 256, .strb .r9 .r12 257] : List Instr) ++
            restore ++ ([.mov .r0 (imm 0)] : List Instr))))))

/-- Checked key scheduling: `(key_len - 1) >> 8` is zero iff `key_len` is in
1..=256; invalid lengths return 1, valid lengths 0. -/
def init : Prog isa :=
  .seq (.block [.dp .sub .r12 .r1 (imm 1), .mov .r12 (.shifted .r12 .lsr 8), .cmp .r12 (imm 0)])
    (.ite .ne (.block [.mov .r0 (imm 1)]) initValid)

/-! ## The stream function: `vg_rc4_apply(ctx = r0, data = r1, len = r2, scratch = r3)` -/

/-- The PRGA index `i` to `r12`, and the length tested. -/
def entry : List Instr := [.ldrb .r12 .r0 256, .cmp .r2 (imm 0)]

/-- `i` to `r4`, the table to `r12`, `j` to `r5`, no bytes done in `r0`, and
all ones in `r10`. -/
def start : List Instr :=
  ([.mov .r4 (.reg .r12), .mov .r12 (.reg .r0), .ldrb .r5 .r12 257, .mov .r0 (imm 0)] :
    List Instr) ++ ones

/-- One PRGA step: `i += 1`, `j += S[i]`, the swap, then the keystream byte
`S[S[i] + S[j]]` XORed into data byte `r0`. -/
def applyStep : List Instr :=
  ([.dp .add .r4 .r4 (imm 1), .dp .and .r4 .r4 (imm 255)] : List Instr) ++ loadI ++
    ([.dp .add .r5 .r5 (.reg .r11), .dp .and .r5 .r5 (imm 255), .mov .r6 (.reg .r5)] :
      List Instr) ++ replace ++ loadI ++
    ([.dp .add .r9 .r12 (.reg .r4), .strb .r7 .r9 0, .dp .add .r6 .r7 (.reg .r11),
      .dp .and .r6 .r6 (imm 255)] : List Instr) ++ lookup ++
    ([.dp .add .r9 .r1 (.reg .r0), .ldrb .r11 .r9 0, .dp .eor .r11 .r11 (.reg .r7),
      .strb .r11 .r9 0, .dp .add .r0 .r0 (imm 1), .cmp .r0 (.reg .r2)] : List Instr)

/-- Store the PRGA indices back. -/
def finish : List Instr := [.strb .r4 .r12 256, .strb .r5 .r12 257]

/-- Streaming XOR, preserving the permutation and both PRGA indices. `i`
is loaded first, while only caller-saved registers are written: the
function may leak it. -/
def apply : Prog isa :=
  .seq (.block entry)
    (.ite .eq (.block [])
      (.seq (.block (save ++ start))
        (.seq (.loop (.block applyStep) .ne) (.block (finish ++ restore)))))

end VG.Impl.Rc4.Arm
