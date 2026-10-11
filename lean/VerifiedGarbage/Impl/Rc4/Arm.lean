module

public import VerifiedGarbage.TCB.Arm.Isa

/-!
# RC4 on ARMv7

As on x86 (`Impl/Rc4/X86.lean`), the 256-byte table at `r12` is visited as
64 words at fixed addresses: a secret-indexed lookup keeps, with masks, the
word that holds the byte and then the byte of it; a secret-indexed
replacement stores every word back, XORed with a masked difference that is
nonzero only in the selected byte. A mask is all ones or zero by a
comparison (`cmp`, which sets the carry flag unless the difference
borrows) and `adc` of all ones (`r10`) and zero: `-1 + C`. Only the word
addresses, the PRGA index `i`, the key offset, the pointers and the lengths
are public.

Registers: the table at `r12`, all ones in `r10`, the public index `i` in
`r4`, `j` in `r5`, the secret index of a lookup or replacement in `r6`, its
result in `r7`; `r8`, `r9` and `r11` are scratch. Initialization keeps the
key at `r0`, its length in `r1` and the key offset in `r2`; the stream
function the count of bytes done in `r0`, the data at `r1` and its length in
`r2`. `scratch` stays in `r3`: our caller's `r4`–`r11` are saved in its first
32 bytes and restored from there at the end. No stack is used.
-/

@[expose] public section

namespace VG.Impl.Rc4.Arm

open VG.Arm

/-- An immediate. -/
def imm (n : Nat) : Op2 := .imm (BitVec.ofNat 32 n)

/-- `r9` := all ones if `r6 XOR 4k < 4` (byte `r6` is in word `k`), else 0. -/
def rowMask (k : Nat) : List Instr :=
  [.dp .eor .r9 .r6 (imm (4 * k)), .cmp .r9 (imm 4), .adc .r9 .r10 (imm 0)]

/-- `r9` := all ones if `r6 AND 3 = j`, else 0. -/
def laneMask (j : Nat) : List Instr :=
  [.dp .and .r9 .r6 (imm 3), .dp .eor .r9 .r9 (imm j), .cmp .r9 (imm 1), .adc .r9 .r10 (imm 0)]

/-- Keep word `k` in `r8` if it holds byte `r6`. -/
def gatherStep (k : Nat) : List Instr :=
  rowMask k ++ ([.ldr .r11 .r12 (4 * k), .dp .and .r9 .r9 (.reg .r11), .dp .orr .r8 .r8 (.reg .r9)] :
    List Instr)

/-- Keep byte `j` of the word in `r8` (shifted down by `8j` so far) in `r7` if
it is byte `r6`. -/
def pickStep (j : Nat) : List Instr :=
  laneMask j ++ ([.dp .and .r9 .r9 (.reg .r8), .dp .orr .r7 .r7 (.reg .r9),
    .mov .r8 (.shifted .r8 .lsr 8)] : List Instr)

/-- The byte of the table at `r12` indexed by the low byte `r6`, into `r7`.
Clobbers `r8`, `r9`, `r11` and the flags. -/
def lookup : List Instr :=
  ([.mov .r8 (imm 0)] : List Instr) ++ (List.range 64).flatMap gatherStep ++
    ([.mov .r7 (imm 0)] : List Instr) ++ (List.range 4).flatMap pickStep ++
    ([.dp .and .r7 .r7 (imm 255)] : List Instr)

/-- Shift the difference in `r8` up a byte and add the byte in `r7` if `j` is
the lane of `r6`. -/
def spreadStep (j : Nat) : List Instr :=
  laneMask j ++ ([.dp .and .r9 .r9 (.reg .r7), .mov .r8 (.shifted .r8 .ror 24),
    .dp .orr .r8 .r8 (.reg .r9)] : List Instr)

/-- XOR word `k` with the difference in `r8` if it holds byte `r6`, and store
it back. -/
def scatterStep (k : Nat) : List Instr :=
  rowMask k ++ ([.dp .and .r9 .r9 (.reg .r8), .ldr .r11 .r12 (4 * k), .dp .eor .r9 .r9 (.reg .r11),
    .str .r9 .r12 (4 * k)] : List Instr)

/-- The lanes 3 down to 0. -/
def lanesDown : List Nat := [3, 2, 1, 0]

/-- `r11` := the byte at the public index `r4` of the table. -/
def loadI : List Instr := [.dp .add .r9 .r12 (.reg .r4), .ldrb .r11 .r9 0]

/-- Replace the byte of the table at `r12` indexed by the low byte of `r6`
with the byte at the public index `r4`, returning its original value in
`r7`. Clobbers `r8`, `r9`, `r11` and the flags. -/
def replace : List Instr :=
  lookup ++ loadI ++ ([.dp .eor .r7 .r7 (.reg .r11), .mov .r8 (imm 0)] : List Instr) ++
    lanesDown.flatMap spreadStep ++ ([.dp .eor .r7 .r7 (.reg .r11)] : List Instr) ++
    (List.range 64).flatMap scatterStep

/-! ## Our caller's registers -/

/-- Where our caller's `r4`–`r11` are kept in `scratch`. -/
def saved : List (Reg × Nat) :=
  [(.r4, 0), (.r5, 4), (.r6, 8), (.r7, 12), (.r8, 16), (.r9, 20), (.r10, 24), (.r11, 28)]

/-- Save them, through `r3`. -/
def save : List Instr := saved.map fun p => .str p.1 .r3 p.2

/-- Restore them, through `r3`. -/
def restore : List Instr := saved.map fun p => .ldr p.1 .r3 p.2

/-- `r10` := all ones. -/
def ones : List Instr := [.movw .r10 0xFFFF, .movt .r10 0xFFFF]

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
