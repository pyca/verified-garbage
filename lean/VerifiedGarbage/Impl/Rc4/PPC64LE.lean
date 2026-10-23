module

public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# RC4 on PPC64LE

As on x86-64 (`Impl/Rc4/X86_64.lean`), the 256-byte table at `r3` is
visited as 32 doublewords at fixed addresses: a secret-indexed lookup keeps,
with masks, the doubleword that holds the byte and then the byte of it; a
secret-indexed replacement stores every doubleword back, XORed with a masked
difference that is nonzero only in the selected byte. There is no compare
instruction: a mask is all ones or zero by whether a value `v < 2 ^ 63` is
zero, `0 - ((v - 1) >> 63)` (`isZero`). Only the doubleword addresses, the
PRGA index `i`, the key offset, the pointers and the lengths are public.

Registers: the table at `r3`, the public index `i` in `r6`, the secret
index of a lookup or replacement in `r9`, its result in `r10`, zero in `r8`;
`r0`, `r11` and `r12` are scratch. Initialization keeps the key at `r7`, its
length in `r4`, the key offset in `r5` and `j` in `r9`; the stream function
keeps the data at `r4`, the remaining length in `r5` and `j` in `r7`. Only
volatile registers are used, and no stack.
-/

@[expose] public section

namespace VG.Impl.Rc4.PPC64LE

open VG.PPC64LE

/-- `r12` := all ones if `r12` (below `2 ^ 63`) is zero, else 0. -/
def isZero : List Instr := [.subi .r12 .r12 1, .lsr .d .r12 .r12 63, .sub .r12 .r8 .r12]

/-- `r12` := all ones if `r9 XOR 8k < 8` (byte `r9` is in doubleword `k`), else 0. -/
def rowMask (k : Nat) : List Instr :=
  [.li .r12 (8 * k), .logic .xor .r12 .r12 .r9, .lsr .d .r12 .r12 3] ++ isZero

/-- `r12` := all ones if `r9 AND 7 = j`, else 0. -/
def laneMask (j : Nat) : List Instr :=
  [.li .r12 j, .logic .xor .r12 .r12 .r9, .lsl .r12 .r12 61, .lsr .d .r12 .r12 61] ++ isZero

/-- Keep doubleword `k` in `r11` if it holds byte `r9`. -/
def gatherStep (k : Nat) : List Instr :=
  rowMask k ++ ([.load .d .r0 .r3 (8 * k), .logic .and .r0 .r0 .r12, .logic .or .r11 .r11 .r0] :
    List Instr)

/-- Keep byte `j` of the doubleword in `r11` (shifted down by `8j` so far) in
`r10` if it is byte `r9`. -/
def pickStep (j : Nat) : List Instr :=
  laneMask j ++ ([.logic .and .r0 .r11 .r12, .logic .or .r10 .r10 .r0, .lsr .d .r11 .r11 8] :
    List Instr)

/-- The byte of the table at `r3` indexed by the low byte `r9`, into `r10`.
Clobbers `r0`, `r11` and `r12`. -/
def lookup : List Instr :=
  ([.li .r11 0] : List Instr) ++ (List.range 32).flatMap gatherStep ++
    ([.li .r10 0] : List Instr) ++ (List.range 8).flatMap pickStep ++
    ([.lsl .r10 .r10 56, .lsr .d .r10 .r10 56] : List Instr)

/-- Shift the difference in `r11` up a byte and add the byte in `r10` if `j`
is the lane of `r9`: run for `j` from 7 down to 0, it leaves `r10` shifted to
the lane of `r9`. -/
def spreadStep (j : Nat) : List Instr :=
  laneMask j ++ ([.logic .and .r0 .r10 .r12, .rotr .d .r11 .r11 56, .logic .or .r11 .r11 .r0] :
    List Instr)

/-- XOR doubleword `k` with the difference in `r11` if it holds byte `r9`,
and store it back. -/
def scatterStep (k : Nat) : List Instr :=
  rowMask k ++ ([.logic .and .r12 .r12 .r11, .load .d .r0 .r3 (8 * k),
    .logic .xor .r0 .r0 .r12, .store .d .r0 .r3 (8 * k)] : List Instr)

/-- The lanes 7 down to 0. -/
def lanesDown : List Nat := [7, 6, 5, 4, 3, 2, 1, 0]

/-- `r0` := the byte at the public index `r6` of the table, through `r12`. -/
def loadI : List Instr := [.add .r12 .r3 .r6, .lbz .r0 .r12 0]

/-- Replace the byte of the table at `r3` indexed by the low byte of `r9`
with the byte at the public index `r6`, returning its original value in
`r10`. Clobbers `r0`, `r11` and `r12`. -/
def replace : List Instr :=
  lookup ++ loadI ++ ([.logic .xor .r10 .r10 .r0, .li .r11 0] : List Instr) ++
    lanesDown.flatMap spreadStep ++ loadI ++ ([.logic .xor .r10 .r10 .r0] : List Instr) ++
    (List.range 32).flatMap scatterStep

/-- Store the identity permutation, a byte at a time; `r12 := i - 256`. -/
def identityStep : List Instr :=
  [.add .r12 .r3 .r6, .stb .r6 .r12 0, .addi .r6 .r6 1, .li .r12 256, .sub .r12 .r6 .r12]

/-- `j += S[i] + key[off]`, the swap, then the next key offset (0 at the key
length, without a branch) and `i`; `r12 := i - 256`. -/
def scheduleStep : List Instr :=
  loadI ++ ([.add .r9 .r9 .r0, .add .r12 .r7 .r5, .lbz .r0 .r12 0, .add .r9 .r9 .r0,
    .lsl .r9 .r9 56, .lsr .d .r9 .r9 56] : List Instr) ++ replace ++
    ([.add .r12 .r3 .r6, .stb .r10 .r12 0,
      .addi .r5 .r5 1, .sub .r12 .r5 .r4, .subi .r0 .r12 1, .logic .xor .r0 .r0 .r12,
      .lsr .d .r12 .r0 63, .subi .r12 .r12 1, .logic .and .r5 .r5 .r12,
      .addi .r6 .r6 1, .li .r12 256, .sub .r12 .r6 .r12] : List Instr)

/-- Key scheduling after the key-length check: the key to `r7`, the context
to `r3`. -/
def initValid : Prog isa :=
  .seq (.block [.logic .or .r7 .r3 .r3, .logic .or .r3 .r5 .r5, .li .r6 0])
    (.seq (.loop (.block identityStep) (.nonzero .d .r12))
      (.seq (.block [.li .r6 0, .li .r5 0, .li .r9 0, .li .r8 0])
        (.seq (.loop (.block scheduleStep) (.nonzero .d .r12))
          (.block [.li .r12 0, .stb .r12 .r3 256, .stb .r12 .r3 257, .li .r3 0]))))

/-- Checked key scheduling: `(key_len - 1) >> 8` is zero exactly for
`key_len` in 1..=256; invalid lengths return 1, valid lengths 0. -/
def init : Prog isa :=
  .seq (.block [.subi .r12 .r4 1, .lsr .d .r12 .r12 8])
    (.ite (.nonzero .d .r12) (.block [.li .r3 1]) initValid)

/-- One PRGA step: `i += 1`, `j += S[i]`, the swap, then the keystream byte
`S[S[i] + S[j]]` XORed into the next data byte. -/
def applyStep : List Instr :=
  ([.addi .r6 .r6 1, .lsl .r6 .r6 56, .lsr .d .r6 .r6 56] : List Instr) ++ loadI ++
    ([.add .r7 .r7 .r0, .lsl .r7 .r7 56, .lsr .d .r7 .r7 56, .logic .or .r9 .r7 .r7] :
      List Instr) ++ replace ++ loadI ++
    ([.stb .r10 .r12 0, .add .r9 .r10 .r0, .lsl .r9 .r9 56, .lsr .d .r9 .r9 56] : List Instr) ++
    lookup ++
    ([.lbz .r0 .r4 0, .logic .xor .r0 .r0 .r10, .stb .r0 .r4 0, .addi .r4 .r4 1,
      .subi .r5 .r5 1] : List Instr)

/-- Streaming XOR, preserving the permutation and both PRGA indices. The
indices are loaded first. -/
def apply : Prog isa :=
  .seq (.block [.lbz .r6 .r3 256, .lbz .r7 .r3 257, .li .r8 0])
    (.ite (.zero .d .r5) (.block [])
      (.seq (.loop (.block applyStep) (.nonzero .d .r5))
        (.block [.stb .r6 .r3 256, .stb .r7 .r3 257])))

end VG.Impl.Rc4.PPC64LE
