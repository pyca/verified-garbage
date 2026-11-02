module

public import VerifiedGarbage.Impl.Rsa.Arm.Recover
public import VerifiedGarbage.Impl.MillerRabin.Arm.Arithmetic

/-!
# A prepared Miller–Rabin round on ARMv7

`vg_miller_rabin_round(ws, ws_len)` (`Proof/MillerRabin/Contract.lean`), in the compact
representation, with the frame of `vg_rsa_public_checked`: `r0`–`r12` and
`lr` pushed (56 bytes), so that frame word 0 holds `ws`, as Montgomery
multiplication (`montOp`) needs it.

The working space is read as the key working space of the RSA key
operations (`Impl/Rsa/Arm/KeyWs.lean`) with its base `r8 = ws + 96` and
`W = 2 w + 2` words of 32 bits: then its stride `4 (W + 2) = 8 (w + 2)` is
that of the 64-bit arrays, and its array `j` is the 64-bit array `j`. Its
header slots used here are the header words 23, 26, 29 and 30 of `ws`, which
the contract lets the round change.

Fixed windows of four bits over the prepared exponent `E = (c − 1) / 2^σ`
(array 27, `Proof/RsaKeyGen/MrWindow.lean`), as on AArch64:

1. The table `T_k = x^k` (`k < 16`, in Montgomery form, array `11 + k`):
   `T_0 := 1`, `T_1 := x` (copies of arrays 9 and 5), then 14 times
   `y := y x`, with each result copied directly to its final entry 2–15.
2. `y := 1` and, over the `16 w` windows of `E` from the top (its 32-bit
   words from the top, eight windows each, the word shifted left four bits
   a window), four squarings, each or'ing the flag with `y = −1`; `T_d` for
   the window's digit `d` selected into array 5 by a scan over all 16
   entries under masks, alternating with array 8; `y := y T_d`; and, if
   `d ≠ 0`, the flag set to `y = 1 ∨ y = −1`.
3. Three more squarings, each or'ing the flag with `y = −1` while fewer
   than `σ` of them are done: `4 − σ` from the word `2^(t mod 64)` after
   `E`'s words.

`−1` is copied into array 8 (its words above the `w` of 64 bits cleared, as
each product's and each table entry's are, so that the comparisons are of
numbers), again after each scan. The number of steps and every address
depend only on `w`.
-/

@[expose] public section

namespace VG.Impl.MillerRabin.Arm

open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Rsa.Arm.Keys

/-! ## The key working space's view -/

/-- The key working space's base: `ws + 96`. -/
def kOff : Nat := 96

/-- `r8 := ws + 96`, `r9 := W = 2 w + 2` and `r7 :=` the stride, from `ws` in
`r0`. -/
def ctx : List Instr :=
  [.dp .add .r8 .r0 (.imm (BitVec.ofNat 32 kOff)), .ldr .r9 .r0 48, .mov .r9 (.shifted .r9 .lsl 1),
    .dp .add .r9 .r9 (.imm 2)] ++ stride

/-! ## Slots: offsets from `r8`, in the header words 23, 26, 29 and 30 of `ws` -/

/-- The comparisons' results (`sE1` also the scan's mask). -/
def sE1 : Nat := 88
def sE2 : Nat := 92
/-- The word of `E` being scanned, shifted left four bits a window. -/
def sV : Nat := 116
/-- The flag. -/
def sF : Nat := 136
/-- The count of the table's entries, then of the windows left. -/
def sK : Nat := 140
/-- The count of a run of squarings, and its threshold. -/
def sQ : Nat := 144
def sR : Nat := 148

/-! ## Arrays -/

/-- The witness (in Montgomery form), the multiplicand and a temporary. -/
def aX : Nat := 5
/-- `y`. -/
def aY : Nat := 6
/-- `−1` (Montgomery form), copied; the scan's other array. -/
def aM1 : Nat := 8
/-- The table: entry `k` is array `aT0 + k`. -/
def aT0 : Nat := 11
/-- The prepared exponent. -/
def aE : Nat := 27

/-! ## Pieces -/

/-- `[o] := [a]`, its words above the low `2 w` cleared. -/
def copyClr (o a : Nat) : List (Prog isa) := [copy o a, .block (Rsa.Arm.Recover.clrTop o)]

/-- `[aY] := [aY] [b] R⁻¹ mod c`, then the context and `[aY]`'s top words cleared. -/
def mulY (b : Nat) (fios : Bool := false) : List (Prog isa) :=
  [.block [.ldrSp .r0 0], Arithmetic.product fios aY aY b, .block (ctx ++ Rsa.Arm.Recover.clrTop aY)]

/-- `[aY] := [aY]² R⁻¹ mod c` by the dedicated square, then the context and `[aY]`'s top
words cleared. -/
def sqY (fios : Bool := false) : List (Prog isa) :=
  [.block [.ldrSp .r0 0], Arithmetic.square fios aY aY, .block (ctx ++ Rsa.Arm.Recover.clrTop aY)]

/-- The count decremented: Z when it reaches 0. -/
def cntNext : List Instr := [.ldr .r1 .r8 sK, .subs .r1 .r1 (.imm 1), .str .r1 .r8 sK]

/-! ## The table -/

/-- The count of the table's entries. -/
def tabCnt : List Instr := [.mov .r1 (.imm 14), .str .r1 .r8 sK]

/-- The context, `T_0 := 1`, `x`'s top words cleared, `T_1 := x`, `y := x`
and the count. -/
def tabInit : List (Prog isa) :=
  [.block ctx, seqs (copyClr aT0 9), .block (Rsa.Arm.Recover.clrTop aX), copy (aT0 + 1) aX, copy aY aX,
    .block tabCnt]

/-- Address the final slot directly from the public number of entries left. -/
def tabCopyArgs : List Instr :=
  [.mov .r0 (.imm 27), .dp .sub .r0 .r0 (.reg .lr), .mla .r0 .r0 .r7 .r8, .dp .add .r0 .r0 (.imm (BitVec.ofNat 32 hdr))]

def tabCopyStore : Prog isa :=
  .seq (.block (tabCopyArgs ++ ptr .r10 aY ++ ptr .r12 aY ++
    [.mov .lr (.reg .r9), .mov .r11 (.imm 0)])) copyWords

def tabCopy : Prog isa := .seq (.block [.ldr .lr .r8 sK]) tabCopyStore

/-- One product and one final-slot copy, keeping the arithmetic in a loop. -/
def tabStep (fios : Bool := false) : Prog isa :=
  seqs [seqs (mulY (fios := fios) aX), tabCopy, .block cntNext]

def tabBuild (fios : Bool := false) : Prog isa := .loop (tabStep (fios := fios)) .ne

/-! ## Squarings -/

/-- The flag or'ed with `y = −1` (`sE2`) if the threshold `sR` is below the
count `sQ`; the count decremented, Z when it reaches 0. -/
def sqFlag : List Instr :=
  [.ldr .r1 .r8 sQ, .ldr .r2 .r8 sR, .dp .sub .r2 .r2 (.reg .r1), .mov .r2 (.shifted .r2 .lsr 31),
    .ldr .r3 .r8 sE2, .dp .and .r3 .r3 (.reg .r2), .ldr .r4 .r8 sF, .dp .orr .r4 .r4 (.reg .r3),
    .str .r4 .r8 sF, .subs .r1 .r1 (.imm 1), .str .r1 .r8 sQ]

/-- A squaring. -/
def sqStep (fios : Bool := false) : Prog isa := seqs [seqs (sqY (fios := fios)), eqS sE2 aY aM1 aX, .block sqFlag]

/-- `sQ` squarings. -/
def sqLoop (fios : Bool := false) : Prog isa := .loop (sqStep (fios := fios)) .ne

/-! ## The scan -/

/-- `sE1 :=` the mask of the digit `d = sV >> 28` being `j`. -/
def maskJ (j : Nat) : List Instr :=
  [.ldr .r1 .r8 sV, .mov .r1 (.shifted .r1 .lsr 28), .dp .eor .r1 .r1 (.imm (BitVec.ofNat 32 j)),
    .dp .sub .r1 .r1 (.imm 1), .mov .r1 (.shifted .r1 .lsr 31), .str .r1 .r8 sE1]

/-- The array holding the selection after entry `j`. -/
def hold (j : Nat) : Nat := if j % 2 = 1 then aX else aM1

/-- The entries `j, …, j + n − 1`: `T_j` into `hold j` if the digit is `j`,
else the selection so far. -/
def scanFrom : Nat → Nat → Prog isa
  | _, 0 => .block []
  | j, n + 1 => .seq (.block (maskJ j)) (.seq (sel (hold j) (hold (j + 1)) (aT0 + j) sE1) (scanFrom (j + 1) n))

/-- `[aX] := T_d`. -/
def scan : Prog isa := .seq (copy aM1 aT0) (scanFrom 1 15)

/-! ## The windows -/

/-- The flag: `y = 1 ∨ y = −1` if the digit is not 0; the word shifted to the
next digit, and the count of windows decremented: Z at the word's end. -/
def winEnd : List Instr :=
  [.ldr .r1 .r8 sV, .mov .r2 (.shifted .r1 .lsr 28), .dp .sub .r2 .r2 (.imm 1), .mov .r2 (.shifted .r2 .lsr 31),
    .dp .eor .r3 .r2 (.imm 1), .ldr .r4 .r8 sE1, .ldr .r5 .r8 sE2, .dp .orr .r4 .r4 (.reg .r5),
    .dp .and .r4 .r4 (.reg .r3), .ldr .r5 .r8 sF, .dp .and .r5 .r5 (.reg .r2), .dp .orr .r4 .r4 (.reg .r5),
    .str .r4 .r8 sF, .mov .r1 (.shifted .r1 .lsl 4), .str .r1 .r8 sV,
    .ldr .r1 .r8 sK, .dp .sub .r1 .r1 (.imm 1), .str .r1 .r8 sK, .dp .and .r1 .r1 (.imm 7), .cmp .r1 (.imm 0)]

/-- Four squarings' count and threshold. -/
def sqFour : List Instr := [.mov .r1 (.imm 0), .str .r1 .r8 sR, .mov .r1 (.imm 4), .str .r1 .r8 sQ]

/-- One window. -/
def win (fios : Bool := false) : Prog isa := seqs [.block sqFour, (sqLoop (fios := fios)), scan, seqs (copyClr aM1 10), seqs (mulY (fios := fios) aX),
  eqS sE1 aY aT0 aX, eqS sE2 aY aM1 aX, .block winEnd]

/-- The count of windows left. -/
def wordK : List Instr := [.ldr .r1 .r8 sK]

/-- The word `K / 8 − 1` of `E`, for the count `K` in `r1`, into `sV`. -/
def wordLd : List Instr :=
  ptr .r0 aE ++ [.mov .r1 (.shifted .r1 .lsr 3), .dp .sub .r1 .r1 (.imm 1), .dp .add .r0 .r0 (.shifted .r1 .lsl 2),
    .ldr .r2 .r0 0, .str .r2 .r8 sV]

/-- Z when no window is left. -/
def wordEnd : List Instr := [.ldr .r1 .r8 sK, .cmp .r1 (.imm 0)]

/-- A word's eight windows; Z when none is left. -/
def word (fios : Bool := false) : Prog isa := seqs [.block wordK, .block wordLd, .loop (win (fios := fios)) .ne, .block wordEnd]

/-- The flag 0 and the count of windows `16 w = 8 W − 16`. -/
def winCnt : List Instr :=
  [.mov .r1 (.imm 0), .str .r1 .r8 sF, .mov .r1 (.shifted .r9 .lsl 3), .dp .sub .r1 .r1 (.imm 16), .str .r1 .r8 sK]

/-- `−1` copied, `y := 1`, the flag and the count. -/
def winInit : List (Prog isa) := [seqs (copyClr aM1 10), copy aY aT0, .block winCnt]

/-! ## The last squarings -/

/-- The threshold `4 − σ` from the word `2^(t mod 64)` after `E`'s (its
32-bit halves or'ed, folded to four bits), and the count 3. -/
def lowBits : List Instr :=
  ptr .r0 aE ++ [.dp .add .r0 .r0 (.shifted .r9 .lsl 2), .dp .sub .r0 .r0 (.imm 8), .ldr .r1 .r0 0, .ldr .r2 .r0 4,
    .dp .orr .r1 .r1 (.reg .r2), .dp .orr .r1 .r1 (.shifted .r1 .lsr 16), .dp .orr .r1 .r1 (.shifted .r1 .lsr 8),
    .dp .orr .r1 .r1 (.shifted .r1 .lsr 4),
    .mov .r2 (.shifted .r1 .lsr 1), .dp .and .r2 .r2 (.imm 1),
    .mov .r3 (.shifted .r1 .lsr 2), .dp .and .r3 .r3 (.imm 1),
    .mov .r4 (.shifted .r1 .lsr 3), .dp .and .r4 .r4 (.imm 1),
    .dp .add .r4 .r4 (.reg .r2), .dp .add .r4 .r4 (.shifted .r2 .lsl 1), .dp .add .r4 .r4 (.shifted .r3 .lsl 1),
    .str .r4 .r8 sR, .mov .r1 (.imm 3), .str .r1 .r8 sQ]

/-! ## The round -/

/-- The round's body: the flag returned in `r0`. -/
def body (fios : Bool := false) : Prog isa :=
  seqs [seqs tabInit, tabBuild (fios := fios), seqs winInit, .loop (word (fios := fios)) .ne, .block lowBits, (sqLoop (fios := fios)),
    .block [.ldr .r0 .r8 sF]]

/-- `vg_miller_rabin_round`. -/
def code (fios : Bool := false) : Prog isa :=
  .frame (.push [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr])
    (.seq (body (fios := fios)) (.block PcFn.restore)) (.pop .r12 56)

end VG.Impl.MillerRabin.Arm
