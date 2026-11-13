module

public import VerifiedGarbage.Impl.Rsa.Arm.KeyFrame
public import VerifiedGarbage.Impl.Rsa.Arm.KeyDiv
public import VerifiedGarbage.Impl.Bignum.Arm.MaskRow
public import VerifiedGarbage.Impl.Bignum.Arm.ShiftK
public import VerifiedGarbage.Impl.Bignum.Arm.UmaalArithmetic

/-! # RSA prime recovery by SP 800-56B Rev. 2 Appendix C.2 on ARMv7

`vg_rsa_recover_primes_det`'s frame, entry and exits (`Recover.codeWith`,
`KeyFrame.lean`), its loads (`Recover.loads`), and its stores of the factors under
the mask (`Recover.stores`), in the key working space with `w` words
(narrow) and `W = 2 w + 2` words (wide, whose array `j` is the narrow arrays
`2 j` and `2 j + 1`). Between them, Appendix C.2 without a branch on a
secret:

* `M = d e` (wide) by a row of words for each of `e`'s `⌈e_len / 4⌉` (`prodW`);
* `x = d e - 1` (wide), and whether `d e ≥ 2` (`sOkDE`);
* the trailing zeros of `u = n - 1` and of the low half of `x` (narrow),
  `k` the smaller, and `u` and `x` shifted down by theirs, `x` by `k`, in
  stages of `2^i` bits and of `2^m` words chosen by masks (`twos`): `u` odd
  and `gcd(n - 1, x) = 2^k gcd(u, x / 2^k)`;
* `gcd(u, x / 2^k)` by `gcdOnly`, at the width `w`, with the odd modulus
  `u` (`1` where `u = 1`, which `gcdOnly` does not take);
* `a = (2^k x) gcd(u, x / 2^k)` by rows of words (`rowProd`);
* `m = ⌊a / n⌋` and `r = a mod n` (by word quotients on the wide arrays,
  `divA`), whether `m < n`, and `b - 1 = (n - r) / (m + 1)` with its
  remainder (`divB`; a divisor `m + 1` that is zero modulo `2^(32 w)`, which
  only `m ≥ n` gives, is replaced by 1);
* `b² - 4 n` (`rowProd` again), whether it is positive, and its integer
  square root by words from the top (`sqrt`: `X` normalized, a digit per
  two words), with whether the remainder is 0;
* `p = (b + ϒ) / 2` and `q = (b - ϒ) / 2`, written under the mask of every
  check.

Sums are differences with a negation (`add`). Every loop's count is a
public length, and every address is computed from `r7`, `r8` and `r9`.
-/

@[expose] public section

namespace VG.Impl.Rsa.Arm.RecoverDet
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Rsa.Arm.Keys
open VG.Impl.Rsa.Arm.Recover (ctxw clrW aW)

/-! ## Header words

Bytes 0–19 are the division's (16: `w`), 100–112 the shared routines', and
132 the mask of the result. -/

/-- `d e < 1`, `d e - 1 < 1`, and `d e ≥ 2`. -/
def sB0 : Nat := 20
def sB1 : Nat := 24
def sOkDE : Nat := 28
/-- A product's multiplier bit. -/
def sY : Nat := 48
/-- `m < n`, `(n - r) mod (m + 1) = 0`. -/
def sLt : Nat := 52
def sExact : Nat := 56
/-- `b² < 4 n`, `b² - 4 n < 1`, and `b² > 4 n`. -/
def sC1 : Nat := 60
def sC2 : Nat := 64
def sOk4 : Nat := 128
/-- The remainder of the square root is zero. -/
def sOk5 : Nat := 76
/-- A loop's count. -/
def sK : Nat := 80
/-- `u = 1`. -/
def sU1 : Nat := 84
/-- `m + 1` is zero modulo `2^(32 w)`. -/
def sM0 : Nat := 88
def sMask : Nat := VG.Impl.Rsa.Arm.Recover.sMask

/-! ## Arrays

Wide: `d e` (`Recover.wM`), zero, one, `x`, `2^k x`, two temporaries, the
product, `n` widened, the remainder, the division's temporary and `b`
widened. -/

def wZ : Nat := 14
def wOne : Nat := 13
def wX : Nat := 10
def wX3 : Nat := 11
def wT1 : Nat := 12
def wT2 : Nat := 15
def wA : Nat := 9
def wN : Nat := 17
def wR : Nat := 19
def wDt : Nat := 18
def wB : Nat := 10

/-- Narrow: `n` (`Recover.aN`), zero, one, two temporaries, `u` (the GCD's
modulus `aM`), the halved `x` (the low half of `wX`), the GCD's input and
result, the multiplier of the first product, `m mod 2^(32 w)` (the low half
of `wA`), `m + 1`, `n - r` (then the quotient), `r mod 2^(32 w)` (the low
half of `wR`), the division's remainder and temporary, `b`, its copy for the
second product, and the square root's root. -/
def aN : Nat := VG.Impl.Rsa.Arm.Recover.aN
def aZN : Nat := 40
def aOneN : Nat := 41
def aT1 : Nat := 36
def aT2 : Nat := 37
def aU : Nat := 8
def aX2 : Nat := 20
def aGx : Nat := 0
def aG1 : Nat := 1
def aG : Nat := 34
def aMlo : Nat := 18
def aM1 : Nat := 22
def aD : Nat := 24
def aRlo : Nat := 38
def aRem : Nat := 2
def aDt : Nat := 3
def aB : Nat := 4
def aBy : Nat := 5
def aY : Nat := 7
/-- The factors, as `Recover.stores` takes them. -/
def aP : Nat := 5
def aQ : Nat := 6

/-! ## Small operations -/

/-- The slot `d` := `r11` (a borrow). -/
def brw (d : Nat) : List Instr := [.str .r11 .r8 d]

/-- The slot `d` := the slot `a` negated (a bit). -/
def notS (d a : Nat) : List Instr := [.ldr .r1 .r8 a, .dp .eor .r1 .r1 (.imm 1), .str .r1 .r8 d]

/-- The slot `d` := neither the slot `a` nor `b` (bits). -/
def norS (d a b : Nat) : List Instr :=
  [.ldr .r1 .r8 a, .ldr .r2 .r8 b, .dp .orr .r1 .r1 (.reg .r2), .dp .eor .r1 .r1 (.imm 1), .str .r1 .r8 d]

/-- From the narrow arrays to the wide ones: `r9 := 2 r9 + 2` and its
stride, from registers alone. -/
def toW : List Instr := [.mov .r9 (.shifted .r9 .lsl 1), .dp .add .r9 .r9 (.imm 2)] ++ stride

/-- From the wide arrays to the narrow ones: `r9 := (r9 - 2) / 2`. -/
def toN : List Instr := [.dp .sub .r9 .r9 (.imm 2), .mov .r9 (.shifted .r9 .lsr 1)] ++ stride

/-- `r11 := 0`. -/
def clr11 : List Instr := [.mov .r11 (.imm 0)]

/-- `[j] := 2 [j] + r11` modulo `2^(32 lr)` over its low `lr` words, the bit shifted out in `r11`. -/
def shlN (j : Nat) : Prog isa := .seq (.block (ptr .r0 j)) shiftLeft

/-- `shlN` over the width. -/
def shl (j : Nat) : Prog isa := .seq (.block [.mov .lr (.reg .r9)]) (shlN j)

/-- `[o] := [a] + [b]` modulo the width, through `t`: `[a] - (0 - [b])`. -/
def add (o a b t z : Nat) : Prog isa := .seq (sub3 t z b) (sub3 o a t)

/-- The count less one, and Z if it is zero. -/
def cntNext : List Instr := [.ldr .r1 .r8 sK, .subs .r1 .r1 (.imm 1), .str .r1 .r8 sK]

/-! ## Shifts by public words -/

/-- `shiftUp`'s copy from `4 s` in `r1` and `[o]`'s address in `r0`, over the `lr` low words. -/
def shiftUpBN (a : Nat) : Prog isa :=
  .seq (.block ([.dp .add .r0 .r0 (.reg .r1)] ++ ptr .r10 a ++ [.mov .r12 (.reg .r10),
    .dp .sub .lr .lr (.shifted .r1 .lsr 2), .mov .r11 (.imm 0)])) copyWords

/-- `shiftUpBN` over the width. -/
def shiftUpB (a : Nat) : Prog isa := .seq (.block [.mov .lr (.reg .r9)]) (shiftUpBN a)

/-- `[o] := [a] 2^(32 s)` modulo `2^(32 W)` (wide), for `4 s` at the header word `d`. A block ends
after the load of `4 s`. -/
def shiftUpBy (d o a : Nat) : Prog isa := seqs [copy o wZ, .block (ptr .r0 o ++ [.ldr .r1 .r8 d]), shiftUpB a]

/-- `shiftDown`'s copy from `4 s` in `r1` and `[a]`'s address in `r10`. -/
def shiftDownB (o : Nat) : Prog isa :=
  .seq (.block ([.dp .add .r10 .r10 (.reg .r1), .mov .r12 (.reg .r10)] ++ ptr .r0 o ++ [.mov .lr (.reg .r9),
    .dp .sub .lr .lr (.shifted .r1 .lsr 2), .mov .r11 (.imm 0)])) copyWords

/-- `[o] := ⌊[a] / 2^(32 s)⌋` for `4 s` at `d`, `z` the context's zero array. A block ends after the
load of `4 s`. -/
def shiftDownBy (z d o a : Nat) : Prog isa :=
  seqs [copy o z, .block (ptr .r10 a ++ [.ldr .r1 .r8 d]), shiftDownB o]

/-! ## `d e - 1` -/

def deMinus : Prog isa := seqs [sub3 wZ VG.Impl.Rsa.Arm.Recover.wM VG.Impl.Rsa.Arm.Recover.wM,
  copy wOne wZ, .block (setOne wOne),
  sub3 wX VG.Impl.Rsa.Arm.Recover.wM wOne, .block (brw sB0),
  sub3 wT1 wX wOne, .block (brw sB1 ++ norS sOkDE sB0 sB1)]

/-! ## The halvings -/

/-- Zero and one narrow, `u = n - 1`, and `2^k x := x`. -/
def twosInit : Prog isa := seqs [copy wX3 wX, .block toN, sub3 aZN aN aN, copy aOneN aZN,
  .block (setOne aOneN), sub3 aU aN aOneN]


/-! ### The halvings by shifts: `tu = ctz u`, `k = min(tu, ctz x₂)`, then `u >>= tu`, `x₂ >>= k` and
`2^k x := x << k`, by stages of masked shifts of `2^i` bits. -/

def sTu : Nat := 136
def sKx : Nat := 140
def sKv : Nat := 144
def sBit : Nat := 148
def sCa : Nat := 152
def sCd : Nat := 156
def sWs : Nat := 116
def sTk : Nat := 120
def sKk : Nat := 124

/-- `r1 := 1` if `r1 ≠ 0`, else 0 (through `r2`). -/
def nzR1 : List Instr :=
  [.mov .r2 (.imm 0), .dp .sub .r2 .r2 (.reg .r1), .dp .orr .r1 .r1 (.reg .r2), .mov .r1 (.shifted .r1 .lsr 31)]

/-- A bit of the trailing zeros: the low bit of `r6` into the flag `r5` (a bit seen), the count `r4` one
more while none was; `r6` halved, `r12` the bits left. -/
def ctzBit : List Instr :=
  [.dp .and .r1 .r6 (.imm 1), .dp .orr .r5 .r5 (.reg .r1), .dp .eor .r1 .r5 (.imm 1), .dp .add .r4 .r4 (.reg .r1),
   .mov .r6 (.shifted .r6 .lsr 1), .subs .r12 .r12 (.imm 1)]

/-- A word of the trailing zeros, from its address in `r0`; `lr` the words left. -/
def ctzWord : Prog isa := seqs [.block [.ldr .r6 .r0 0, .dp .add .r0 .r0 (.imm 4), .mov .r12 (.imm 32)],
  .loop (.block ctzBit) .ne, .block [.subs .lr .lr (.imm 1)]]

/-- The trailing zeros of `[j]` (`32 w` for zero) into the slot `d`, a bit at a time. -/
def ctz (j d : Nat) : Prog isa := seqs [
  .block (ptr .r0 j ++ [.mov .lr (.reg .r9), .mov .r4 (.imm 0), .mov .r5 (.imm 0)]),
  .loop ctzWord .ne, .block [.str .r4 .r8 d]]

/-- `r11 := 0` and the slot `sK` cleared, as the shifts by `k` bits leave it. -/
def clrK : List Instr := [.mov .r11 (.imm 0), .str .r11 .r8 sK]

/-- `[j] := ⌊([j] + r11 · 2^(32 w)) / 2^k⌋`, narrow: `r11` stored as word `w`, then one shift by `k`. -/
def halfKN (j k : Nat) : Prog isa :=
  .seq (.block (ptr .r0 j ++ [.dp .add .r1 .r0 (.shifted .r9 .lsl 2), .str .r11 .r1 0, .mov .lr (.reg .r9)]))
    (shiftRightK k)

/-- `[j] := ⌊[j] / 2^k⌋`, narrow, `0 < k < 32`. -/
def halfK (j k : Nat) : Prog isa := .seq (.block clrK) (halfKN j k)

/-- `[j] := 2^k [j] + r11` modulo `2^(32 W)`, wide, the bits shifted out in `r11`. -/
def shlKN (j k : Nat) : Prog isa := .seq (.block (.mov .lr (.reg .r9) :: ptr .r0 j)) (shiftLeftK k)

/-- `[j] := [j] 2^k` modulo `2^(32 W)`, wide, `0 < k < 32`. -/
def shlK (j k : Nat) : Prog isa := .seq (.block clrK) (shlKN j k)

/-- Bit `i` of the slot `src` into `sBit`. -/
def bitTo (src i : Nat) : List Instr :=
  [.ldr .r1 .r8 src] ++ (if i = 0 then [] else [.mov .r1 (.shifted .r1 .lsr i)]) ++
    [.dp .and .r1 .r1 (.imm 1), .str .r1 .r8 sBit]

/-- The stage of `2^i` bits, `i < 5`. -/
def bitStage (i : Nat) : Prog isa := seqs [
  .block (bitTo sTu i), copy aT1 aU, halfK aT1 (2 ^ i), sel aT2 aU aT1 sBit, copy aU aT2,
  .block (bitTo sKv i), copy aT1 aX2, halfK aT1 (2 ^ i), sel aT2 aX2 aT1 sBit, copy aX2 aT2,
  .block toW, copy wT1 wX3, shlK wT1 (2 ^ i), sel wT2 wX3 wT1 sBit, copy wX3 wT2, .block toN]

/-- `[o] := ⌊[a] / 2^(32 s)⌋` (`4 s` at `sWs`), narrow. -/
def shrW (o a : Nat) : Prog isa := shiftDownBy aZN sWs o a

/-- A stage of `s` words, `s` doubling while below `w`. -/
def wordStage : Prog isa := seqs [
  .block [.ldr .r1 .r8 sTk, .dp .and .r1 .r1 (.imm 1), .str .r1 .r8 sBit], shrW aT1 aU, sel aT2 aU aT1 sBit,
  copy aU aT2,
  .block [.ldr .r1 .r8 sKk, .dp .and .r1 .r1 (.imm 1), .str .r1 .r8 sBit], shrW aT1 aX2, sel aT2 aX2 aT1 sBit,
  copy aX2 aT2,
  .block toW, shiftUpBy sWs wT1 wX3, sel wT2 wX3 wT1 sBit, copy wX3 wT2, .block toN,
  .block [.ldr .r1 .r8 sTk, .mov .r1 (.shifted .r1 .lsr 1), .str .r1 .r8 sTk,
    .ldr .r1 .r8 sKk, .mov .r1 (.shifted .r1 .lsr 1), .str .r1 .r8 sKk,
    .ldr .r1 .r8 sWs, .mov .r1 (.shifted .r1 .lsl 1), .str .r1 .r8 sWs,
    .dp .sub .r1 .r1 (.shifted .r9 .lsl 2), .mov .r1 (.shifted .r1 .lsr 31), .cmp .r1 (.imm 0)]]

/-- `k = min(tu, kx)`, and the word stages' start. -/
def kMin : List Instr :=
  [.ldr .r1 .r8 sTu, .ldr .r2 .r8 sKx, .dp .sub .r3 .r2 (.reg .r1), .mov .r4 (.shifted .r3 .lsr 31),
   .mov .r5 (.imm 0), .dp .sub .r4 .r5 (.reg .r4), .dp .and .r3 .r3 (.reg .r4), .dp .add .r1 .r1 (.reg .r3),
   .str .r1 .r8 sKv, .mov .r1 (.shifted .r1 .lsr 5), .str .r1 .r8 sKk,
   .ldr .r1 .r8 sTu, .mov .r1 (.shifted .r1 .lsr 5), .str .r1 .r8 sTk, .mov .r1 (.imm 4), .str .r1 .r8 sWs]

def twos : Prog isa := seqs [twosInit, ctz aU sTu, ctz aX2 sKx, .block kMin,
  bitStage 0, bitStage 1, bitStage 2, bitStage 3, bitStage 4, .loop wordStage .ne]

/-! ## The GCD -/

/-- `gcd(u, x / 2^k)` into `aG`: `gcdOnly`'s, or 1 where `u = 1`. -/
def gcdPost : Prog isa := .seq (eqS sU1 aU aOneN aW) (sel aG aG1 aOneN sU1)

def gcd (um : Bool := false) : Prog isa := seqs [copy aGx aX2, gcdOnly um, gcdPost]

/-! ## Products by rows: `[o] := [x] y` modulo `2^(32 W)`, wide, for `y` the narrow array `2 Y` (the low
`w` words of the wide `Y`): a row per word of `y`. -/

/-- Row `i` (`4 i` at `sK`) of `[o] += y_i [x]` over the `W - i` words from word `i`, the carry
dropped; then the next row, `Z` after the `w`-th. A block ends after the load of the offset. -/
def pRowA (o : Nat) : List Instr := ptr .r0 o ++ [.ldr .r2 .r8 sK]

/-- The rest of the row, from the offset in `r2` and `[o]`'s address in `r0`; `cnt` puts `4` times the
number of rows into `r1`. -/
def pRowBG (x Y : Nat) (cnt : List Instr) : Prog isa :=
  .seq (.block ([.dp .add .r0 .r0 (.reg .r2)] ++ ptr .r12 x ++
      [.mov .r3 (.shifted .r2 .lsr 2), .dp .sub .lr .r9 (.reg .r3)] ++ ptr .r1 Y ++
      [.dp .add .r1 .r1 (.reg .r2), .ldr .r1 .r1 0, .mov .r11 (.imm 0)]))
    (.seq row (.block (VG.Impl.Rsa.Arm.Recover.ctxW ++ [.ldr .r0 .r8 sK, .dp .add .r0 .r0 (.imm 4), .str .r0 .r8 sK] ++
      cnt ++ [.cmp .r0 (.reg .r1)])))

/-- `4 w`: a row for each of the narrow `y`'s words. -/
def cntW : List Instr := [.ldr .r1 .r8 16, .mov .r1 (.shifted .r1 .lsl 2)]

def pRowB (x Y : Nat) : Prog isa := pRowBG x Y cntW

def pRowG (o x Y : Nat) (cnt : List Instr) : Prog isa := .seq (.block (pRowA o)) (pRowBG x Y cnt)

def pRow (o x Y : Nat) : Prog isa := pRowG o x Y cntW

/-- From the narrow context, back to it. -/
def rowsInit : List Instr := [.mov .r0 (.imm 0), .str .r0 .r8 sK]

def rowProdG (o x Y : Nat) (cnt : List Instr) : Prog isa :=
  seqs [.block toW, copy o wZ, .block rowsInit, .loop (pRowG o x Y cnt) .ne, .block toN]

def rowProd (o x Y : Nat) : Prog isa := rowProdG o x Y cntW

/-- The rows of `d e`: `4 ⌈e_len / 4⌉`, set before them. -/
def sRows : Nat := 92

/-- `4 ⌈e_len / 4⌉` at `sRows`: `e_len`, then its words. -/
def rowsE : Prog isa := seqs [.block [.ldrSp .r1 VG.Impl.Rsa.Arm.Recover.aoEl],
  .block [.dp .add .r1 .r1 (.imm 3), .mov .r1 (.shifted .r1 .lsr 2), .mov .r1 (.shifted .r1 .lsl 2), .str .r1 .r8 sRows]]

/-- A row for each of `e`'s words. -/
def cntE : List Instr := [.ldr .r1 .r8 sRows]

/-- `M := d e` (wide), by a row for each of `e`'s `⌈e_len / 4⌉` words, from the narrow context after the
loads into the wide one. -/
def prodW : Prog isa := seqs [rowsE, rowProdG VG.Impl.Rsa.Arm.Recover.wM VG.Impl.Rsa.Arm.Recover.wD
  VG.Impl.Rsa.Arm.Recover.wE cntE, .block toW]

/-! ## The divisions -/


/-- `w = (W - 2) / 2` back in the header, and the narrow context. -/
def restoreW : List Instr :=
  [.ldr .r9 .r8 16, .dp .sub .r9 .r9 (.imm 2), .mov .r9 (.shifted .r9 .lsr 1), .str .r9 .r8 16] ++ stride

/-- `n` widened, in the wide context. -/
def divAPre : Prog isa := seqs [.block toW, copy wN wZ, .block toN, copy (2 * wN) aN, .block toW]

/-- `4 s` for the shift `s = W / 2 - ⌈n_len / 4⌉` that puts `n`'s top word at word `W / 2 - 1`. -/
def sS : Nat := 92

/-- `4 s` from `n_len` in `r1`. -/
def shiftAmtB : List Instr :=
  [.dp .add .r1 .r1 (.imm 3), .mov .r1 (.shifted .r1 .lsr 2), .mov .r0 (.shifted .r9 .lsl 1),
    .dp .sub .r0 .r0 (.shifted .r1 .lsl 2), .str .r0 .r8 sS]

def shiftAmt : Prog isa := .seq (.block [.ldrSp .r1 VG.Impl.Rsa.Arm.Recover.aoK]) (.block shiftAmtB)

/-- `[o] := [a] 2^(32 s)` modulo `2^(32 W)` (wide), `s` the shift. -/
def shiftUp (o a : Nat) : Prog isa := shiftUpBy sS o a


/-- `[o] := ⌊[a] / 2^(32 s)⌋` (wide). A block ends after the load of `4 s`. -/
def shiftDown (o a : Nat) : Prog isa := shiftDownBy wZ sS o a

/-- Whether `a` is below `2^(32 (W - s))`, so that the shifted division is exact. -/
def sAok : Nat := 96

/-- `m` and `r` by words (`KeyDiv.divW` with the quotient into `wA`): `a` and `n` shifted up by `s`
words, `a` below `2^(32 (W - s))` or the flag `sAok` clear; `W` in the header for the division. -/
def divAW : Prog isa := seqs [shiftAmt,
  shiftUp 3 wA, shiftDown 12 3, eqS sAok wA 12 18,
  shiftUp 15 wN, copy 0 wZ, copy wA wZ, .block [.str .r9 .r8 16],
  VG.Impl.Rsa.Arm.KeyDiv.divW 3 12 15 18 10 11 none (some wA), .block restoreW]

/-- `r` shifted back down; whether `m < n` and `sAok`. -/
def divAPost : Prog isa := seqs [.block toW, shiftDown wR 12, sub3 wT1 wA wN,
  .block (brw sLt ++ andS sLt sLt sAok ++ toN)]

def divA : Prog isa := seqs [divAPre, divAW, divAPost]

/-- `m + 1` (1 where it is zero modulo `2^(32 w)`, so that the divisor is
positive) and `n - r`. -/
def divBPre : Prog isa := seqs [sub3 aT2 aZN aOneN, sub3 aT1 aMlo aT2, eqS sM0 aT1 aZN aW,
  sel aM1 aT1 aOneN sM0, sub3 aD aN aRlo]

/-! ### `(n - r) / (m + 1)` by words: both shifted left by `s' = W / 2 - wl(m + 1)` words (secret, by
masked stages of `2^k` words), so that the divisor's top word is word `W / 2 - 1`. -/

/-- A word of the word length: where the word is not zero, its index plus one (counted at `sCd`)
into `sCa`; the pointer `r0` and the count `lr` on. -/
def wlStep : List Instr :=
  [.ldr .r1 .r0 0, .dp .add .r0 .r0 (.imm 4)] ++ nzR1 ++
  [.ldr .r2 .r8 sCd, .dp .add .r2 .r2 (.imm 1), .str .r2 .r8 sCd, .mov .r3 (.imm 0), .dp .sub .r1 .r3 (.reg .r1),
   .ldr .r3 .r8 sCa, .dp .bic .r3 .r3 (.reg .r1), .dp .and .r2 .r2 (.reg .r1), .dp .orr .r3 .r3 (.reg .r2),
   .str .r3 .r8 sCa, .subs .lr .lr (.imm 1)]

/-- The word length of the narrow `[j]` into `sCa`. -/
def wlInit (j : Nat) : List Instr :=
  ptr .r0 j ++ [.mov .lr (.reg .r9), .mov .r1 (.imm 0), .str .r1 .r8 sCa, .str .r1 .r8 sCd]

/-- `s' = w + 1 - wl` into `sTk`, and `4` (a word) into `sWs`. -/
def shAmtW : List Instr :=
  [.ldr .r1 .r8 sCa, .dp .add .r2 .r9 (.imm 1), .dp .sub .r2 .r2 (.reg .r1), .str .r2 .r8 sTk,
   .mov .r1 (.imm 4), .str .r1 .r8 sWs]

/-- A stage of `2^k` words (`4 · 2^k` at `sWs`) of `s'` (its bit `k` the low bit of `sTk`) on the
wide `[j]` and `[j']`, through `[t]` and `[u]`; then `2^(k + 1)`, while below `W / 2`. -/
def wStage (j j' t u : Nat) : Prog isa := seqs [
  .block [.ldr .r1 .r8 sTk, .dp .and .r1 .r1 (.imm 1), .str .r1 .r8 sBit],
  shiftUpBy sWs t j, sel u j t sBit, copy j u, shiftUpBy sWs t j', sel u j' t sBit, copy j' u,
  .block [.ldr .r1 .r8 sTk, .mov .r1 (.shifted .r1 .lsr 1), .str .r1 .r8 sTk,
    .ldr .r1 .r8 sWs, .mov .r1 (.shifted .r1 .lsl 1), .str .r1 .r8 sWs,
    .dp .sub .r1 .r1 (.shifted .r9 .lsl 1), .mov .r1 (.shifted .r1 .lsr 31), .cmp .r1 (.imm 0)]]

/-- The word length `wl` of `m + 1`, and `s' = w + 1 - wl`. -/
def wlen : Prog isa := seqs [.block (wlInit aM1), .loop (.block wlStep) .ne, .block shAmtW]

/-- `m + 1` and `n - r` widened into `5` and `6`; the quotient's array `2` zero. -/
def widenB : Prog isa := seqs [.block toW, copy 5 wZ, copy 6 wZ, copy 2 wZ, .block toN, copy 10 aM1, copy 12 aD,
  .block toW]

/-- The division with the quotient into `2`. -/
def divBMid : Prog isa :=
  seqs [.block [.str .r9 .r8 16], VG.Impl.Rsa.Arm.KeyDiv.divW 6 7 5 8 15 21 none (some 2), .block restoreW]

/-- Whether the remainder is zero; `b - 1` the quotient's low half. -/
def divBEnd : Prog isa := seqs [.block toW, eqS sExact 7 wZ 18, .block toN, copy aD aB]

/-- `m + 1` and `n - r` widened into `5` and `6` and shifted by `s'` words; the division with the
quotient, and whether the remainder is zero; `b - 1` the quotient's low half. -/
def divBW : Prog isa := seqs [wlen, widenB, .loop (wStage 5 6 18 3) .ne, divBMid, divBEnd]

def divB : Prog isa := seqs [divBPre, divBW]

/-! ## `b² - 4 n` -/

/-- `b = q + 1`, narrow in `aB` and `aBy` and wide in `wB`, and `b²` in `wA`. -/
def squarePre : Prog isa := seqs [sub3 aT1 aZN aOneN, sub3 aB aD aT1, copy aBy aB,
  .block toW, copy wB wZ, .block toN, copy (2 * wB) aB]

def square : Prog isa := .seq squarePre (rowProd wA wB 2)

/-- `4 n`, `b² - 4 n` in `wR`, and whether `b² > 4 n`. -/
def minus4n : Prog isa := seqs [.block (toW ++ clr11), shl wN, .block clr11, shl wN,
  sub3 wR wA wN, .block (brw sC1), sub3 wT1 wR wOne, .block (brw sC2 ++ norS sOk4 sC1 sC2 ++ toN)]

/-! ## The square root

By words (`β = 2^32`), on the wide `X = [wR]` of `W` words, `X := 1` where it is 0: `X' = 4^c X` for
`c = ⌊lz / 2⌋`, `lz` the leading zeros of `X` (`lzW`), so that `X'`'s top word is at least `β / 4`
(`normX`); the root `s₀` of its top two words and their remainder, by pairs of bits in registers
(`firstDigit`); the reciprocal of `s₀` once (`KeyDiv.recip`). The root `s` of `X'`'s top `2 j` words is
kept as `D = 2 s`, top-aligned (its words `W / 2 - j` to `W / 2`), with its complement `C`, and the
remainder `r` in place of those words of `X'`. Then for each of the `W / 2 - 1` pairs `P` of words of
`X'` below, from the top, `R = r β² + P` (in place), the digit `q̂` estimated by dividing the three
words of `⌊R / 2⌋` above `s β`'s top two words by those (`KeyDiv.quot`, `KeyDiv.refine3`), so that
`q ≤ q̂ ≤ q + 2`; then `T = R - q̂ (2 s β + q̂)` in place by one row (`mulSubD`), and two corrections
`T += 2 s β + 2 q̂ - 1`, `q̂ -= 1` where `T < 0`, each a row adding `D'` under a mask (`correct`), and
`D := 2 s β + 2 q̂` (`finishQ`). `s = D / 2` and `r = [wR]` are then the root and the remainder of
`X'`; `X` is a square iff `r = 0`, and its root is `⌊s / 2^c⌋`, replaced by 0 where `X` was 0. -/

/-- `X = 0`, the offset of the next pair, the estimate's offset, and the leading zeros. -/
def sZ : Nat := 32
def sPo : Nat := 40
def sMo : Nat := 44
def sLz : Nat := 92

/-- The root, `D = 2 s`, its complement `C`, and two temporaries (wide). -/
def wS : Nat := 5
def wD : Nat := 7
def wE : Nat := 9
def wF : Nat := 10
def wG : Nat := 11

/-- A bit of the leading zeros: the top bit of `r6` into the flag `r5` (a bit seen), the count `r4`
one more while none was; `r6` doubled, `r12` the bits left. -/
def clzBit : List Instr :=
  [.mov .r1 (.shifted .r6 .lsr 31), .dp .orr .r5 .r5 (.reg .r1), .dp .eor .r1 .r5 (.imm 1),
   .dp .add .r4 .r4 (.reg .r1), .mov .r6 (.shifted .r6 .lsl 1), .subs .r12 .r12 (.imm 1)]

/-- A word of the leading zeros, from its address in `r0` (moving down); `lr` the words left. -/
def clzWord : Prog isa := seqs [.block [.ldr .r6 .r0 0, .dp .sub .r0 .r0 (.imm 4), .mov .r12 (.imm 32)],
  .loop (.block clzBit) .ne, .block [.subs .lr .lr (.imm 1)]]

/-- The leading zeros of `[j]` over the width (`32` times it for zero) into the slot `d`. -/
def lzW (j d : Nat) : Prog isa := seqs [
  .block (ptr .r0 j ++ [.dp .add .r0 .r0 (.reg .r7), .dp .sub .r0 .r0 (.imm 12), .mov .lr (.reg .r9),
    .mov .r4 (.imm 0), .mov .r5 (.imm 0)]),
  .loop clzWord .ne, .block [.str .r4 .r8 d]]

/-- The next word stage: `sTk` halved, `sWs` doubled, and whether `sWs` is still below `4 W` (`Z`
clear). -/
def stageNext : List Instr :=
  [.ldr .r1 .r8 sTk, .mov .r1 (.shifted .r1 .lsr 1), .str .r1 .r8 sTk,
    .ldr .r1 .r8 sWs, .mov .r1 (.shifted .r1 .lsl 1), .str .r1 .r8 sWs,
    .dp .sub .r1 .r1 (.shifted .r9 .lsl 2), .mov .r1 (.shifted .r1 .lsr 31), .cmp .r1 (.imm 0)]

/-- `op` puts a value into `[t1]`; then `[x] :=` it where the bit at `sBit` is set, through `t2`. -/
def selStage (op : Prog isa) (x t1 t2 : Nat) : Prog isa := seqs [op, sel t2 x t1 sBit, copy x t2]

/-- A stage of `X'`: `2^i` bits where bit `i` of `lz` is set. -/
def normBitStage (i : Nat) : Prog isa := seqs [.block (bitTo sLz i), copy wG wR, selStage (shlK wG (2 ^ i)) wR wG wF]

/-- A stage of `X'` by `2^m` words (`4 · 2^m` at `sWs`) where bit `m` of `⌊lz / 32⌋` (`sTk`) is set;
then `2^(m + 1)`, while below `W`. -/
def normWordStage : Prog isa := seqs [.block (bitTo sTk 0), selStage (shiftUpBy sWs wG wR) wR wG wF,
  .block stageNext]

/-- `X' = 4^⌊lz / 2⌋ X` (wide): whether `X = 0`, and `X := 1` there (its root is then replaced by 0), `lz`,
then the even bits of `lz` below 32 and its words. -/
def normX : Prog isa := seqs [eqS sZ wR wZ 18,
  .block ([.ldr .r2 .r8 sZ] ++ ptr .r0 wR ++ [.ldr .r1 .r0 0, .dp .orr .r1 .r1 (.reg .r2), .str .r1 .r0 0]),
  lzW wR sLz,
  normBitStage 1, normBitStage 2, normBitStage 3, normBitStage 4,
  .block [.ldr .r1 .r8 sLz, .mov .r1 (.shifted .r1 .lsr 5), .str .r1 .r8 sTk, .mov .r1 (.imm 4),
    .str .r1 .r8 sWs],
  .loop normWordStage .ne]

/-- A pair of bits of `T` (`r1`, `r2`) into the remainder (`r4`, `r5`), the root `r3` doubled, and
one more where `4 s + 1` fits, subtracted; `lr` the pairs left. -/
def isqBit : List Instr :=
  [.mov .r4 (.shifted .r4 .lsl 2), .dp .orr .r4 .r4 (.shifted .r5 .lsr 30),
   .mov .r5 (.shifted .r5 .lsl 2), .dp .orr .r5 .r5 (.shifted .r1 .lsr 30),
   .mov .r1 (.shifted .r1 .lsl 2), .dp .orr .r1 .r1 (.shifted .r2 .lsr 30), .mov .r2 (.shifted .r2 .lsl 2),
   .mov .r0 (.shifted .r3 .lsr 30), .mov .r6 (.shifted .r3 .lsl 2), .dp .orr .r6 .r6 (.imm 1),
   .subs .r10 .r5 (.reg .r6), .mov .r11 (.imm 0), .adc .r11 .r11 (.imm 0),
   .dp .add .r12 .r4 (.reg .r11), .dp .sub .r12 .r12 (.reg .r0), .dp .sub .r12 .r12 (.imm 1),
   .mov .r0 (.shifted .r12 .lsr 31), .dp .sub .r11 .r0 (.imm 1),
   .dp .eor .r6 .r5 (.reg .r10), .dp .and .r6 .r6 (.reg .r11), .dp .eor .r5 .r5 (.reg .r6),
   .dp .eor .r6 .r4 (.reg .r12), .dp .and .r6 .r6 (.reg .r11), .dp .eor .r4 .r4 (.reg .r6),
   .dp .add .r3 .r3 (.reg .r3), .dp .add .r3 .r3 (.imm 1), .dp .sub .r3 .r3 (.reg .r0),
   .subs .lr .lr (.imm 1)]

/-- The offset of `D`'s word `m = W / 2 - 1 - j` (and `C`'s). -/
def sCm : Nat := 60

/-- The root `s₀` of `X'`'s top two words into the slot `d` (140), their remainder in their place, and
`2 s₀` into `D`'s words `W / 2 - 1` and `W / 2`, and its complement into `C`'s. -/
def isqTop : Prog isa := seqs [
  .block (ptr .r0 wR ++ [.dp .add .r0 .r0 (.reg .r7), .dp .sub .r0 .r0 (.imm 16), .ldr .r2 .r0 0,
    .ldr .r1 .r0 4, .mov .r3 (.imm 0), .mov .r4 (.imm 0), .mov .r5 (.imm 0), .mov .lr (.imm 32)]),
  .loop (.block isqBit) .ne,
  .block (ptr .r0 wR ++ [.dp .add .r0 .r0 (.reg .r7), .dp .sub .r0 .r0 (.imm 16), .str .r5 .r0 0, .str .r4 .r0 4,
    .str .r3 .r8 VG.Impl.Rsa.Arm.KeyDiv.sD] ++ ptr .r0 wD ++ [.dp .add .r0 .r0 (.shifted .r9 .lsl 1),
    .dp .sub .r0 .r0 (.imm 4), .dp .add .r1 .r3 (.reg .r3), .mov .r2 (.shifted .r3 .lsr 31), .str .r1 .r0 0,
    .str .r2 .r0 4] ++ ptr .r0 wE ++ [.dp .add .r0 .r0 (.shifted .r9 .lsl 1), .dp .sub .r0 .r0 (.imm 4),
    .mvn .r1 (.reg .r1), .mvn .r2 (.reg .r2), .str .r1 .r0 0, .str .r2 .r0 4])]

/-- `D` zero and `C` all ones, `s₀` and its remainder (`isqTop`), and the reciprocal of `s₀`. -/
def firstDigit : Prog isa := seqs [copy wD wZ, sub3 wE wZ wOne, isqTop, VG.Impl.Rsa.Arm.KeyDiv.recip]

/-- The digits' length (words), and `d₁`. -/
def sLn : Nat := 96

/-! ### A digit

`R = r β² + P` is in place in `X'`, at its word `b = W - 2 j - 2` (offset at `sPo`), over `j + 3` words
(`sLn`); `D`'s word `m` (offset at `sCm`) takes `q̂`, so that `D`'s words from `m` are `D' = 2 s β + q̂`
(`j + 2` words), and `C`'s its complement. -/

/-- `q̂` into `D`'s word `m` and its complement into `C`'s, from `m`'s offset in `r3`. -/
def setQ : List Instr :=
  [.ldr .r1 .r8 VG.Impl.Rsa.Arm.KeyDiv.sQ] ++ ptr .r2 wD ++ [.dp .add .r2 .r2 (.reg .r3), .str .r1 .r2 0,
    .mvn .r1 (.reg .r1)] ++ ptr .r2 wE ++ [.dp .add .r2 .r2 (.reg .r3), .str .r1 .r2 0]

/-- `r0 :=` `R`'s address, `r12 :=` that of word `m` of `[d]`, and `lr := j + 2`. -/
def dPtrs (d : Nat) : List Instr :=
  ptr .r0 wR ++ [.ldr .r1 .r8 sPo, .dp .add .r0 .r0 (.reg .r1)] ++ ptr .r12 d ++
    [.ldr .r1 .r8 sCm, .dp .add .r12 .r12 (.reg .r1), .ldr .lr .r8 sLn, .dp .sub .lr .lr (.imm 1)]

/-- `T = R - q̂ D'`: `R`'s low `j + 2` words plus `q̂ C' + q̂` by a row (`C' = β^(j + 2) - 1 - D'`), and
`R`'s top word less `q̂` plus the carry. A block ends after each load of an offset. -/
def mulSubD : Prog isa := seqs [.block [.ldr .r3 .r8 sCm], .block setQ, .block (dPtrs wE),
  .block [.ldr .r1 .r8 VG.Impl.Rsa.Arm.KeyDiv.sQ, .mov .r11 (.reg .r1)],
  row,
  .block ([.ldr .r2 .r0 0, .dp .add .r2 .r2 (.reg .r11), .dp .sub .r2 .r2 (.reg .r1), .str .r2 .r0 0] ++
    VG.Impl.Rsa.Arm.Recover.ctxW)]

/-- The sign `x` of `T` (its top word's top bit), its mask `-x` into `r1`, and `x (q̂ - 1)` into `r11`. -/
def corrPre : List Instr := [.dp .add .r2 .r0 (.shifted .lr .lsl 2), .ldr .r2 .r2 0,
  .mov .r1 (.shifted .r2 .lsr 31), .ldr .r2 .r8 VG.Impl.Rsa.Arm.KeyDiv.sQ, .dp .sub .r11 .r2 (.imm 1),
  .mov .r3 (.imm 0), .dp .sub .r3 .r3 (.reg .r1), .dp .and .r11 .r11 (.reg .r3), .mov .r1 (.reg .r3)]

/-- The carry into `T`'s top word, the context back, `q̂ := q̂ - x` (`q̂` plus the mask, in `r2`), and `m`'s
offset into `r4`. -/
def corrPost : List Instr := [.ldr .r2 .r0 0, .dp .add .r2 .r2 (.reg .r11), .str .r2 .r0 0] ++
  VG.Impl.Rsa.Arm.Recover.ctxW ++ [.ldr .r2 .r8 VG.Impl.Rsa.Arm.KeyDiv.sQ, .dp .add .r2 .r2 (.reg .r1),
    .str .r2 .r8 VG.Impl.Rsa.Arm.KeyDiv.sQ, .ldr .r4 .r8 sCm]

/-- `q̂` (`r2`) into `D`'s word `m`. -/
def corrSet : List Instr := ptr .r3 wD ++ [.dp .add .r3 .r3 (.reg .r4), .str .r2 .r3 0]

/-- A correction: where `T < 0`, `T += 2 s β + 2 q̂ - 1 = D' + q̂ - 1` (a row adding `D'` under the mask `-x`)
and `q̂ -= 1`. -/
def correct : Prog isa :=
  seqs [.block (dPtrs wD), .seq (.block corrPre) (.seq maskRow (.block corrPost)), .block corrSet]

/-- `D := 2 s' = 2 s β + 2 q` from its word `m` (`2 q`'s low word, and the next plus its top bit) and `C`
its complement, from `m`'s offset in `r1`. -/
def finishQ : List Instr :=
  ptr .r12 wE ++ [.dp .add .r12 .r12 (.reg .r1)] ++ ptr .r10 wD ++
  [.dp .add .r10 .r10 (.reg .r1), .ldr .r1 .r8 VG.Impl.Rsa.Arm.KeyDiv.sQ, .dp .add .r2 .r1 (.reg .r1),
    .str .r2 .r10 0, .mvn .r2 (.reg .r2), .str .r2 .r12 0, .mov .r3 (.shifted .r1 .lsr 31),
    .ldr .r4 .r10 4, .dp .add .r4 .r4 (.reg .r3), .str .r4 .r10 4,
    .ldr .r4 .r12 4, .dp .sub .r4 .r4 (.reg .r3), .str .r4 .r12 4]

/-- `d₁`, `s'`'s second word, from `D`'s words `W / 2 - 2` and `W / 2 - 1`. -/
def finishD1 : List Instr :=
  ptr .r12 wD ++ [.dp .add .r12 .r12 (.shifted .r9 .lsl 1), .dp .sub .r12 .r12 (.imm 8), .ldr .r2 .r12 0,
    .ldr .r3 .r12 4, .mov .r2 (.shifted .r2 .lsr 1), .dp .orr .r2 .r2 (.shifted .r3 .lsl 31),
    .str .r2 .r8 VG.Impl.Rsa.Arm.KeyDiv.sD1]

/-- The next digit's offsets and length. -/
def digNext : List Instr := [.ldr .r1 .r8 sPo, .dp .sub .r1 .r1 (.imm 8), .str .r1 .r8 sPo,
  .ldr .r1 .r8 sMo, .dp .add .r1 .r1 (.imm 4), .str .r1 .r8 sMo,
  .ldr .r1 .r8 sLn, .dp .add .r1 .r1 (.imm 1), .str .r1 .r8 sLn,
  .ldr .r1 .r8 sCm, .dp .sub .r1 .r1 (.imm 4), .str .r1 .r8 sCm]

/-- The estimate's pointer: `R`'s address. -/
def estPtr : List Instr := ptr .r10 wR ++ [.ldr .r1 .r8 sPo]

/-- Then `4 j`. -/
def estOff : List Instr := [.dp .add .r10 .r10 (.reg .r1), .ldr .r1 .r8 sMo]

/-- `q̂` from `⌊R / 2⌋`'s words `j - 1` to `j + 1`, by the 3-by-2 estimate. -/
def estBody : List Instr := [.dp .add .r10 .r10 (.reg .r1), .dp .sub .r10 .r10 (.imm 4), .ldr .r0 .r10 0,
  .ldr .r1 .r10 4, .ldr .r2 .r10 8, .ldr .r3 .r10 12,
  .mov .r0 (.shifted .r0 .lsr 1), .dp .orr .r0 .r0 (.shifted .r1 .lsl 31), .str .r0 .r8 VG.Impl.Rsa.Arm.KeyDiv.sU0,
  .mov .r11 (.shifted .r1 .lsr 1), .dp .orr .r11 .r11 (.shifted .r2 .lsl 31),
  .mov .r2 (.shifted .r2 .lsr 1), .dp .orr .r2 .r2 (.shifted .r3 .lsl 31),
  .str .r2 .r8 VG.Impl.Rsa.Arm.KeyDiv.sU2, .mov .r12 (.reg .r8)] ++ VG.Impl.Rsa.Arm.KeyDiv.quot ++
  VG.Impl.Rsa.Arm.KeyDiv.refine3 ++ [.mov .r8 (.reg .r12)] ++ VG.Impl.Rsa.Arm.Recover.ctxW

/-- A digit: `q̂`, `T = R - q̂ (2 s β + q̂)` in place, two corrections, `D := 2 s'`. -/
def sqDigit : Prog isa := seqs [.block estPtr, .block estOff, .block estBody, mulSubD, correct, correct,
  .block [.ldr .r1 .r8 sCm], .block finishQ, .block finishD1, .block digNext, .block cntNext]

/-- The root `s = D / 2` into `[wS]`. -/
def sqEnd : Prog isa := seqs [copy wS wD, .block clr11, half wS]

/-! ### The root's stages, over its `W / 2` words -/

/-- `lr := W / 2`, the root's words. -/
def lrH : Instr := .mov .lr (.shifted .r9 .lsr 1)

/-- `[o] := [a]` over the root's words. -/
def copyH (o a : Nat) : Prog isa := .seq (.block [lrH]) (copyN o a)

/-- `[o] := [b]` if the slot `sl` holds 1, else `[a]`, over the root's words. -/
def selH (o a b sl : Nat) : Prog isa := .seq (.block [lrH]) (selN o a b sl)

/-- `[j] := ⌊([j] + r11 · 2^(32 W / 2)) / 2^k⌋` over the root's words: `r11` stored as word `W / 2`, then
one shift by `k`. -/
def halfKHN (j k : Nat) : Prog isa :=
  .seq (.block (ptr .r0 j ++ [lrH, .dp .add .r1 .r0 (.shifted .lr .lsl 2), .str .r11 .r1 0])) (shiftRightK k)

/-- `[j] := ⌊[j] / 2^k⌋` over the root's words, `0 < k < 32`. -/
def halfKH (j k : Nat) : Prog isa := .seq (.block clrK) (halfKHN j k)

/-- `shiftDownB` over the root's words. -/
def shiftDownBH (o : Nat) : Prog isa :=
  .seq (.block ([.dp .add .r10 .r10 (.reg .r1), .mov .r12 (.reg .r10)] ++ ptr .r0 o ++ [lrH,
    .dp .sub .lr .lr (.shifted .r1 .lsr 2), .mov .r11 (.imm 0)])) copyWords

/-- `[o] := ⌊[a] / 2^(32 s)⌋` over the root's words, for `4 s` at `d`. A block ends after the load of
`4 s`. -/
def shiftDownByH (d o a : Nat) : Prog isa :=
  seqs [copyH o wZ, .block (ptr .r10 a ++ [.ldr .r1 .r8 d]), shiftDownBH o]

/-- `stageNext` while below the root's `W / 2` words. -/
def stageNextH : List Instr :=
  [.ldr .r1 .r8 sTk, .mov .r1 (.shifted .r1 .lsr 1), .str .r1 .r8 sTk,
    .ldr .r1 .r8 sWs, .mov .r1 (.shifted .r1 .lsl 1), .str .r1 .r8 sWs,
    .dp .sub .r1 .r1 (.shifted .r9 .lsl 1), .mov .r1 (.shifted .r1 .lsr 31), .cmp .r1 (.imm 0)]

/-- `selStage` over the root's words. -/
def selStageH (op : Prog isa) (x t1 t2 : Nat) : Prog isa := seqs [op, selH t2 x t1 sBit, copyH x t2]

/-- The root's bit stage `i`: `[wS]` halved `2^i` times where bit `i` of `c` (`sTu`) is set. -/
def rootBitStage (i : Nat) : Prog isa :=
  seqs [.block (bitTo sTu i), copyH wG wS, selStageH (halfKH wG (2 ^ i)) wS wG wF]

/-- The root's word stage: `[wS]` shifted down by `2^m` words where bit `m` of `⌊c / 32⌋` (`sTk`) is
set. -/
def rootWordStage : Prog isa := seqs [.block (bitTo sTk 0), selStageH (shiftDownByH sWs wG wS) wS wG wF,
  .block stageNextH]

/-- `c = ⌊lz / 2⌋` (`sTu`), `⌊c / 32⌋` (`sTk`) and the word stages' first step (`sWs`). -/
def sqMid : List Instr := [.ldr .r1 .r8 sLz, .mov .r1 (.shifted .r1 .lsr 1), .str .r1 .r8 sTu,
  .mov .r1 (.shifted .r1 .lsr 5), .str .r1 .r8 sTk, .mov .r1 (.imm 4), .str .r1 .r8 sWs]

/-- `X' = 4^c X`'s root `⌊s / 2^c⌋`, 0 where `X` was 0, into the narrow `[aY]`; whether `X` is a
square (`sOk5`: `r = 0`). -/
def sqFinish : Prog isa := seqs [eqS sOk5 wR wZ 18, copy wG wZ, copy wF wZ, .block sqMid,
  rootBitStage 0, rootBitStage 1, rootBitStage 2, rootBitStage 3, rootBitStage 4,
  .loop rootWordStage .ne,
  selH wG wS wZ sZ, .block toN, copy aY 22]

/-- The digits' slots: the offsets, the count `W / 2 - 1`, the length 4, `d₁ = 0` and `D`'s offset. -/
def sqInit : List Instr := [.mov .r1 (.shifted .r9 .lsl 2), .dp .sub .r1 .r1 (.imm 16), .str .r1 .r8 sPo,
  .mov .r1 (.imm 4), .str .r1 .r8 sMo, .dp .sub .r1 .r9 (.imm 2), .mov .r1 (.shifted .r1 .lsr 1), .str .r1 .r8 sK,
  .mov .r1 (.imm 4), .str .r1 .r8 sLn, .mov .r1 (.imm 0), .str .r1 .r8 VG.Impl.Rsa.Arm.KeyDiv.sD1,
  .mov .r1 (.shifted .r9 .lsl 1), .dp .sub .r1 .r1 (.imm 8), .str .r1 .r8 sCm]

/-- The square root of `[wR]` (wide), from the narrow context. -/
def sqrt : Prog isa := seqs [.block toW, normX, firstDigit, .block sqInit, .loop sqDigit .ne, sqEnd, sqFinish]

/-! ## The factors -/

def factors : Prog isa := seqs [add aP aB aY aT1 aZN, .block clr11, half aP,
  sub3 aQ aB aY, .block clr11, half aQ,
  .block (andS sMask sOkDE sLt ++ andS sMask sMask sExact ++ andS sMask sMask sOk4 ++
    andS sMask sMask sOk5)]

/-! ## The function -/

def det (um : Bool := false) : Prog isa := seqs [deMinus, twos, gcd um, rowProd wA wX3 17, divA, divB,
  square, minus4n, sqrt, factors]

/-- Once `n` is known valid. -/
def valid (um : Bool := false) : Prog isa := seqs [VG.Impl.Rsa.Arm.Recover.loads, prodW, det um,
  VG.Impl.Rsa.Arm.Recover.stores]

/-- `vg_rsa_recover_primes_det`; `um` its inverse's `umaal` variant. -/
def code (um : Bool := false) : Prog isa :=
  VG.Impl.Rsa.Arm.Recover.codeWith (.ite .eq (valid um) VG.Impl.Rsa.Arm.Recover.fail)

/-- `vg_rsa_recover_primes_det_umaal`: the `umaal` inverse in the GCD, and `umaal` rows (`umaalArithmetic`). -/
def codeU : Prog isa := VG.Impl.Bignum.Arm.umaalArithmetic (code true)

/-- The code of a variant (`Proof/Variants/RsaInverse/Arm.lean`). -/
def codeFor (um : Bool) : Prog isa := if um then codeU else code

end VG.Impl.Rsa.Arm.RecoverDet
