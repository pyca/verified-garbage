module

public import VerifiedGarbage.Impl.Rsa.RISCV64.MulMod
public import VerifiedGarbage.Impl.Rsa.RISCV64.WordDiv
public import VerifiedGarbage.Impl.Rsa.RISCV64.Div
public import VerifiedGarbage.Impl.Rsa.RISCV64.InvBatch
public import VerifiedGarbage.Impl.Bignum.RISCV64.Precompute

/-!
# `vg_rsa_recover_primes_det` on RISC-V

`vg_rsa_recover_primes_det(p = a0, p_len = a1, q = a2, q_len = a3, n = a4,
n_len = a5, e = a6, e_len = a7, d, d_len, scratch, scratch_len)`, the last
four on the stack. SP 800-56B Rev. 2 Appendix C.2 without a branch on a
secret, as on PPC64LE (`Impl/Rsa/PPC64LE/RecoverDet.lean`), in words of 64
bits and computing what `Proof/Rsa/RecoverDetModel.lean` models, with `nb =
64 w` narrow and `wb = 64 W` wide bits.

The numbers live in the key working space (`Impl/Rsa/RISCV64/KeyWs.lean`)
with `w = ⌈n_len / 8⌉ + 1` words (narrow), a word more than `n` needs, so
that `d e` fits; read with `W = 2 w + 2` words (wide), the same working
space has twice the stride, and its array `j` is the narrow arrays `2 j` and
`2 j + 1`. A narrow number copied into the low half of a wide array of zeros
is that wide number.

* `n` is checked as `vg_rsa_public_precompute` checks it (`Precompute.check`),
  an invalid modulus writes zeros at once.
* `d e`, one row of the product (`mulRow`), `e` being one word (wide), `x =
  d e - 1` and whether `d e ≥ 2`;
* the halvings of `u = n - 1` while it is even, and while `x` is even too of
  `x` and doublings of `2^k x` (`u` and `x` narrow, `2^k x` wide), in closed
  form: `t₁`, the trailing zeros of `u ∨ x` (those of `gcd(u, x)`), and `t₂`,
  those of `u` (`ctz`: a scan for the lowest nonzero word, then six stages
  within it), then `u / 2^t₂`, `x / 2^t₁` and `2^k x 2^t₁` by shifts of
  words in stages, each a masked pass, and of bits (`shrBy`, `shlBy`);
* `gcd(u, x)`, `u` odd, by batches of divsteps on `f` and `g` alone
  (`InvBatch.gcd`, on narrow arrays, `2 w` digits), with 1 where `u = 1`,
  which it leaves to its caller;
* `a = gcd(u, x) · 2^k x` modulo `2^(64 W)` by a schoolbook product of words
  (`mulLow`, `mul` and `mulhu`), `m = ⌊a / n⌋`, `r = a mod n` by long division
  of words (`WordDiv.divCore`, `n` being `h = w - 1` words with its top word
  not zero), and whether `m < n`;
* `b - 1 = (n - r) / (m + 1)` by the same division, `m + 1` and `n - r`
  shifted up by the leading zero words of `m + 1`'s `h` words (`clz`, shifts
  of words in stages) so that its top word is not zero, which matters only
  where `m < n`, `m + 1 ≤ n`; `b² - 4 n` (`mulLow`) and whether `b² > 4 n`;
* its square root, two bits at a time from the top in `32 W` steps
  (`sqrtBody`): the wide radicand shifted left by two into the narrow
  remainder (`shl2C`), which keeps `4 y + 1` where it fits (`trial`);
* `p = (b + ϒ) / 2` and `q = (b - ϒ) / 2`, written under the mask of every
  check, which is returned.

Registers kept throughout: `s1` `n`, `s2` `n_len`, `s3` `p`, `s4` `q`, `s5`
`e`, `s6` `e_len`, `a0` `d`, `a1` `d_len` (the divisions' saved in the
header around them, `save`, `restore`); `s9`–`s11` the working space's (`w`
or `W`, the stride, the base), `s7` the count of each loop, and `s8` and `a2`,
`a3`, `a6` the product's. Every address is computed from the base,
the stride and `s9`, and every count from `s9` and `n_len`: the addresses and
branches depend only on them and on `n`.
-/

@[expose] public section

namespace VG.Impl.Rsa.RISCV64.RecoverDet

open VG.RISCV64 VG.Impl.Bignum.RISCV64 VG.Impl.Rsa.RISCV64.Keys VG.Impl.Rsa.RISCV64.Div
open VG.Impl.Bignum.RISCV64.Precompute (lzStep recipHead divBit)

/-! ## The header

Bytes 0–95 hold the caller's `s0`–`s11`, 96 whether `u = 1` for the GCD,
104–120 and 168–184 the registers a division borrows, 128–144 the shared
routines' slots, and from 152 this function's. -/

/-- Whether `u = 1`, which the GCD leaves to its caller. -/
def sU1 : Nat := 96

/-- The registers a division borrows, and their slots. -/
def divSaved : List (Reg × Nat) := [(.s1, 104), (.s2, 112), (.s3, 120), (.s4, 168), (.a0, 176), (.a1, 184)]

def saveDiv : List Instr := divSaved.map fun (r, o) => .store .d r .s11 o
def restDiv : List Instr := divSaved.map fun (r, o) => .load .d r .s11 o

/-- `d e < 1` and `d e - 1 < 1`. -/
def sB0 : Nat := 152
def sB1 : Nat := 160
/-- `m < n`. -/
def sLt : Nat := 200
/-- `(n - r) mod (m + 1) = 0`. -/
def sExact : Nat := 208
/-- `b² < 4 n` and `b² - 4 n < 1`. -/
def sC1 : Nat := 216
def sC2 : Nat := 224
/-- The square root's borrow. -/
def sBb : Nat := 232
/-- The square root's remainder is zero. -/
def sOk5 : Nat := 240
/-- The mask of every check. -/
def sMask : Nat := 248

/-! ## The arrays

Wide (`W` words; the wide array `j` is the narrow arrays `2 j` and `2 j + 1`):
zero, `e`, `d`, `d e`, unused, the divisions' digits (5) and temporary (6)
and `b`'s shifted divisor and dividend (7, 8), `x`, one, `2^k x`, `a`, the
remainder `r` (then `b² - 4 n`), `n` (then `4 n`), `m`, a temporary (then
`b - 1`), the GCD, `b`, `b²`. -/

def wZ : Nat := 0
def wE : Nat := 1
def wD : Nat := 2
def wM : Nat := 3
def wDig : Nat := 5
def wTmp : Nat := 6
def wSD : Nat := 7
def wSN : Nat := 8
def wX : Nat := 9
def wOne : Nat := 10
def wX3 : Nat := 11
def wA : Nat := 12
def wR : Nat := 13
def wN : Nat := 14
def wDt : Nat := 15
def wT2 : Nat := 16
def wG : Nat := 17
def wB : Nat := 18
def wSq : Nat := 19

/-- Narrow (`w` words), from 40 on, past the wide arrays 0–19: `n`, one,
zero, `u`, `x` halved, a temporary; the GCD's `u`, `v` and temporaries; the
second division's `-1`, `m + 1`, `n - r` (then `b - 1` and `b`), and two
unused; the square root's remainder, root, `4 y + 1` and difference;
the factors and the temporary of their sum. -/
def aN : Nat := 40
def aOne : Nat := 41
def aZero : Nat := 42
def aU : Nat := 43
def aX2 : Nat := 44
def aT : Nat := 45
def aNeg1 : Nat := 51
def aM1 : Nat := 52
def aD : Nat := 53
def aRm : Nat := 56
def aSy : Nat := 57
def aTy : Nat := 58
def aDf : Nat := 59
def aP : Nat := 60
def aQ : Nat := 61
def aNy : Nat := 62

/-- The number of narrow arrays, all zeroed. -/
def nArr : Nat := 63

/-! ## Contexts -/

/-- The narrow `w = ⌈n_len / 8⌉ + 1` into `s9` and its stride `8 (w + 2)` into `s10`. -/
def ctxInit : List Instr :=
  [.addi .s9 .s2 7, .shift .srl .d .s9 .s9 3, .addi .s9 .s9 1, .addi .s10 .s9 2,
    .shift .sll .d .s10 .s10 3]

/-- `W = 2 w + 2` into `s9` and its stride `8 (W + 2)`, twice the narrow one. -/
def ctxW : List Instr :=
  [.shift .sll .d .s9 .s9 1, .addi .s9 .s9 2, .shift .sll .d .s10 .s10 1]

/-- Back to `w = (W - 2) / 2`. -/
def ctxw : List Instr :=
  [.addi .s9 .s9 (-2), .shift .srl .d .s9 .s9 1, .shift .srl .d .s10 .s10 1]

/-! ## Entry and exit -/

/-- The working space (the stack argument 2) and the registers saved there,
then the pointers and lengths into the registers kept. -/
def entry : List Instr :=
  save 16 ++
  [mov .s3 .a0, mov .s4 .a2, mov .s1 .a4, mov .s2 .a5, mov .s5 .a6, mov .s6 .a7, .addSp .t0 0,
    .load .d .a0 .t0 0, .load .d .a1 .t0 8]

/-- Whether `n` is a valid modulus, in `s0`: 0 if it is. -/
def nCheck : Prog isa := .seq (.block [mov .s7 .s1, mov .s8 .s2]) Precompute.check

/-- Zeros to `p` and `q`, and 0 returned. -/
def fail : Prog isa := seqs [zeroBytes .s3 .s2, zeroBytes .s4 .s2, .block [.li .a0 0]]

/-! ## Operations -/

/-- `[j] := 2 [j] + t4` modulo `2^(64 s9)`, for `t4` 0 or 1, the bit shifted
out in `t4`. -/
def shlC (j : Nat) : Prog isa := .seq (.block (ptr .t0 j ++ [mov .t3 .s9])) (countLoop .t3 shlBody)

/-- `[j] := 2 [j]` modulo `2^(64 s9)`, the bit shifted out in `t4`. -/
def shl (j : Nat) : Prog isa := .seq (.block [.li .t4 0]) (shlC j)

/-- `[o] := [a] + [b]` modulo `2^(64 s9)`, through `[t] = [z] - [b]`, with
`[z]` zero. -/
def add (o a b z t : Nat) : Prog isa := .seq (sub3 t z b) (sub3 o a t)

/-- One word of a row of the product: `t4 + [t0] + a6 [t1]`, its low word to
`[t0]` and its high word, the carry, into `t4`. -/
def mulBody : List Instr :=
  [.load .d .t5 .t1 0, .mul .t6 .a6 .t5, .mulhu .t5 .a6 .t5, .load .d .a4 .t0 0,
    .add .t6 .t6 .a4, .sltu .a4 .t6 .a4, .add .t5 .t5 .a4,
    .add .t6 .t6 .t4, .sltu .a4 .t6 .t4, .add .t5 .t5 .a4,
    .store .d .t6 .t0 0, mov .t4 .t5, .addi .t0 .t0 8, .addi .t1 .t1 8]

/-- A row: `[o] += y_i [x] 2^(64 i)` modulo `2^(64 s9)`, for `y_i` the word
at `a2`, `a3` the word `i` of `[o]` and `s8 = s9 - i` words to go; then the
next row's. -/
def mulRow (x : Nat) : Prog isa :=
  .seq (.block ([.load .d .a6 .a2 0, mov .t0 .a3] ++ ptr .t1 x ++ [mov .t3 .s8, .li .t4 0]))
    (.seq (countLoop .t3 mulBody) (.block [.addi .a2 .a2 8, .addi .a3 .a3 8, .addi .s8 .s8 (-1)]))

/-- `[o] := [y] [x]` modulo `2^(64 s9)`, from `[o] = 0`: a row for each of
the `s9` words of `[y]`. -/
def mulLow (o y x : Nat) : Prog isa :=
  .seq (.block (ptr .a2 y ++ ptr .a3 o ++ [mov .s8 .s9])) (.loop (mulRow x) (.nonzero .s8))

/-- A row of `mulHalf`: `[o] += y_i [x] 2^(64 i)` over the low `w / 2` words of `[x]`, for `y_i` the
word at `a2` and `a3` the word `i` of `[o]`, the carry stored to word `i + w / 2`; then the next row's. -/
def mulRowH (x : Nat) : Prog isa :=
  .seq (.block ([.load .d .a6 .a2 0, mov .t0 .a3] ++ ptr .t1 x ++ [.shift .srl .d .t3 .s9 1, .li .t4 0]))
    (.seq (countLoop .t3 mulBody)
      (.block [.store .d .t4 .t0 0, .addi .a2 .a2 8, .addi .a3 .a3 8, .addi .s8 .s8 (-1)]))

/-- `[o] := [y] [x]`, from `[o] = 0`, for `[y]` and `[x]` of `w / 2` words: a row for each of the
`w / 2` words of `[y]`. -/
def mulHalf (o y x : Nat) : Prog isa :=
  .seq (.block (ptr .a2 y ++ ptr .a3 o ++ [.shift .srl .d .s8 .s9 1])) (.loop (mulRowH x) (.nonzero .s8))

/-- A step less. -/
def next : List Instr := [.addi .s7 .s7 (-1)]

/-! ## `d e - 1` (wide) -/

/-- `n` (narrow), then with `W` `e` and `d`. -/
def loads : Prog isa := seqs [load aN .s1 .s2, .block ctxW, load wE .s5 .s6, load wD .a0 .a1]

/-- `d e`: `e` is one word, so one row of `mulLow`, `[wM] := e [wD]`, which fits. -/
def prod : Prog isa := .seq (.block (ptr .a2 wE ++ ptr .a3 wM ++ [mov .s8 .s9])) (mulRow wD)

/-- One (`wOne`), `x = d e - 1`, and the borrows of `d e - 1` and `x - 1`. -/
def deMinus : Prog isa := seqs [.block (setOne wOne), sub3 wX wM wOne, .block (stBorrow sB0),
  sub3 wT2 wX wOne, .block (stBorrow sB1)]

/-! ## The halvings -/

/-- `2^k x := x` (wide); `u = n - 1` and `x` (narrow). -/
def twosInit : Prog isa := seqs [copy wX3 wX, .block ctxw, .block (setOne aOne), sub3 aU aN aOne,
  copy aX2 (2 * wX)]

/-- A word of `ctz`'s scan, at `t0` and `t1`: `y = [A]_i ∨ [B]_i` (`t4`) and,
for the first nonzero one (`a5` whether one was found), its index `i` (`t2`)
into `a6` and `y` into `a3`, by a mask. -/
def tzScan : List Instr :=
  [.load .d .t4 .t0 0, .load .d .t5 .t1 0, .logic .or .t4 .t4 .t5, .sltu .t5 .a4 .t4,
    .logicImm .xor .t6 .a5 1, .logic .and .t6 .t6 .t5, .sub .t6 .a4 .t6, .logic .xor .a7 .a6 .t2,
    .logic .and .a7 .a7 .t6, .logic .xor .a6 .a6 .a7, .logic .xor .a7 .a3 .t4, .logic .and .a7 .a7 .t6,
    .logic .xor .a3 .a3 .a7, .logic .or .a5 .a5 .t5, .addi .t2 .t2 1, .addi .t0 .t0 8, .addi .t1 .t1 8]

/-- A stage of `2^k` of the trailing zeros of the word `y` (`a3`): `2^k`
more (`a2`) and `y` shifted down by them if `y`'s low `2^k` bits are zero. -/
def tzStage (k : Nat) : List Instr :=
  [.shift .sll .d .t4 .a3 (64 - 2 ^ k), .sltu .t4 .a4 .t4, .logicImm .xor .t4 .t4 1, .shift .sll .d .t5 .t4 k,
    .add .a2 .a2 .t5, .shiftReg .srl .d .a3 .a3 .t5]

/-- `dst :=` the trailing zeros of `[A] ∨ [B]` (`s9` words, not zero): the
scan for the lowest nonzero word, then six stages within it. -/
def ctz (A B : Nat) (dst : Reg) : Prog isa :=
  .seq (.block (ptr .t0 A ++ ptr .t1 B ++ [.li .a4 0, .li .t2 0, .li .a5 0, .li .a6 0, .li .a3 0, mov .t3 .s9]))
    (.seq (countLoop .t3 tzScan)
      (.block ([.li .a2 0] ++ ([5, 4, 3, 2, 1, 0] : List Nat).flatMap tzStage ++
        [.shift .sll .d .a6 .a6 6, .add dst .a6 .a2])))

/-- The mask of a stage, `0 - ` bit `b + j` of `R` (`t4`), and `2^j` (`t3`). -/
def stageMask (R : Reg) (b j : Nat) : List Instr :=
  [.li .t3 (2 ^ j : Nat), .shift .srl .d .t4 R (b + j), .logicImm .and .t4 .t4 1, .li .a4 0, .sub .t4 .a4 .t4]

/-- A word of a masked shift of words: `[t0] := mask ? [t1] : [t0]`, both
pointers moved by `d`. -/
def stageMove (d : Int) : List Instr :=
  [.load .d .a7 .t0 0, .load .d .a3 .t1 0, .logic .xor .a3 .a3 .a7, .logic .and .a3 .a3 .t4,
    .logic .xor .a7 .a7 .a3, .store .d .a7 .t0 0, .addi .t0 .t0 d, .addi .t1 .t1 d]

/-- A word of the masked clearing of the words shifted out: `[t0] := mask ? 0 : [t0]`. -/
def stageClear (d : Int) : List Instr :=
  [.load .d .a7 .t0 0, .logic .and .a7 .a7 .a3, .store .d .a7 .t0 0, .addi .t0 .t0 d]

/-- The `s9 - 2^j` moves of a stage from `t0` and `t1`, then the clearing of
the last `2^j` words. -/
def stageBody (d : Int) : Prog isa :=
  .seq (countLoop .t5 (stageMove d)) (.seq (.block [.logicImm .xor .a3 .t4 (-1), mov .t5 .t3])
    (countLoop .t5 (stageClear d)))

/-- Stage `j` of `[X] := ⌊[X] / 2^(64 ⌊R / 2^b⌋)⌋` (`s9` words): down by
`2^j` words if bit `b + j` of `R` is set; nothing where `2^j ≥ s9`. -/
def shrStage (X : Nat) (R : Reg) (b j : Nat) : Prog isa :=
  .seq (.block (stageMask R b j))
    (.ite (.geu .t3 .s9) (.block [])
      (.seq (.block (ptr .t0 X ++ [.shift .sll .d .t1 .t3 3, .add .t1 .t0 .t1, .sub .t5 .s9 .t3]))
        (stageBody 8)))

/-- Stage `j` of `[X] := [X] 2^(64 ⌊R / 2^b⌋) mod 2^(64 s9)`: up by `2^j`
words if bit `b + j` of `R` is set, from the top; nothing where `2^j ≥ s9`. -/
def shlStage (X : Nat) (R : Reg) (b j : Nat) : Prog isa :=
  .seq (.block (stageMask R b j))
    (.ite (.geu .t3 .s9) (.block [])
      (.seq (.block (ptr .t0 X ++ [.shift .sll .d .t5 .s9 3, .add .t0 .t0 .t5, .addi .t0 .t0 (-8),
          .shift .sll .d .t1 .t3 3, .sub .t1 .t0 .t1, .sub .t5 .s9 .t3]))
        (stageBody (-8))))

/-- The stages `0, …, k - 1` of a shift down by words. -/
def shrStages (X : Nat) (R : Reg) (b : Nat) : Nat → Prog isa
  | 0 => .block []
  | k + 1 => .seq (shrStages X R b k) (shrStage X R b k)

/-- The stages `0, …, k - 1` of a shift up by words. -/
def shlStages (X : Nat) (R : Reg) (b : Nat) : Nat → Prog isa
  | 0 => .block []
  | k + 1 => .seq (shlStages X R b k) (shlStage X R b k)

/-- `[X] := ⌊[X] / 2^R⌋` (`s9` words, `R < 2^13`): seven stages of words, then
`R mod 64` bits, a word from it and the next (`(y << 1) << (63 - b)` is
`y 2^(64 - b)` even for `b = 0`). -/
def shrBy (X : Nat) (R : Reg) (n : Nat := 7) : Prog isa := .seq (shrStages X R 6 n)
  (.seq (.block (ptr .t0 X ++ [.logicImm .and .a5 R 63, .logicImm .xor .a6 .a5 63, .addi .t5 .s9 (-1)]))
    (.seq (countLoop .t5 [.load .d .a7 .t0 0, .load .d .a3 .t0 8, .shiftReg .srl .d .a7 .a7 .a5,
        .shift .sll .d .a3 .a3 1, .shiftReg .sll .d .a3 .a3 .a6, .logic .or .a7 .a7 .a3, .store .d .a7 .t0 0,
        .addi .t0 .t0 8])
      (.block [.load .d .a7 .t0 0, .shiftReg .srl .d .a7 .a7 .a5, .store .d .a7 .t0 0])))

/-- `[X] := [X] 2^R mod 2^(64 s9)` (`R < 2^13`): seven stages of words, then
`R mod 64` bits, from the top. -/
def shlBy (X : Nat) (R : Reg) (n : Nat := 7) : Prog isa := .seq (shlStages X R 6 n)
  (.seq (.block (ptr .t0 X ++ [.shift .sll .d .t5 .s9 3, .add .t0 .t0 .t5, .addi .t0 .t0 (-8),
      .logicImm .and .a5 R 63, .logicImm .xor .a6 .a5 63, .addi .t5 .s9 (-1), .addi .t1 .t0 (-8)]))
    (.seq (countLoop .t5 [.load .d .a7 .t0 0, .load .d .a3 .t1 0, .shiftReg .sll .d .a7 .a7 .a5,
        .shift .srl .d .a3 .a3 1, .shiftReg .srl .d .a3 .a3 .a6, .logic .or .a7 .a7 .a3, .store .d .a7 .t0 0,
        .addi .t0 .t0 (-8), .addi .t1 .t1 (-8)])
      (.block [.load .d .a7 .t0 0, .shiftReg .sll .d .a7 .a7 .a5, .store .d .a7 .t0 0])))

/-- The halvings: `t₁ = tz(u ∨ x)` (`s7`) and `t₂ = tz(u)` (`s8`), `u := u / 2^t₂`,
`x := x / 2^t₁` (narrow) and `2^k x := 2^k x 2^t₁` (wide). -/
def twos : Prog isa := seqs [twosInit, ctz aU aX2 .s7, ctz aU aZero .s8, shrBy aU .s8, shrBy aX2 .s7,
  .block ctxW, shlBy wX3 .s7, .block ctxw]

/-! ## The GCD (narrow) -/

/-- `gcd(x, u)` into the low half of the wide `wG`, from `(x, u)`, by
`InvBatch.gcd` on the inverse's arrays with `n = 2 w` digits, and 1 where
`u = 1`. -/
def gcd : Prog isa := seqs [copy InvBatch.aX aX2, copy InvBatch.aMin aU, .block [.add .s8 .s9 .s9], InvBatch.gcd,
  eqS sU1 InvBatch.aMin aOne, sel InvBatch.aY InvBatch.aGcd aOne sU1, copy (2 * wG) InvBatch.aY]

/-! ## `a`, `m` and `r` (wide) -/

/-- `t0 := h = W / 2 - 2 = w - 1`, `n`'s words. -/
def halfH : List Instr := [.shift .srl .d .t0 .s9 1, .addi .t0 .t0 (-2)]

/-- `a = gcd(u, x) · 2^k x` modulo `2^(64 W)`; `n` into the zeroed wide
`wN`, `m = ⌊a / n⌋` (`wDt`) and `r = a mod n` (`wR`), and whether `m < n`. -/
def divA : Prog isa := seqs [copy (2 * wN) aN, .block ctxW, mulLow wA wG wX3,
  .block (saveDiv ++ halfH ++ [mov .t6 .s9]), WordDiv.divCore wA wR wN wTmp (some (wDig, wDt)), .block restDiv,
  sub3 wT2 wDt wN, .block (stBorrow sLt)]

/-! ## `b` (narrow) -/

/-- `s7 :=` the leading zero words of `[D]`'s `t0` words, but its lowest: a
scan for the highest nonzero word (index `t2`), by a mask. -/
def clz (D : Nat) : Prog isa :=
  .seq (.block (ptr .a5 D ++ [.li .a4 0, .li .t1 0, .li .t2 0, mov .t3 .t0]))
    (.seq (countLoop .t3 [.load .d .t4 .a5 0, .sltu .t4 .a4 .t4, .sub .t4 .a4 .t4, .logic .xor .t5 .t2 .t1,
        .logic .and .t5 .t5 .t4, .logic .xor .t2 .t2 .t5, .addi .t1 .t1 1, .addi .a5 .a5 8])
      (.block [.sub .s7 .t0 .t2, .addi .s7 .s7 (-1)]))

/-- `s0 :=` the top nonzero word of the `t0 = k` words of `[D]` (0 where every one is zero), every word
read and selected by a mask. -/
def topW (D : Nat) : Prog isa :=
  .seq (.block (ptr .a5 D ++ [.li .a4 0, .li .s0 0, mov .t3 .t0]))
    (countLoop .t3 [.load .d .t4 .a5 0, .sltu .t5 .a4 .t4, .sub .t5 .a4 .t5, .logic .xor .t6 .s0 .t4,
      .logic .and .t6 .t6 .t5, .logic .xor .s0 .s0 .t6, .addi .a5 .a5 8])

/-- `[X] := [X] 2^(64 s7) mod 2^(64 W)`, by stages of words. -/
def shlWords (X : Nat) : Prog isa := shlStages X .s7 0 7

/-- `[D]`'s word `h - 1` plus 1 if it is zero (`t0 = h`). -/
def fixTopH (D : Nat) : List Instr :=
  ptr .t3 D ++ [.shift .sll .d .t5 .t0 3, .add .t3 .t3 .t5, .addi .t3 .t3 (-8), .load .d .t5 .t3 0,
    .li .t6 1, .sltu .t6 .t5 .t6, .add .t5 .t5 .t6, .store .d .t5 .t3 0]

/-- `-1`, `m + 1` and `n - r` (narrow); both shifted up by the leading zero
words of `m + 1`'s `h` words (wide, 7 and 8), the divisor's top word made
nonzero; their quotient (`wT2`, then `aD`) and remainder (`wR`), and whether it is zero. -/
def divB : Prog isa := seqs [.block ctxw, sub3 aNeg1 aZero aOne, sub3 aM1 (2 * wDt) aNeg1,
  sub3 aD aN (2 * wR), .block ctxW, InvBatch.zeroW wSD, InvBatch.zeroW wSN, InvBatch.zeroW wR,
  InvBatch.zeroW wT2, .block ctxw, copy (2 * wSD) aM1, copy (2 * wSN) aD, .block (ctxW ++ saveDiv ++ halfH),
  clz wSD, shlWords wSD, shlWords wSN, .block (halfH ++ fixTopH wSD ++ halfH ++ [.add .t6 .t0 .t0]),
  WordDiv.divCore wSN wR wSD wTmp (some (wDig, wT2)), .block restDiv, .block ctxw, copy aD (2 * wT2),
  eqS sExact (2 * wR) aZero]

/-! ## `b² - 4 n` (wide) -/

/-- `[o] := [x]²` for `[x]` of `w` words (wide view, `s9 = 2 w + 2`, `[o]` zero): `w` rows
(`mulRowH`) of `w + 1` words. -/
def sqB (o x : Nat) : Prog isa :=
  .seq (.block (ptr .a2 x ++ ptr .a3 o ++ [.shift .srl .d .s8 .s9 1, .addi .s8 .s8 (-1)]))
    (.loop (mulRowH x) (.nonzero .s8))

/-- `b`, `b²` (`w` rows: `b` has `w` words), `4 n`, `b² - 4 n` in `wR`, and whether
`b² < 4 n` and `b² - 4 n < 1`. -/
def minus4n : Prog isa := seqs [sub3 aD aD aNeg1, copy (2 * wB) aD, .block ctxW, sqB wSq wB,
  shl wN, shl wN, sub3 wR wSq wN, .block (stBorrow sC1), sub3 wT2 wR wOne, .block (stBorrow sC2)]

/-! ## The square root

By words (`Proof/Bignum/SqrtRem.lean`), the radicand `X` (`[wR]`, `L = W` words,
`k = W / 2` digits) normalized by `4^c`, `c = ⌊clz(X) / 2⌋` (`norm`), so that its
root's top word `s₀ ≥ 2^63`: `s₀` and its remainder by bit pairs of the top two
words (`first`), then a digit a step (`digit`), each estimated from the
remainder's top words by `s₀`'s reciprocal (`Precompute.recip`, once), the
remainder `R - q̂ (2 s β + q̂)` kept in place over `X`'s words, and three
masked corrections. The root is the digits shifted down by `c`; where `X = 0`
(`sBb`), 0 and an exact root. -/

/-- `a1 := 0` and the steps `t5 := 63` of `lzStep`, on the top nonzero word `s0` (`topW`). -/
def nTop : List Instr := [.li .a1 0, .li .t5 63]

/-- `s8 := c2 = 2 ⌊clz / 2⌋`, `clz = 64 s7 + a1`, masked to 0 where `X = 0` (`sBb`), and `c = c2 / 2` into
`wTmp`'s word 1. -/
def nShift : List Instr :=
  [.shift .sll .d .t2 .s7 6, .add .t2 .t2 .a1, .logicImm .and .t2 .t2 (-2), .load .d .t3 .s11 sBb,
    .addi .t3 .t3 (-1), .logic .and .s8 .t2 .t3, .shift .srl .d .t2 .s8 1] ++ ptr .t3 wTmp ++
    [.store .d .t2 .t3 8]

/-- Normalize `[wR]` (wide): `sBb := [X = 0]`, `c2 = 2 ⌊clz / 2⌋` (0 where `X = 0`), `X := X 2^c2`,
`c = c2 / 2` into `wTmp`'s word 1. -/
def norm : Prog isa := seqs [eqS sBb wR wDig, .block [mov .t0 .s9], clz wR, topW wR, .block nTop, countLoop .t5 lzStep,
  .block nShift, shlBy wR .s8 9]

/-- A step of the first digit's square root by bit pairs, of `T` (`a2:a3`): root `s0`,
remainder `a4:a5`. -/
def pairStep : List Instr :=
  [.shift .sll .d .a4 .a4 2, .shift .srl .d .t2 .a5 62, .logic .or .a4 .a4 .t2, .shift .sll .d .a5 .a5 2,
    .shift .srl .d .t2 .a2 62, .logic .or .a5 .a5 .t2, .shift .sll .d .a2 .a2 2, .shift .srl .d .t2 .a3 62,
    .logic .or .a2 .a2 .t2, .shift .sll .d .a3 .a3 2, .shift .sll .d .s0 .s0 1,
    .shift .sll .d .t3 .s0 1, .logicImm .or .t3 .t3 1, .shift .srl .d .t4 .s0 63,
    .sltu .t6 .a5 .t3, .sub .a6 .a5 .t3, .sltu .a7 .a4 .t4, .sub .t2 .a4 .t4, .sltu .s1 .t2 .t6,
    .sub .t2 .t2 .t6, .logic .or .a7 .a7 .s1, .addi .s1 .a7 (-1),
    .logic .xor .a6 .a6 .a5, .logic .and .a6 .a6 .s1, .logic .xor .a5 .a5 .a6,
    .logic .xor .t2 .t2 .a4, .logic .and .t2 .t2 .s1, .logic .xor .a4 .a4 .t2,
    .logicImm .xor .t6 .a7 1, .logic .or .s0 .s0 .t6]

/-- `s4 :=` `[wR]`'s address, `t1 :=` its word `L - 2`, the top two words `T` into `a2:a3`, the root
`s0` and remainder `a4:a5` zero, and the 64 steps into `t5`. -/
def fHead : List Instr :=
  ptr .s4 wR ++ [.shift .sll .d .t0 .s9 3, .add .t1 .s4 .t0, .addi .t1 .t1 (-16), .load .d .a2 .t1 8,
    .load .d .a3 .t1 0, .li .s0 0, .li .a4 0, .li .a5 0, .li .t5 64]

/-- The remainder over `T`, `s7 :=` `[wSN]`'s address, `s₀` into its word `k - 1`, and `recipHead` for
`s₀` (`s2`). -/
def fMid : List Instr :=
  [.store .d .a5 .t1 0, .store .d .a4 .t1 8] ++ ptr .s7 wSN ++
    [.shift .srl .d .t0 .s9 1, .shift .sll .d .t0 .t0 3, .add .t0 .s7 .t0, .addi .t0 .t0 (-8), .store .d .s0 .t0 0,
      mov .s2 .s0] ++ recipHead

/-- The first digit: `s₀ = ⌊√T⌋` of `X`'s top two words, the remainder over them, `s₀` into
`[wSN]`'s word `k - 1`; its reciprocal into `wTmp`'s word 0. -/
def first : Prog isa := seqs [.block fHead, countLoop .t5 pairStep, .block fMid, countLoop .t5 divBit,
  .block (ptr .t3 wTmp ++ [.store .d .s4 .t3 0])]

/-- One word of `q̂ (2 s β + q̂)` subtracted, `2 s`'s word from `s` (`a6`) and the previous (`t2`). -/
def msBody : List Instr :=
  [.load .d .t3 .a6 0, .shift .sll .d .t4 .t3 1, .shift .srl .d .t5 .t2 63, .logic .or .t4 .t4 .t5, mov .t2 .t3,
    .mul .t3 .s8 .t4, .mulhu .t4 .s8 .t4, .add .t3 .t3 .a4, .sltu .t5 .t3 .a4, .add .t4 .t4 .t5,
    .load .d .t5 .a5 0, .sltu .a0 .t5 .t3, .sub .t5 .t5 .t3, .add .t4 .t4 .a0, .store .d .t5 .a5 0,
    mov .a4 .t4, .addi .a5 .a5 8, .addi .a6 .a6 8]

/-- One word of a masked correction: `2 s` masked (`t3`) added. -/
def corBody : List Instr :=
  [.load .d .t4 .a6 0, .shift .sll .d .t5 .t4 1, .shift .srl .d .t6 .t2 63, .logic .or .t5 .t5 .t6, mov .t2 .t4,
    .logic .and .t5 .t5 .t3, .load .d .t6 .a5 0, .add .t6 .t6 .a4, .sltu .t4 .t6 .a4, .add .t6 .t6 .t5,
    .sltu .t5 .t6 .t5, .add .a4 .t4 .t5, .store .d .t6 .a5 0, .addi .a5 .a5 8, .addi .a6 .a6 8]

/-- A correction's first word: the mask `t3 = 0 - a0` of a negative remainder, `q̂ + (q̂ - 1)` under
it added to word `o` (at `a2`), the carry into `a4`; the loop's pointers and count. -/
def cHead : List Instr :=
  [.li .t2 0, .sub .t3 .t2 .a0, .logic .and .t4 .s8 .t3, .addi .t5 .s8 (-1), .logic .and .t5 .t5 .t3,
    .load .d .t6 .a2 0, .add .t6 .t6 .t4, .sltu .a4 .t6 .t4, .add .t6 .t6 .t5, .sltu .t4 .t6 .t5,
    .add .a4 .a4 .t4, .store .d .t6 .a2 0, .addi .a5 .a2 8, mov .a6 .a3, .addi .a7 .s2 1]

/-- A correction's top word plus the carry, `q̂ - a0`, and `a0` cleared by a carry out. -/
def cTail : List Instr :=
  [.load .d .t6 .a5 0, .add .t6 .t6 .a4, .sltu .t4 .t6 .a4, .store .d .t6 .a5 0, .sub .s8 .s8 .a0,
    .logicImm .xor .t4 .t4 1, .logic .and .a0 .a0 .t4]

/-- A correction: where the remainder is negative (`a0`), `+ 2 s β + 2 q̂ - 1` and `q̂ - 1`. -/
def correct : Prog isa := seqs [.block cHead, countLoop .a7 corBody, .block cTail]

/-- A digit's top three words of the remainder `R` (words `L - m - 2` to `L - m`, `t4`, `t3`, `t2`),
halved: `u = ⌊R / (2 β^m)⌋`, `t5:t6`. -/
def dLoad : List Instr :=
  [.sub .t0 .s9 .s2, .shift .sll .d .t1 .t0 3, .add .t1 .s4 .t1, .addi .t1 .t1 (-16), .load .d .t2 .t1 16,
    .load .d .t3 .t1 8, .load .d .t4 .t1 0, .shift .sll .d .t5 .t2 63, .shift .srl .d .t6 .t3 1,
    .logic .or .t5 .t5 .t6, .shift .sll .d .t6 .t3 63, .shift .srl .d .t4 .t4 1, .logic .or .t6 .t6 .t4]

/-- The estimate `q̂ = ⌊u / s₀⌋` by `s₀`'s reciprocal (`s1`), Möller and Granlund's division
(`Precompute.quotMG`'s), `β - 1` where `u₂ ≥ s₀`, into `s8`. -/
def dEst : List Instr :=
  [.mul .a4 .s1 .t5, .mulhu .a5 .s1 .t5, .add .a4 .a4 .t6, .sltu .a6 .a4 .t6, .add .a5 .a5 .t5,
    .add .a5 .a5 .a6, .addi .a5 .a5 1, .mul .a6 .a5 .s0, .sub .a6 .t6 .a6, .sltu .a7 .a4 .a6, .sub .a5 .a5 .a7,
    .li .t2 0, .sub .t2 .t2 .a7, .logic .and .t2 .t2 .s0, .add .a6 .a6 .t2, .sltu .a7 .a6 .s0,
    .logicImm .xor .a7 .a7 1, .add .a5 .a5 .a7, .sltu .a7 .t5 .s0, .logicImm .xor .a7 .a7 1, .li .t2 0,
    .sub .a7 .t2 .a7, .logic .or .s8 .a5 .a7]

/-- `a2 :=` word `o = L - 2 m - 2` of `[wR]`, `a3 :=` word `k - m` of `[wSN]`, the root's lowest. -/
def dPtr : List Instr :=
  [.shift .sll .d .a2 .s2 4, .shift .sll .d .t0 .s9 3, .sub .a2 .t0 .a2, .addi .a2 .a2 (-16), .add .a2 .s4 .a2,
    .sub .t0 .s3 .s2, .shift .sll .d .t0 .t0 3, .add .a3 .s7 .t0]

/-- `q̂²` off word `o`, the carry into `a4`, and the loop's pointers and count. -/
def dSq : List Instr :=
  [.mul .t3 .s8 .s8, .mulhu .t4 .s8 .s8, .load .d .t5 .a2 0, .sltu .t6 .t5 .t3, .sub .t5 .t5 .t3,
    .add .a4 .t4 .t6, .store .d .t5 .a2 0, .addi .a5 .a2 8, mov .a6 .a3, .li .t2 0, .addi .a7 .s2 1]

/-- The top word less the carry, its borrow the remainder's sign `a0`. -/
def dTop : List Instr := [.load .d .t5 .a5 0, .sltu .a0 .t5 .a4, .sub .t5 .t5 .a4, .store .d .t5 .a5 0]

/-- The digit stored below the root, and the next. -/
def dNext : List Instr := [.addi .t0 .a3 (-8), .store .d .s8 .t0 0, .addi .s2 .s2 1, .addi .a1 .a1 (-1)]

/-- A digit, `m = s2` digits so far. -/
def digit : Prog isa := seqs [.block (dLoad ++ dEst ++ dPtr ++ dSq), countLoop .a7 msBody, .block dTop,
  correct, correct, correct, .block dNext]

/-- `t3 :=` `wTmp`'s address, `s4 :=` `[wR]`'s, `s1 := v`, `s3 := k`, `s0 := s₀` (`[wSN]`'s word
`k - 1`), `s2 := 1` digit, and `a1 := k - 1` to go. -/
def dsHead : List Instr :=
  ptr .t3 wTmp ++ ptr .s4 wR ++ [.load .d .s1 .t3 0, .shift .srl .d .s3 .s9 1, .shift .sll .d .t0 .s3 3,
    .add .t0 .s7 .t0, .addi .t0 .t0 (-8), .load .d .s0 .t0 0, .li .s2 1, .addi .a1 .s3 (-1)]

/-- The digits after the first: `k - 1` of them. -/
def digits : Prog isa := seqs [.block dsHead, .loop digit (.nonzero .a1)]

/-- The square root by words. -/
def sqrt : Prog isa := seqs [.block saveDiv, InvBatch.zeroW wSN, InvBatch.zeroW wDig, norm, first, digits,
  eqS sOk5 wR wDig, .block [.load .d .t2 .s11 sOk5, .load .d .t3 .s11 sBb, .logic .or .t2 .t2 .t3,
    .store .d .t2 .s11 sOk5],
  .block (ptr .t3 wTmp ++ [.load .d .s8 .t3 8]), shrBy wSN .s8 8,
  .block restDiv, .block ctxw, copy aSy (2 * wSN), sel aSy aSy aZero sBb]

/-! ## The factors -/

/-- The mask: `d e ≥ 2`, `m < n`, the exact division, `b² > 4 n` and the
exact square root. -/
def maskOf : List Instr :=
  [.load .d .t5 .s11 sB0, .logicImm .xor .t5 .t5 1, .load .d .t6 .s11 sB1, .logicImm .xor .t6 .t6 1,
    .logic .and .t5 .t5 .t6, .load .d .t6 .s11 sLt, .logic .and .t5 .t5 .t6,
    .load .d .t6 .s11 sExact, .logic .and .t5 .t5 .t6,
    .load .d .t6 .s11 sC1, .logicImm .xor .t6 .t6 1, .logic .and .t5 .t5 .t6,
    .load .d .t6 .s11 sC2, .logicImm .xor .t6 .t6 1, .logic .and .t5 .t5 .t6,
    .load .d .t6 .s11 sOk5, .logic .and .t5 .t5 .t6, .store .d .t5 .s11 sMask]

/-- `p = (b + ϒ) / 2` and `q = (b - ϒ) / 2`, and the mask. -/
def factors : Prog isa := seqs [add aP aD aSy aZero aNy, .block [.li .t4 0], half aP,
  sub3 aQ aD aSy, .block [.li .t4 0], half aQ, .block maskOf]

/-- The mask `0 - [sMask]` into `t4`. -/
def mask : List Instr := [.load .d .t4 .s11 sMask, .li .t5 0, .sub .t4 .t5 .t4]

/-- The factors written out under the mask, and the mask returned. -/
def stores : Prog isa := seqs [.block mask, storeBytes aP .s3 .s2, storeBytes aQ .s4 .s2,
  .block [.load .d .a0 .s11 sMask]]

/-! ## The function -/

/-- `w`, the stride and every array zeroed. -/
def setup : Prog isa := .seq (.block ctxInit) (zeroArrays nArr)

def det : Prog isa := seqs [deMinus, twos, gcd, divA, divB, minus4n, sqrt, factors]

/-- Once `n` is known valid. -/
def valid : Prog isa := seqs [setup, loads, prod, det, stores]

/-- `vg_rsa_recover_primes_det`. -/
def code : Prog isa :=
  .seq (.block entry) (.seq nCheck (.seq (.ite (.zero .s0) valid fail) (.block restore)))

end VG.Impl.Rsa.RISCV64.RecoverDet
