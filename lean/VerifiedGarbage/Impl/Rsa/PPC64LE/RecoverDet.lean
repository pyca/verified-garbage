module

public import VerifiedGarbage.Impl.Rsa.PPC64LE.MulMod
public import VerifiedGarbage.Impl.Rsa.PPC64LE.CrtValues
public import VerifiedGarbage.Impl.Bignum.PPC64LE.Precompute
public import VerifiedGarbage.Impl.Bignum.PPC64LE.PublicChecked
public import VerifiedGarbage.Impl.Rsa.PPC64LE.InvBatch

/-! # `vg_rsa_recover_primes_det` on PPC64LE

SP 800-56B Rev. 2 Appendix C.2 without a branch on a secret, after the
entry, the check of `n`, the loads and the product `d e` (in the namespace
`Recover`, with the stores and the exits): the numbers are `w` digits
(narrow) or, in the same working space read with `W = 2 w + 2` digits, wide,
wide array `j` being the narrow arrays `2 j` and `2 j + 1`. A narrow number
copied into the low half of a wide array of zeros is that wide number.

* `x = d e - 1` (wide), and whether `d e ≥ 2`;
* `32 w` steps that halve `u = n - 1` while it is even, and while `x` is even
  too halve it and double `2^k x` (all wide), then `gcd(u, x)` by the
  batched divsteps without the inverse (`InvBatch.gcd`, on narrow arrays),
  with 1 where `u = 1`, which the GCD leaves to its caller;
* `a = (2^k x) gcd(u, x)` modulo `2^(32 W)` by the `32 w` bits of the GCD,
  doubling the multiplicand (`product`), and `m = ⌊a / n⌋`, `r = a mod n`
  (`Div.div`, wide);
* `b - 1 = (n - r) / (m + 1)` (`Div.div`, narrow), `b²` (`product`) and
  `b² - 4 n`;
* its square root, two bits at a time from the top in `16 W` steps (`sqrtBody`):
  the wide radicand shifted left into the narrow remainder (`shlC`, whose
  carry in is `r9`), which keeps `4 y + 1` where it fits;
* `p = (b + ϒ) / 2` and `q = (b - ϒ) / 2`, written under the mask of every
  check (`Recover.stores`).

Each loop counts down in `r27`, set from `w`; the operations keep it. The
addresses and branches depend only on `w` and the base, as in the
operations of the key working space (`KeyWs.lean`).
-/

@[expose] public section

namespace VG.Impl.Rsa.PPC64LE.Recover

open VG.PPC64LE VG.Impl.Rsa.PPC64LE.Keys VG.Impl.Rsa.PPC64LE.Div

/-! ## The header

Bytes 0–39 are the function's slots, 124–132 the shared routines', and 152
the mask of the result (`CrtValues.sMask`, which `CrtValues.mask` reads). -/

def sMask : Nat := CrtValues.sMask

/-! ## The arrays

With `w` digits: `n` (32), 1 (33) and 0 (34). Arrays 44–45 hold the saved
registers. -/

def aN : Nat := 32
def aOne : Nat := 33
def aZ : Nat := 34
/-- The number of arrays zeroed; the saved registers are in the next two. -/
def nArr : Nat := 44

/-- With `W` digits: zero, `e`, `d` and `M = d e`. -/
def wZ : Nat := 0
def wE : Nat := 1
def wD : Nat := 2
def wM : Nat := 3

/-! ## Contexts -/

/-- `W = 2 w + 2` into `r29` and its stride into `r30`. -/
def ctxW : List Instr := [.lsl .r29 .r29 1, .addi .r29 .r29 2] ++ stride

/-- Back to `w = (W - 2) / 2`. -/
def ctxw : List Instr := [.subi .r29 .r29 2, .lsr .d .r29 .r29 1] ++ stride

/-! ## Entry and exit -/

/-- The nonvolatile registers, in the order they are saved. -/
def savedReg (i : Nat) : Reg :=
  [.r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r25, .r26, .r27, .r28, .r29, .r30,
    .r31].getD i .r14

/-- `w = 2 ⌈n_len / 8⌉ + 2` into `rd`, from `n_len` in `r8`. -/
def wOf (rd : Reg) : List Instr := [.addi rd .r8 7, .lsr .d rd rd 3, .lsl rd rd 1, .addi rd rd 2]

/-- The base of the key array `nArr` into `rd`, the working space's base in
`b` and the stride in `s`. -/
def saveBase (rd b s : Reg) : List Instr := [.li rd nArr, .mul rd rd s, .add rd rd b, .addi rd rd hdr]

/-- The working space's base into `r11` and the nonvolatile registers saved
in its arrays 44–45 (through `r12`). -/
def save : List Instr :=
  CrtValues.stackArg .r11 2 ++ wOf .r12 ++ [.addi .r0 .r12 2, .lsl .r0 .r0 2] ++ saveBase .r12 .r11 .r0 ++
    (List.range 18).map (fun i => .store .d (savedReg i) .r12 (8 * i))

/-- The working space's base, `w` and the stride; `p`, `q`, `n`, `n_len`,
`e`, `e_len` kept, and `d` and `d_len` from the stack. -/
def entry : List Instr :=
  save ++ [.addi .r31 .r11 0] ++ wOf .r29 ++ stride ++
  [.addi .r21 .r3 0, .addi .r23 .r5 0, .addi .r24 .r7 0, .addi .r25 .r8 0, .addi .r26 .r9 0,
    .addi .r27 .r10 0] ++
  CrtValues.stackArg .r28 0 ++ CrtValues.stackArg .r22 1

/-- `n` checked: 0 in `r0` if it is valid. -/
def nCheck : Prog isa := .seq (.block [.addi .r9 .r24 0, .addi .r10 .r25 0]) CrtValues.check

/-- The saved registers restored, through `r11`, `r31` last. -/
def restore : List Instr :=
  saveBase .r11 .r31 .r30 ++ (List.range 18).map (fun i => .load .d (savedReg i) .r11 (8 * i))

/-- Zeros to `p` and `q`, and 0 returned. -/
def fail : Prog isa := seqs [
  .block [.addi .r5 .r21 0, .addi .r8 .r25 0], CrtValues.zeroBytes,
  .block [.addi .r5 .r23 0, .addi .r8 .r25 0], CrtValues.zeroBytes,
  .block [.li .r3 0]]

/-! ## The numbers -/

/-- Every array zeroed. -/
def zeroAll : Prog isa := .seq (.block [.li .r8 nArr, .mul .r8 .r8 .r30, .lsr .d .r8 .r8 2]) (zeroArrays .r8)

/-- `[j] :=` the `rL` bytes at `rP`. -/
def loadR (rP rL : Reg) (j : Nat) : List (Prog isa) :=
  [.block [.addi .r6 rP 0, .addi .r8 rL 0], CrtValues.load j]

/-- `n` read, then with `W` `e` and `d` (to the arrays `wE` and `wD`), and
`c = 8 (e_len + d_len)` into `r26`. -/
def loads : Prog isa :=
  seqs ([zeroAll] ++ loadR .r24 .r25 aN ++ [.block ctxW] ++ loadR .r26 .r27 wE ++ loadR .r28 .r22 wD ++
    [.block [.add .r26 .r27 .r22, .lsl .r26 .r26 3]])

/-! ## Products by words -/

/-- One row of `mulW`: word `i` of `[x]` (at `r10`) times `[y]`'s `w / 2 - i` low words added at
word `i` of `[o]`, the carry dropped (`InvBatch.macWBody`). -/
def mulWRow (o x y : Nat) : Prog isa :=
  .seq (.block ([.load .d .r11 .r10 0] ++ ptr .r5 o ++ ptr .r6 x ++
      [.sub .r6 .r10 .r6, .lsr .d .r8 .r29 1, .lsr .d .r3 .r6 3, .sub .r8 .r8 .r3, .add .r5 .r5 .r6,
        .addi .r6 .r5 0] ++ ptr .r7 y ++ [.li .r9 0]))
    (.seq (countLoop .r8 InvBatch.macWBody) (.block [.addi .r10 .r10 8, .subi .r4 .r4 1]))

/-- `[o] := [x] [y] mod 2^(32 w)`, `w` even, over the low `R` words of `[x]` (`R` in `r4`, `1 ≤ R ≤ w / 2`):
`[o]`'s `w / 2` words zeroed, then a row of 64-bit words for each word of `[x]`. -/
def mulW (o x y : Nat) : Prog isa := seqs [
  .block (ptr .r5 o ++ [.lsr .d .r8 .r29 1, .li .r0 0]), InvBatch.zerosW,
  .block (ptr .r10 x), .loop (mulWRow o x y) (.nonzero .d .r4)]

/-- `M := d e`, with `W`: a row for each of `e`'s `⌈e_len / 8⌉` words. -/
def prod : Prog isa := .seq (.block [.addi .r4 .r27 7, .lsr .d .r4 .r4 3]) (mulW wM wE wD)

/-! ## The factors -/

/-- The digit above the `w` of `[j]` cleared, as the division's divisor needs. -/
def clrW (j : Nat) : List Instr := ptr .r5 j ++ [.lsl .r0 .r29 2, .add .r5 .r5 .r0, .li .r0 0, .store .w .r0 .r5 0]

/-- The factors written out under the mask, and the mask returned. -/
def stores : Prog isa := seqs [
  .block ([.addi .r5 .r21 0, .addi .r8 .r25 0] ++ CrtValues.mask), CrtValues.storeBytes 5,
  .block ([.addi .r5 .r23 0, .addi .r8 .r25 0] ++ CrtValues.mask), CrtValues.storeBytes 6,
  .block [.load .w .r3 .r31 sMask]]

end VG.Impl.Rsa.PPC64LE.Recover

namespace VG.Impl.Rsa.PPC64LE.RecoverDet

open VG.PPC64LE VG.Impl.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Recover (ctxW ctxw clrW)

/-! ## The header's slots

Bytes 0–55 are the function's slots; 124–132 are the shared routines' and
152 the mask (`Recover.sMask`). -/

/-- `d e < 1` and `d e - 1 < 1`. -/
def sB0 : Nat := 0
def sB1 : Nat := 4
/-- A step of the halvings: the low bits of `u` and `x`, `u` even, and both even. -/
def sU : Nat := 8
def sX : Nat := 12
def sEven : Nat := 16
def sBoth : Nat := 20
/-- A product's multiplier bit. -/
def sY : Nat := 24
/-- `m < n`. -/
def sLt : Nat := 28
/-- `(n - r) mod (m + 1) = 0`. -/
def sExact : Nat := 32
/-- `b² < 4 n` and `b² - 4 n < 1`. -/
def sC1 : Nat := 36
def sC2 : Nat := 40
/-- The square root's borrow. -/
def sBb : Nat := 44
/-- The square root's remainder is zero. -/
def sOk5 : Nat := 48
/-- `u = 1`. -/
def sU1 : Nat := 52

/-! ## The arrays

Wide: zero (from the loads), `d e` (`Recover.wM`), one, `x`, a temporary,
`2^k x`, `x` halved, `u` (later `b`), zero, the multiplier, the product, the
remainder, `n`, the division's temporary, and the negated addend. -/

def wZ : Nat := 0
def wDE : Nat := 3
def wOne : Nat := 9
def wX : Nat := 10
def wT : Nat := 11
def wX3 : Nat := 12
def wX2 : Nat := 13
def wU : Nat := 14
def wZero : Nat := 15
def wY : Nat := 8
def wA : Nat := 17
def wR : Nat := 18
def wN : Nat := 19
def wDt : Nat := 21
def wNg : Nat := 20

/-- Narrow: `n` (`Recover.aN`), the low halves of the wide arrays, one, and
the GCD's input `x` (array 0), modulus (array 8) and result (array 1). -/
def aN : Nat := 32
def aX : Nat := 20
def aX2 : Nat := 26
def aU : Nat := 28
def aZero : Nat := 30
def aY : Nat := 16
def aM : Nat := 34
def aRlo : Nat := 36
def aWN : Nat := 38
def aOne : Nat := 42
/-- `n - 1`, before it is copied into the zeroed wide `wU`. -/
def aTu : Nat := 40
def aGx : Nat := 0
def aGm : Nat := 8
def aG : Nat := 1
/-- The second division: one, `-1`, `m + 1`, `n - r` (then `b - 1` and `b`),
its remainder and temporary; `b` into the low half of `wU`. -/
def aOne2 : Nat := 22
def aNeg1 : Nat := 23
def aM1 : Nat := 24
def aD : Nat := 25
def aRem : Nat := 26
def aDt : Nat := 27
/-- The square root: remainder, root, `4 y + 1`, difference; `-y`; the factors. -/
def aRm : Nat := 2
def aSy : Nat := 4
def aTy : Nat := 6
def aDf : Nat := 8
def aNy : Nat := 9
def aP : Nat := 5
def aQ : Nat := 6

/-! ## Operations -/

/-- `[j] := 2 [j] + r9` modulo `2^(32 w)`, for `r9` 0 or 1, the bit shifted
out in `r9`. -/
def shlC (j : Nat) : Prog isa :=
  .seq (.block (ptr .r5 j))
    (evenW (.seq (.block [.lsr .d .r8 .r29 1]) (countLoop .r8 Div.shlWBody))
      (.seq (.block [.addi .r8 .r29 0]) (countLoop .r8 Div.shlBody)))

/-- `[j] := 2 [j]` modulo `2^(32 w)`, the bit shifted out in `r9`. -/
def shl (j : Nat) : Prog isa := .seq (.block [.li .r9 0]) (shlC j)

/-- `[o] := [a] + [b]` modulo `2^(32 w)`, through `[t] = [z] - [b]`, with
`[z]` zero. -/
def add (o a b z t : Nat) : Prog isa := .seq (sub3 t z b) (sub3 o a t)

/-- `32 w` steps into `r27`, from `w`. -/
def countN : List Instr := [.lsl .r27 .r29 5]

/-- `16 W = 32 w + 32` steps into `r27`, from `w`. -/
def countS : List Instr := [.lsl .r27 .r29 5, .addi .r27 .r27 32]

/-- A step less. -/
def next : List Instr := [.subi .r27 .r27 1]

/-! ## `d e - 1` (wide) -/

/-- One (`wOne`), `x = d e - 1`, and the borrows of `d e - 1` and `x - 1`;
the zero `wZero`, which the GCD leaves alone. -/
def deMinus : Prog isa := seqs [copy wOne wZ, .block (setOne wOne),
  sub3 wX wDE wOne, .block (stBorrow sB0), sub3 wT wX wOne, .block (stBorrow sB1), copy wZero wZ]

/-! ## The halvings -/

/-- `2^k x := x`, `x` and `u = n - 1` copied into zeroed wide arrays (through
the narrow view), the multiplier's wide array zeroed, and `32 w` steps. -/
def twosInit : Prog isa := seqs [copy wX3 wX, copy wX2 wZero, copy wU wZero, copy wY wZero,
  .block ctxw, copy aX2 aX, copy aOne aZero, .block (setOne aOne), sub3 aTu aN aOne,
  copy aU aTu, .block (countN ++ ctxW)]

/-! ## Shifts by a count, by stages

`shlBy j sw sb bits` and `shrBy j sw sb` shift the wide array `j` (its
`L = W / 2` words) up (modulo `2^(64 L)`) or down by `64 c_w + c_b` bits, the
counts in the slots `sw` and `sb`: by `2^k` words where bit `k` of `c_w` is
set, for each `2^k < L`, then (for `shlBy`, if `bits`) by `2^k` bits where bit
`k` of `c_b < 64` is set. Each stage runs over every word whatever its bit,
which only chooses by a mask (`r9`, and its complement `r12`). -/

/-- `r7 := L = W / 2`, the words of a wide array. -/
def lenW : List Instr := [.lsr .d .r7 .r29 1]

/-- `r9 :=` all ones if bit `s` (`r11`, a power of two) of the slot `sl` is set, else zero; `r12 := ¬r9`. -/
def wordMask (sl : Nat) : List Instr :=
  [.load .w .r10 .r31 sl, .logic .and .r3 .r10 .r11, .li .r0 0, .sub .r0 .r0 .r3, .logic .or .r3 .r3 .r0,
    .lsr .d .r3 .r3 63, .li .r0 0, .sub .r9 .r0 .r3, .subi .r12 .r3 1]

/-- `[j]`'s `L` words shifted up by `s` (`r11`) words where the mask `r9` is set (`r12` its
complement), from the top: word `i ≥ s` takes word `i - s`, and words below `s` are cleared. -/
def shlWords (j : Nat) : Prog isa := seqs [
  .block (ptr .r5 j ++ lenW ++ [.lsl .r0 .r7 3, .add .r5 .r5 .r0, .subi .r5 .r5 8, .lsl .r0 .r11 3, .sub .r6 .r5 .r0,
    .sub .r8 .r7 .r11]),
  countLoop .r8 [.load .d .r0 .r5 0, .load .d .r3 .r6 0, .logic .xor .r3 .r3 .r0, .logic .and .r3 .r3 .r9,
    .logic .xor .r3 .r3 .r0, .store .d .r3 .r5 0, .subi .r5 .r5 8, .subi .r6 .r6 8],
  .block [.addi .r8 .r11 0],
  countLoop .r8 [.load .d .r0 .r5 0, .logic .and .r0 .r0 .r12, .store .d .r0 .r5 0, .subi .r5 .r5 8]]

/-- `[j]`'s `L` words shifted down by `s` (`r11`) words where the mask `r9` is set (`r12` its
complement), from the bottom: word `i < L - s` takes word `i + s`, and the top `s` are cleared. -/
def shrWords (j : Nat) : Prog isa := seqs [
  .block (ptr .r5 j ++ lenW ++ [.lsl .r0 .r11 3, .add .r6 .r5 .r0, .sub .r8 .r7 .r11]),
  countLoop .r8 [.load .d .r0 .r5 0, .load .d .r3 .r6 0, .logic .xor .r3 .r3 .r0, .logic .and .r3 .r3 .r9,
    .logic .xor .r3 .r3 .r0, .store .d .r3 .r5 0, .addi .r5 .r5 8, .addi .r6 .r6 8],
  .block [.addi .r8 .r11 0],
  countLoop .r8 [.load .d .r0 .r5 0, .logic .and .r0 .r0 .r12, .store .d .r0 .r5 0, .addi .r5 .r5 8]]

/-- The word stages of `sh`: `s = 1, 2, 4, …` (`r11`) while `s < L`, each under bit `s` of the slot `sl`. -/
def wordStages (sl : Nat) (sh : Prog isa) : Prog isa := .seq (.block [.li .r11 1])
  (.loop (seqs [.block (wordMask sl), sh, .block (lenW ++ [.lsl .r11 .r11 1, .sub .r0 .r11 .r7, .lsr .d .r0 .r0 63])])
    (.nonzero .d .r0))

/-- `r9 :=` all ones if bit `b` of the slot `sl` is set, else zero. -/
def bitMask (sl b : Nat) : List Instr :=
  [.load .w .r10 .r31 sl, .li .r3 b, .logic .and .r3 .r10 .r3, .li .r0 0, .sub .r0 .r0 .r3, .logic .or .r3 .r3 .r0,
    .lsr .d .r3 .r3 63, .li .r0 0, .sub .r9 .r0 .r3]

/-- `[j]` shifted down by `b` bits where the mask `r9` is set: word `i` := its high `64 - b`
bits and the low `b` of word `i + 1` (disjoint, so added). -/
def shrBits (j b : Nat) : Prog isa := seqs [
  .block (ptr .r5 j ++ lenW ++ [.subi .r8 .r7 1]),
  countLoop .r8 [.load .d .r0 .r5 0, .load .d .r3 .r5 8, .lsl .r3 .r3 (64 - b), .lsr .d .r6 .r0 b,
    .add .r3 .r6 .r3, .logic .xor .r3 .r3 .r0, .logic .and .r3 .r3 .r9, .logic .xor .r3 .r3 .r0,
    .store .d .r3 .r5 0, .addi .r5 .r5 8],
  .block [.load .d .r0 .r5 0, .lsr .d .r3 .r0 b, .logic .xor .r3 .r3 .r0, .logic .and .r3 .r3 .r9,
    .logic .xor .r3 .r3 .r0, .store .d .r3 .r5 0]]

/-- `[j]` shifted up by `b` bits modulo `2^(64 L)` where the mask `r9` is set. -/
def shlBits (j b : Nat) : Prog isa := seqs [
  .block (ptr .r5 j ++ lenW ++ [.lsl .r0 .r7 3, .add .r5 .r5 .r0, .subi .r5 .r5 8, .subi .r6 .r5 8,
    .subi .r8 .r7 1]),
  countLoop .r8 [.load .d .r0 .r5 0, .load .d .r3 .r6 0, .lsr .d .r3 .r3 (64 - b), .lsl .r10 .r0 b,
    .add .r3 .r3 .r10, .logic .xor .r3 .r3 .r0, .logic .and .r3 .r3 .r9, .logic .xor .r3 .r3 .r0,
    .store .d .r3 .r5 0, .subi .r5 .r5 8, .subi .r6 .r6 8],
  .block [.load .d .r0 .r5 0, .lsl .r3 .r0 b, .logic .xor .r3 .r3 .r0, .logic .and .r3 .r3 .r9,
    .logic .xor .r3 .r3 .r0, .store .d .r3 .r5 0]]

/-- The bit stages `b = 32, …, 1` of `sh`, each under bit `b` of the slot `sl`. -/
def bitStages (sl : Nat) (sh : Nat → Prog isa) : List Nat → Prog isa
  | [] => .block []
  | b :: bs => seqs [.block (bitMask sl b), sh b, bitStages sl sh bs]

/-- The bit stages' sizes. -/
def bitSizes : List Nat := [32, 16, 8, 4, 2, 1]

/-- `[j]` shifted up by the counts in the slots `sw` (words) and, if `bits`, `sb` (bits). -/
def shlBy (j sw sb : Nat) (bits : Bool) : Prog isa :=
  .seq (wordStages sw (shlWords j)) (if bits then bitStages sb (shlBits j) bitSizes else .block [])

/-- `[j]` shifted down by the counts in the slots `sw` (words) and `sb` (bits). -/
def shrBy (j sw sb : Nat) : Prog isa := .seq (wordStages sw (shrWords j)) (bitStages sb (shrBits j) bitSizes)

/-! ## Counts of zeros, in constant time -/

/-- `r4 := h = w / 2 - 1`, the words of `n`. -/
def hW : List Instr := [.lsr .d .r4 .r29 1, .subi .r4 .r4 1]

/-- The slot `sl` := the leading zero words of `[m]`'s low `h` words (narrow): a mask, all
ones while every word so far from the top is zero. -/
def clzW (m sl : Nat) : Prog isa := seqs [
  .block (ptr .r5 m ++ hW ++ [.lsl .r0 .r4 3, .add .r5 .r5 .r0, .subi .r5 .r5 8, .addi .r8 .r4 0, .li .r9 0,
    .subi .r9 .r9 1, .li .r10 0]),
  countLoop .r8 [.load .d .r0 .r5 0, .li .r3 0, .sub .r3 .r3 .r0, .logic .or .r3 .r3 .r0, .lsr .d .r3 .r3 63,
    .subi .r3 .r3 1, .logic .and .r9 .r9 .r3, .li .r3 1, .logic .and .r3 .r9 .r3, .add .r10 .r10 .r3, .subi .r5 .r5 8],
  .block [.store .w .r10 .r31 sl]]

/-- A stage of a word's trailing zeros (`r11`, their count in `r10`): if its low `b = 2^lg`
bits are zero, `b` more and the word shifted down by `b`. -/
def tzStage (b lg : Nat) : List Instr :=
  [.lsl .r3 .r11 (64 - b), .li .r0 0, .sub .r0 .r0 .r3, .logic .or .r3 .r3 .r0,
    .lsr .d .r3 .r3 63, .li .r0 1, .logic .xor .r3 .r3 .r0, .lsl .r0 .r3 lg, .add .r10 .r10 .r0, .li .r0 0,
    .sub .r9 .r0 .r3, .lsr .d .r0 .r11 b, .logic .xor .r0 .r0 .r11, .logic .and .r0 .r0 .r9,
    .logic .xor .r11 .r11 .r0]

/-- The slots `sw` and `sb` := the trailing zero words of `[a] ∨ [b]` (wide), and the trailing
zero bits of its lowest word that is not zero: a mask, all ones while every word so far is zero,
selects that word; then its stages. -/
def tzW (a b sw sb : Nat) : Prog isa := seqs [
  .block (ptr .r5 a ++ ptr .r6 b ++ lenW ++ [.addi .r8 .r7 0, .li .r9 0, .subi .r9 .r9 1, .li .r10 0, .li .r11 0]),
  countLoop .r8 [.load .d .r0 .r5 0, .load .d .r3 .r6 0, .logic .or .r0 .r0 .r3, .logic .and .r3 .r0 .r9,
    .logic .or .r11 .r11 .r3, .li .r3 0, .sub .r3 .r3 .r0, .logic .or .r3 .r3 .r0, .lsr .d .r3 .r3 63,
    .subi .r3 .r3 1, .logic .and .r9 .r9 .r3, .li .r3 1, .logic .and .r3 .r9 .r3, .add .r10 .r10 .r3,
    .addi .r5 .r5 8, .addi .r6 .r6 8],
  .block ([.store .w .r10 .r31 sw, .li .r10 0] ++ tzStage 32 5 ++ tzStage 16 4 ++ tzStage 8 3 ++ tzStage 4 2 ++
    tzStage 2 1 ++ tzStage 1 0 ++ [.store .w .r10 .r31 sb])]

/-! ## The halvings, by counts -/

/-- The slots of the trailing zeros: of `u` and of `u ∨ x`, in words and bits. -/
def sUw : Nat := 60
def sUb : Nat := 64
def sTw : Nat := 68
def sTb : Nat := 72

/-- `t = tz(u ∨ x)`: `u` shifted down by its trailing zeros, `x` (in `wX2`) down by `t` and
`2^t x` (`wX3`) up. -/
def twos : Prog isa := seqs [twosInit, tzW wU wU sUw sUb, tzW wU wX2 sTw sTb, shrBy wU sUw sUb,
  shrBy wX2 sTw sTb, shlBy wX3 sTw sTb true, .block [.li .r27 0]]

/-! ## The GCD (narrow) -/

/-- `gcd(u, x)` into array 1: the GCD's inputs, `n = w`, and 1 where
`u = 1`. Then the GCD into the low half of `wY`. -/
def gcd : Prog isa := seqs [.block ctxw, copy aGx aX2, copy aGm aU, .block [.addi .r11 .r29 0],
  InvBatch.gcd, eqS sU1 aGm aOne, sel aG aG aOne sU1, copy aY aG]

/-! ## Products: `[a] := ([y] mod 2^(32 w)) [x]` modulo `2^(32 W)`, by rows of words (`Recover.mulW`) -/

/-- `a = 2^k x gcd(u, x)`, from the narrow view: the GCD's `4 w` digits. -/
def aProduct : Prog isa := seqs [.block ([.lsr .d .r4 .r29 1] ++ ctxW), Recover.mulW wA wY wX3]

/-! ## The divisions -/

/-- `m` and `r` (wide), with `n` wide, and whether `m < n`: one word division
(`KeyDiv.divQ`) on the wide view, of `W / 2 = w + 1` words by `n`'s `h = (W - 6) / 4`
words, through the wide arrays 21 and 20. -/
def divA : Prog isa := seqs [copy wN wZero, .block ctxw, copy aWN aN, .block ctxW,
  KeyDiv.divQ wA wR wN wDt wNg [.subi .r11 .r29 6, .lsr .d .r11 .r11 1] [.lsr .d .r4 .r29 1],
  sub3 wNg wA wN, .block (stBorrow sLt)]

/-- The second division (wide): the divisor `m + 1` (4) and dividend `n - r` (5), both shifted
up by the divisor's leading zero words (slot `sCz`), the remainder (6), the temporary (7) and the
save area (3). -/
def wD1 : Nat := 4
def wNN : Nat := 5
def wRm : Nat := 6
def wTq : Nat := 7
def wSq : Nat := 3
def aD1 : Nat := 8
def aNN : Nat := 10
def sCz : Nat := 56

/-- The divisor's word `h - 1` (wide `j`, `W = 4 h + 6`) or'ed with whether it is zero: a no-op
where `m < n`, as the word is not zero once shifted, and otherwise what the division needs. -/
def fixTop (j : Nat) : List Instr := ptr .r5 j ++ [.subi .r11 .r29 6, .lsl .r11 .r11 1, .add .r5 .r5 .r11,
  .subi .r5 .r5 8, .load .d .r0 .r5 0, .li .r3 0, .sub .r3 .r3 .r0, .logic .or .r3 .r3 .r0, .lsr .d .r3 .r3 63,
  .li .r9 1, .logic .xor .r3 .r3 .r9, .logic .or .r0 .r0 .r3, .store .d .r0 .r5 0]

/-- `m + 1` and `n - r` (narrow), their quotient (`b - 1`, narrow) and whether the remainder is
zero: both shifted up by the divisor's leading zero words, and one word division (wide). -/
def divB : Prog isa := seqs [.block ctxw, copy aOne2 aZero, .block (setOne aOne2), sub3 aNeg1 aZero aOne2,
  sub3 aM1 aM aNeg1, sub3 aD aN aRlo, clzW aM1 sCz, .block ctxW, copy wD1 wZero, copy wNN wZero, .block ctxw,
  copy aD1 aM1, copy aNN aD, .block ctxW, shlBy wD1 sCz sCz false, .block (fixTop wD1), shlBy wNN sCz sCz false,
  KeyDiv.divQ wNN wRm wD1 wTq wSq [.subi .r11 .r29 6, .lsr .d .r11 .r11 1] [.lsr .d .r4 .r29 1],
  eqS sExact wRm wZero, .block ctxw, copy aD aNN]

/-! ## `b² - 4 n` -/

/-- `b` (narrow in `aD`, and into the zeroed wide `wU` and `wY`) and `b²` in `wA`. -/
def square : Prog isa := seqs [sub3 aD aD aNeg1, .block ctxW, copy wU wZero, copy wY wZero,
  .block ctxw, copy aU aD, copy aY aD, .block ([.lsr .d .r4 .r29 1] ++ ctxW), Recover.mulW wA wY wU]

/-- `b² - 4 n` in `wR`, and whether `b² < 4 n` and `b² - 4 n < 1`. -/
def minus4n : Prog isa := seqs [shl wN, shl wN, sub3 wR wA wN, .block (stBorrow sC1),
  sub3 wNg wR wOne, .block (stBorrow sC2)]

/-! ## The square root, by words

`X` (wide `[wR]`, its low `2 h` words; `1` in place of `0`, the root less
one at the end) is normalized, `X' = X 2^(2 c)` for `c = ⌊z / 2⌋` and `z` its
leading zero bits in `2 h` words. The root `s` of `X'` is found a word at a
time from the top, in `D = 2 s`, kept top-aligned (its top word at `h`): its
first word `s₀ ≥ 2^63` from `X'`'s top two words (64 steps of two bits, in
registers), then for `j = 1 … h - 1` the digit `q` into `D`'s word
`m = h - 1 - j`, from the remainder `r`, kept in place in `X'`, and the next
two words `P`, `R = r β² + P` (`X'`'s words `2 m … 2 m + j + 2`):
`q̂ = min(⌊U / (s₀ β + s₁)⌋, β - 1)` for `⌊R / 2⌋`'s top three words `U`
(`Precompute.quot`, `quot3`, by the reciprocal of `s₀`, computed once), at
most two more than `q`; `T = R - q̂ (2 s β + q̂)` in place by one multiply and
subtract with `D`'s word `m` set to `q̂`; two masked corrections `T := T + 2 s β
+ 2 q̂ - 1`, `q̂ := q̂ - 1` where `T < 0`; then `D`'s word `m` and `m + 1` := `2 s'`'s.
The root of `X` is `D` shifted down by `c + 1`, and `X` is a square exactly
where the last remainder is zero. -/

open VG.Impl.Bignum.PPC64LE.Precompute (recip quotMG quotFix quot3)

/-- `D = 2 s` (wide, top-aligned at word `h`) and a temporary (`P = 1` at word 0, `s₀` at 1, its
reciprocal at 2, `s₁` at 3, `U`'s low word at 5). -/
def wS : Nat := 2
def wTmp : Nat := 3
/-- The slots: `X`'s shift `2 c` (words and bits), `D`'s `c + 1`, and whether `X = 0`. -/
def sQw : Nat := 76
def sQb : Nat := 80
def sRw : Nat := 84
def sRb : Nat := 88
def sZ : Nat := 92

/-- `r11 := 2 h` from `W = 4 h + 6`. -/
def twoH : List Instr := [.subi .r11 .r29 6, .lsr .d .r11 .r11 1]

/-- Whether `X`'s `2 h` words are zero, into `sZ`, and then `X := 1` if so. -/
def zeroX : Prog isa := seqs [
  .block (ptr .r5 wR ++ twoH ++ [.addi .r8 .r11 0, .li .r9 0]),
  countLoop .r8 [.load .d .r0 .r5 0, .logic .or .r9 .r9 .r0, .addi .r5 .r5 8],
  .block (ptr .r5 wR ++ [.li .r3 0, .sub .r3 .r3 .r9, .logic .or .r3 .r3 .r9, .lsr .d .r3 .r3 63, .li .r0 1,
    .logic .xor .r3 .r3 .r0, .store .w .r3 .r31 sZ, .load .d .r0 .r5 0, .logic .or .r0 .r0 .r3, .store .d .r0 .r5 0])]

/-- The scan from the top of `X`'s `2 h` words: `r10 :=` the zero words and `r11 :=` the top word
that is not zero. -/
def clzX : Prog isa := seqs [
  .block (ptr .r5 wR ++ twoH ++ [.lsl .r0 .r11 3, .add .r5 .r5 .r0, .subi .r5 .r5 8, .addi .r8 .r11 0, .li .r9 0,
    .subi .r9 .r9 1, .li .r10 0, .li .r11 0]),
  countLoop .r8 [.load .d .r0 .r5 0, .logic .and .r3 .r0 .r9, .logic .or .r11 .r11 .r3, .li .r3 0,
    .sub .r3 .r3 .r0, .logic .or .r3 .r3 .r0, .lsr .d .r3 .r3 63, .subi .r3 .r3 1, .logic .and .r9 .r9 .r3,
    .li .r3 1, .logic .and .r3 .r9 .r3, .add .r10 .r10 .r3, .subi .r5 .r5 8]]

/-- A stage of a word's leading zeros (`r11`, their count in `r12`): if its top `b = 2^lg`
bits are zero, `b` more and the word shifted up by `b`. -/
def clzStage (b lg : Nat) : List Instr :=
  [.lsr .d .r3 .r11 (64 - b), .li .r0 0, .sub .r0 .r0 .r3, .logic .or .r3 .r3 .r0,
    .lsr .d .r3 .r3 63, .li .r0 1, .logic .xor .r3 .r3 .r0, .lsl .r0 .r3 lg, .add .r12 .r12 .r0, .li .r0 0,
    .sub .r6 .r0 .r3, .lsl .r0 .r11 b, .logic .xor .r0 .r0 .r11, .logic .and .r0 .r0 .r6,
    .logic .xor .r11 .r11 .r0]

/-- The counts into the slots, from the zero words `c_w` (`r10`) and the top word's zero bits `c_b`:
`X`'s shift `2 c = 64 c_w + c_b - (c_b mod 2)` and `D`'s `c + 1`, in words and bits. -/
def counts : List Instr :=
  [.li .r12 0] ++ clzStage 32 5 ++ clzStage 16 4 ++ clzStage 8 3 ++ clzStage 4 2 ++ clzStage 2 1 ++
    clzStage 1 0 ++
  [.store .w .r10 .r31 sQw, .lsr .d .r0 .r12 1, .lsl .r3 .r0 1, .store .w .r3 .r31 sQb,
    .lsl .r4 .r10 6, .add .r4 .r4 .r12, .lsr .d .r4 .r4 1, .addi .r4 .r4 1, .lsr .d .r3 .r4 6,
    .store .w .r3 .r31 sRw, .li .r3 63, .logic .and .r3 .r4 .r3, .store .w .r3 .r31 sRb]

/-- `X'`'s top two words into `r14`, `r15`; the remainder `r16`, `r17` and root `r18` := 0. -/
def digit0Head : List Instr :=
  ptr .r5 wR ++ twoH ++ [.lsl .r0 .r11 3, .add .r5 .r5 .r0, .subi .r5 .r5 16, .load .d .r14 .r5 8,
    .load .d .r15 .r5 0, .li .r16 0, .li .r17 0, .li .r18 0, .li .r20 0, .li .r8 64]

/-- Two bits of `(r14, r15)` into the remainder `(r16, r17)`; the root `r18` doubled, plus one where
`4 y + 1` fits, subtracted. -/
def digit0Step : List Instr :=
  [.lsr .d .r0 .r17 62, .lsl .r16 .r16 2, .add .r16 .r0 .r16,
    .lsr .d .r0 .r14 62, .lsl .r17 .r17 2, .add .r17 .r0 .r17,
    .lsr .d .r0 .r15 62, .lsl .r14 .r14 2, .add .r14 .r0 .r14, .lsl .r15 .r15 2,
    .lsr .d .r3 .r18 62, .lsl .r12 .r18 2, .addi .r12 .r12 1,
    .subc .r10 .r17 .r12, .sube .r9 .r16 .r3, .addze .r0 .r20, .sub .r6 .r20 .r0,
    .logic .xor .r10 .r10 .r17, .logic .and .r10 .r10 .r6, .logic .xor .r17 .r17 .r10,
    .logic .xor .r9 .r9 .r16, .logic .and .r9 .r9 .r6, .logic .xor .r16 .r16 .r9,
    .add .r18 .r18 .r18, .add .r18 .r18 .r0]

/-- The remainder back into `X'`'s top two words (`r5`), `2 s₀` into `D`'s words `h - 1` and `h`,
and `P = 1` and `s₀` into the temporary's words 0 and 1 (`r9`). -/
def digit0Tail : List Instr :=
  [.store .d .r17 .r5 0, .store .d .r16 .r5 8] ++ ptr .r6 wS ++ twoH ++
    [.lsl .r0 .r11 2, .add .r6 .r6 .r0, .subi .r6 .r6 8, .add .r0 .r18 .r18, .store .d .r0 .r6 0,
      .lsr .d .r0 .r18 63, .store .d .r0 .r6 8] ++ ptr .r9 wTmp ++ [.li .r0 1, .store .d .r0 .r9 0,
      .store .d .r18 .r9 8]

/-- The root's first word `s₀ = ⌊√T⌋` of `X'`'s top two words `T`, the remainder `T - s₀²` in
their place, `D = 2 s₀`, and the reciprocal of `s₀`. -/
def digit0 : Prog isa := seqs [.block digit0Head, countLoop .r8 digit0Step, .block digit0Tail, recip]

/-- The steps' registers: `X'` (`r19`), `D` (`r24`), `j := 1` (`r26`), `h - 1` steps (`r28`). -/
def stepsHead : List Instr :=
  ptr .r19 wR ++ ptr .r24 wS ++ twoH ++ [.lsr .d .r28 .r11 1, .subi .r28 .r28 1, .li .r26 1]

/-- `r5 :=` the address of `R`'s word 0, `X'`'s word `2 h - 2 j - 2`, and `r6 :=` `D`'s word
`m = h - 1 - j` (for `r11 = 2 h`). -/
def ptrs : List Instr :=
  [.sub .r5 .r11 .r26, .sub .r5 .r5 .r26, .lsl .r5 .r5 3, .add .r5 .r5 .r19, .subi .r5 .r5 16,
    .lsr .d .r6 .r11 1, .sub .r6 .r6 .r26, .lsl .r6 .r6 3, .add .r6 .r6 .r24, .subi .r6 .r6 8]

/-- `q̂` (`r18`): `s₁` (from `D`'s words `h - 2` and `h - 1`) into the temporary's word 3, `⌊R / 2⌋`'s
words `j + 1`, `j` (`r15`, `r16`, and the temporary's words 7 and 6) and `j - 1` (its word 5), and
`min(⌊U / (s₀ β + s₁)⌋, β - 1)` by `Precompute.quot`'s steps with `P = 1`. -/
def estimate : List Instr :=
  twoH ++ ptrs ++ ptr .r9 wTmp ++
  [.lsl .r0 .r11 2, .add .r3 .r0 .r24, .subi .r3 .r3 16, .load .d .r10 .r3 0, .load .d .r12 .r3 8,
    .lsr .d .r10 .r10 1, .lsl .r12 .r12 63, .add .r10 .r10 .r12, .store .d .r10 .r9 24,
    .lsl .r3 .r26 3, .add .r3 .r3 .r5, .subi .r3 .r3 8, .load .d .r17 .r3 0, .load .d .r10 .r3 8,
    .load .d .r12 .r3 16, .load .d .r0 .r3 24,
    .lsl .r0 .r0 63, .lsr .d .r15 .r12 1, .add .r15 .r15 .r0,
    .lsl .r12 .r12 63, .lsr .d .r16 .r10 1, .add .r16 .r16 .r12,
    .lsl .r10 .r10 63, .lsr .d .r17 .r17 1, .add .r17 .r17 .r10, .store .d .r17 .r9 40,
    .store .d .r16 .r9 48, .store .d .r15 .r9 56, .addi .r14 .r9 40, .li .r6 1, .load .d .r7 .r9 8, .load .d .r18 .r9 16, .sub .r22 .r7 .r15, .li .r20 0] ++
  quotMG ++ quotFix ++ quot3

/-- `T := R - q̂ D` in place over `R`'s `j + 3` words, `D`'s word `m` set to `q̂` (`D = 2 s β + q̂`):
`D`'s `j + 2` words times `q̂` with the carry (`r3`) and the borrow (`r22`, 1 for none), then the
top word less the carry. -/
def mulSubD : Prog isa := seqs [
  .block (twoH ++ ptrs ++ [.store .d .r18 .r6 0, .li .r20 0, .subi .r17 .r20 1, .li .r3 0, .li .r22 1,
    .addi .r8 .r26 2]),
  countLoop .r8 [.load .d .r7 .r6 0, .mul .r12 .r7 .r18, .mulhu .r0 .r7 .r18, .addc .r12 .r12 .r3,
    .addze .r3 .r0, .load .d .r0 .r5 0, .addc .r10 .r22 .r17, .sube .r0 .r0 .r12, .addze .r22 .r20,
    .store .d .r0 .r5 0, .addi .r5 .r5 8, .addi .r6 .r6 8],
  .block [.load .d .r0 .r5 0, .addc .r10 .r22 .r17, .sube .r0 .r0 .r3, .store .d .r0 .r5 0]]

/-- A correction: where `T` (its top word's sign) is negative, `T := T + 2 s β + 2 q̂ - 1` and
`q̂ := q̂ - 1`, by a mask (`r9`): word 0 `2 q̂ - 1`, word 1 `D`'s word `m + 1` (`2 s`'s word 0, even)
or'ed with that one's carry, then `D`'s words `m + 2 …`. -/
def correct : Prog isa := seqs [
  .block (twoH ++ ptrs ++ [.li .r20 0, .lsl .r3 .r26 3, .add .r3 .r3 .r5, .load .d .r0 .r3 16,
    .lsr .d .r0 .r0 63, .sub .r9 .r20 .r0, .add .r10 .r18 .r18, .subi .r10 .r10 1, .subi .r14 .r18 1,
    .lsr .d .r14 .r14 63, .load .d .r3 .r5 0, .logic .and .r10 .r10 .r9, .addc .r3 .r3 .r10,
    .store .d .r3 .r5 0, .load .d .r7 .r6 8, .logic .or .r7 .r7 .r14, .logic .and .r7 .r7 .r9,
    .load .d .r3 .r5 8, .adde .r3 .r3 .r7, .store .d .r3 .r5 8, .addi .r5 .r5 16, .addi .r6 .r6 16,
    .add .r18 .r18 .r9, .addi .r8 .r26 0]),
  countLoop .r8 [.load .d .r7 .r6 0, .logic .and .r7 .r7 .r9, .load .d .r3 .r5 0, .adde .r3 .r3 .r7,
    .store .d .r3 .r5 0, .addi .r5 .r5 8, .addi .r6 .r6 8],
  .block [.load .d .r3 .r5 0, .addze .r3 .r3, .store .d .r3 .r5 0]]

/-- `D := 2 s' = 2 s β + 2 q`: its word `m` `2 q`, word `m + 1` plus `q`'s top bit; `j + 1`. -/
def finishQ : List Instr :=
  twoH ++ ptrs ++ [.add .r0 .r18 .r18, .store .d .r0 .r6 0, .lsr .d .r3 .r18 63, .load .d .r0 .r6 8,
    .add .r0 .r0 .r3, .store .d .r0 .r6 8, .addi .r26 .r26 1, .subi .r28 .r28 1]

/-- A step: `q̂`, `T`, two corrections, `D`; `j + 1`. -/
def sqStep : Prog isa := seqs [.block estimate, mulSubD, correct, correct, .block finishQ]

/-- Whether the remainder (`X'`'s `2 h` words) is zero: into `sOk5`. -/
def remZero : Prog isa := seqs [
  .block (ptr .r5 wR ++ twoH ++ [.addi .r8 .r11 0, .li .r9 0]),
  countLoop .r8 [.load .d .r0 .r5 0, .logic .or .r9 .r9 .r0, .addi .r5 .r5 8],
  .block [.li .r3 0, .sub .r3 .r3 .r9, .logic .or .r3 .r3 .r9, .lsr .d .r3 .r3 63, .li .r0 1,
    .logic .xor .r3 .r3 .r0, .store .w .r3 .r31 sOk5]]

/-- The root's word 0 less one if `X = 0` (`X = 1` was rooted instead). -/
def rootFix : List Instr :=
  ptr .r5 wS ++ [.load .w .r3 .r31 sZ, .load .d .r0 .r5 0, .sub .r0 .r0 .r3, .store .d .r0 .r5 0]

/-- The root of `X` (`[wR]`, its low `2 h` words) into the narrow `[aSy]` and whether `X` is a square
into `sOk5`. -/
def sqrt : Prog isa := seqs [copy wS wZero, zeroX, clzX, .block counts, shlBy wR sQw sQb true, digit0,
  .block stepsHead, .loop sqStep (.nonzero .d .r28), remZero, shrBy wS sRw sRb, .block rootFix, .block ctxw]

/-! ## The factors -/

/-- The mask: `d e ≥ 2`, `m < n`, the exact division, `b² > 4 n` and the
exact square root. -/
def maskOf : List Instr :=
  [.li .r6 1, .load .w .r0 .r31 sB0, .logic .xor .r0 .r0 .r6, .load .w .r3 .r31 sB1, .logic .xor .r3 .r3 .r6,
    .logic .and .r0 .r0 .r3, .load .w .r3 .r31 sLt, .logic .and .r0 .r0 .r3,
    .load .w .r3 .r31 sExact, .logic .and .r0 .r0 .r3,
    .load .w .r3 .r31 sC1, .logic .xor .r3 .r3 .r6, .logic .and .r0 .r0 .r3,
    .load .w .r3 .r31 sC2, .logic .xor .r3 .r3 .r6, .logic .and .r0 .r0 .r3,
    .load .w .r3 .r31 sOk5, .logic .and .r0 .r0 .r3, .store .w .r0 .r31 Recover.sMask]

/-- `p = (b + ϒ) / 2` into array 5 and `q = (b - ϒ) / 2` into array 6, and the mask. -/
def factors : Prog isa := seqs [add aP aD aSy aZero aNy, .block [.li .r9 0], half aP,
  sub3 aQ aD aSy, .block [.li .r9 0], half aQ, .block maskOf]

/-! ## The function -/

def det : Prog isa := seqs [deMinus, twos, gcd, aProduct, divA, divB, square, minus4n, sqrt, factors]

/-- Once `n` is known valid. -/
def valid : Prog isa := seqs [Recover.loads, Recover.prod, det, Recover.stores]

/-- `vg_rsa_recover_primes_det`. -/
def code : Prog isa :=
  .seq (.block Recover.entry)
    (.seq Recover.nCheck (.seq (.ite (.zero .d .r0) valid Recover.fail) (.block Recover.restore)))

end VG.Impl.Rsa.PPC64LE.RecoverDet
