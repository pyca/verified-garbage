module

public import VerifiedGarbage.Impl.Rsa.Arm.KeyWs
public import VerifiedGarbage.Impl.Bignum.Arm.Zero

/-! # The inverse modulo an odd number, on ARMv7

`inverse`: Bernstein and Yang's divsteps (`Proof/Divstep/`) in batches of 30,
at the width `k = r9` words in arrays of the stride `r7` (`Impl/Rsa/Arm/KeyWs.lean`,
whose `w` is `k` here; a caller can run it on the low `k` words of wider
arrays). From `a = [0]` and the odd modulus `m = [aM]` (both below
`2^(32 k)`), array 1 ends as `gcd(a, m)` and array 3 as `x < m` with
`x a ≡ gcd(a, m) (mod m)`, each zero to the arrays' width `r7 / 4 - 2`.

The state is `δ` and `(f, g)`, two's complement in `k + 1` words (arrays
`bF`, `bG`), and `(d, e)` in `[0, m)` (arrays `bD`, `bE`, their word `k`
zero), from `(1, m, a', 0, 1)`, with `a' = a + m` for an even `a`, so
that `g` starts odd or zero. Each batch runs 30 divsteps on the low words of
`f` and `g` (`wstep`, in registers), which give the batch's matrix
`(u, v, q, r)`, its entries at most `2^30` in magnitude; then

* `f, g := (u f + v g) / 2^30, (q f + r g) / 2^30`: each product as the
  magnitude of the coefficient times the factor negated (modulo
  `2^(32 (k + 1))`) where the coefficient is negative (`cnegFG`), the sum
  exact modulo `2^(32 (k + 1))` (`macRow`), shifted right by 30 bits with
  its sign (`shr30`);
* `d, e := (u d + v e) / 2^30, (q d + r e) / 2^30` modulo `m`: likewise,
  `m - d` in place of `-d` (`cnegDE`), so that the sum is at most `2^30 m`;
  then a multiple of `m` that clears its low 30 bits (`redc`, with
  `-m⁻¹ mod 2^32`), the shift, and one conditional subtraction of `m`.

`3 (k + 1)` batches leave `g = 0` and `f = ±gcd(a, m)` with `x a ≡ f d`:
array 1 gets `|f|` and array 3 `±d mod m`. The batches count down in the
high bits of `r6` and the divsteps in its low five. Every choice is a masked
selection, so the addresses and branches depend only on `r7`, `r8` and `r9`.
-/

@[expose] public section

namespace VG.Impl.Rsa.Arm.Keys
open VG VG.Arm VG.Impl.Bignum.Arm

/-- The arrays callers set up: the modulus `m`, its negation and zero (which
`inverse` reads only `m` of), and four temporaries. -/
def aM : Nat := 8
def aNM : Nat := 9
def aZero : Nat := 10
def aT1 : Nat := 11
def aT2 : Nat := 12
def aT3 : Nat := 13
def aT4 : Nat := 14

namespace Inv

/-! ## The arrays and the window

Zero, the modulus with its word `k` zero, the state, two temporaries for
the negated factors and two accumulators. `δ` and `-m⁻¹ mod 2^32` are in the
header words `sOdd` and `sB`; the matrix in words 0–2 of array 1 and word 0
of array 3, which only the end writes. -/

def bZ : Nat := 0
def bP : Nat := 2
def bF : Nat := 4
def bG : Nat := 5
def bD : Nat := 6
def bE : Nat := 7
def bT1 : Nat := 11
def bT2 : Nat := 12
def bA1 : Nat := 13
def bA2 : Nat := 14

/-- Where a coefficient of the matrix is kept: an array and a byte. -/
structure Coef where
  arr : Nat
  off : Nat

def cU : Coef := ⟨1, 0⟩
def cV : Coef := ⟨1, 4⟩
def cQ : Coef := ⟨1, 8⟩
def cR : Coef := ⟨3, 0⟩

/-! ## Word loops -/

/-- `r1 · [r12 + 4 i] + r11` added into `[r0 + 4 i]` for `lr` words, the carry
out in `r11`: the scalar split once into its halves, `r1` and `r10`, and each
product from four 16 × 16-bit products. Preserves `r6`–`r9`. -/
def macSplit : List Instr := [.mov .r10 (.shifted .r1 .lsr 16), .dp .bic .r1 .r1 (.shifted .r10 .lsl 16)]

/-- `r5:r4 := (r1 + 2^16 r10) · r2 + r11`, `r2` split into its halves. -/
def macMul : List Instr :=
  [.mov .r3 (.shifted .r2 .lsr 16), .dp .bic .r2 .r2 (.shifted .r3 .lsl 16),
   .mul .r4 .r1 .r2, .mul .r2 .r10 .r2, .mul .r5 .r10 .r3, .mul .r3 .r1 .r3,
   .adds .r4 .r4 (.shifted .r2 .lsl 16), .adc .r5 .r5 (.shifted .r2 .lsr 16),
   .adds .r4 .r4 (.shifted .r3 .lsl 16), .adc .r5 .r5 (.shifted .r3 .lsr 16),
   .adds .r4 .r4 (.reg .r11), .adc .r5 .r5 (.imm 0)]

/-- The accumulator word added in, the carry into `r11`, and the word stored. -/
def macAcc : List Instr := [.ldr .r2 .r0 0, .adds .r4 .r4 (.reg .r2), .adc .r11 .r5 (.imm 0), .str .r4 .r0 0]

def macAdvance : List Instr := [.dp .add .r0 .r0 (.imm 4), .dp .add .r12 .r12 (.imm 4), .subs .lr .lr (.imm 1)]

def macStep : List Instr := .ldr .r2 .r12 0 :: macMul ++ macAcc ++ macAdvance

def macRow : Prog isa := .seq (.block macSplit) (.loop (.block macStep) .ne)

/-- `[r0 + 4 i] := ([r12 + 4 i] >> 30) + ([r12 + 4 i + 4] << 2)` for `lr`
words, then the word after them the last word shifted right by 30 with its
sign: `lr + 1` words shifted right by 30 bits, as a signed number. -/
def shrStep : List Instr :=
  [.ldr .r1 .r12 0, .ldr .r2 .r12 4, .mov .r1 (.shifted .r1 .lsr 30), .dp .add .r1 .r1 (.shifted .r2 .lsl 2),
   .str .r1 .r0 0, .dp .add .r0 .r0 (.imm 4), .dp .add .r12 .r12 (.imm 4), .subs .lr .lr (.imm 1)]

def shrTop : List Instr :=
  [.ldr .r1 .r12 0, .mov .r2 (.shifted .r1 .lsr 30), .mov .r1 (.shifted .r1 .lsr 31),
   .dp .sub .r2 .r2 (.shifted .r1 .lsl 2), .str .r2 .r0 0]

def shr30 : Prog isa := .seq (.loop (.block shrStep) .ne) (.block shrTop)

/-! ## Array operations at the width `k` -/

/-- `lr := k + 1`. -/
def cnt1 : Instr := .dp .add .lr .r9 (.imm 1)

/-- `[o] := 0`, `k + 1` words. -/
def zero1 (o : Nat) : Prog isa := .seq (.block (ptr .r0 o ++ [cnt1, .mov .r3 (.imm 0)])) zero

/-- `[o] := [a] - [b]`, `k + 1` words, the borrow out in `r11`. -/
def sub1 (o a b : Nat) : Prog isa :=
  .seq (.block (ptr .r0 o ++ ptr .r10 a ++ ptr .r12 b ++ [cnt1, .mov .r11 (.imm 0)])) subRow

/-- `[o] := [b]` if `r11` is 1, else `[a]`: `k + 1` words, or `k` with `low`. -/
def sel1 (o a b : Nat) (low : Bool := false) : Prog isa :=
  .seq (.block (ptr .r0 o ++ ptr .r10 a ++ ptr .r12 b ++ [if low then .mov .lr (.reg .r9) else cnt1]))
    selectRow

/-- `[o] := [a]`, `k + 1` words, or `k` with `low`. -/
def copy1 (o a : Nat) (low : Bool := false) : Prog isa :=
  .seq (.block (ptr .r0 o ++ ptr .r10 a ++ ptr .r12 a ++
    [if low then .mov .lr (.reg .r9) else cnt1, .mov .r11 (.imm 0)])) copyWords

/-- Word `k` of `[o]` := 0. -/
def topZero (o : Nat) : List Instr :=
  ptr .r0 o ++ [.dp .add .r0 .r0 (.shifted .r9 .lsl 2), .mov .r1 (.imm 0), .str .r1 .r0 0]

/-- `r11` := the sign bit of the coefficient `c`. -/
def signOf (c : Coef) : List Instr := ptr .r12 c.arr ++ [.ldr .r1 .r12 c.off, .mov .r11 (.shifted .r1 .lsr 31)]

/-- `r1` := the magnitude of the coefficient `c`, and `r11 := 0`. -/
def absOf (c : Coef) : List Instr :=
  ptr .r12 c.arr ++ [.ldr .r1 .r12 c.off, .mov .r11 (.shifted .r1 .lsr 31),
    .dp .sub .r2 .r11 (.shifted .r11 .lsl 1), .dp .eor .r1 .r1 (.reg .r2), .dp .sub .r1 .r1 (.reg .r2),
    .mov .r11 (.imm 0)]

/-- `[t] := [base] - [x]` where `c` is negative, else `[x]`. -/
def cneg (base t x : Nat) (c : Coef) : Prog isa :=
  seqs [sub1 t base x, .block (signOf c), sel1 t x t]

/-- `[acc] += |c| · [src]`, `k + 1` words, the carry dropped. -/
def mac1 (acc src : Nat) (c : Coef) : Prog isa :=
  .seq (.block (ptr .r0 acc ++ absOf c ++ ptr .r12 src ++ [cnt1])) macRow

/-- `[acc] := c₁ [x] + c₂ [y]`, as `|c₁| (±[x]) + |c₂| (±[y])`, the negations
from `base`. -/
def lin (base acc x y : Nat) (c₁ c₂ : Coef) : Prog isa :=
  seqs [cneg base bT1 x c₁, cneg base bT2 y c₂, zero1 acc, mac1 acc bT1 c₁, mac1 acc bT2 c₂]

/-- `[o] := [a] >> 30`, signed, `k + 1` words. -/
def shr1 (o a : Nat) : Prog isa := .seq (.block (ptr .r0 o ++ ptr .r12 a ++ [.mov .lr (.reg .r9)])) shr30

/-- `[acc] +=` the multiple `((acc · (-m⁻¹)) mod 2^30) m` that clears its low 30 bits. -/
def redc (acc : Nat) : Prog isa :=
  .seq (.block (ptr .r0 acc ++ [.ldr .r1 .r0 0, .ldr .r2 .r8 sB, .mul .r1 .r1 .r2,
    .dp .bic .r1 .r1 (.imm 0xC0000000), .mov .r11 (.imm 0)] ++ ptr .r12 bP ++ [cnt1])) macRow

/-- `[o] := [a] - m` if that does not borrow, else `[a]`. -/
def csub1 (o a : Nat) (low : Bool := false) : Prog isa := seqs [sub1 bT1 a bP, sel1 o bT1 a low]

/-! ## The divsteps -/

/-- `wstep` on `δ, f, g, u, v, q, r` in `r0, r1, r2, r3, r4, r5, r10`, with
`B` in `r11`, `S` in `r12` and `lr` scratch. -/
def wstepI : List Instr :=
  [.dp .and .r11 .r2 (.imm 1), .dp .sub .r11 .r11 (.shifted .r11 .lsl 1),
   .mov .r12 (.shifted .r0 .lsr 31), .dp .sub .r12 .r12 (.imm 1), .dp .and .r12 .r12 (.reg .r11),
   .dp .eor .lr .r1 (.reg .r12), .dp .sub .lr .lr (.reg .r12), .dp .and .lr .lr (.reg .r11),
   .dp .add .r2 .r2 (.reg .lr),
   .dp .eor .lr .r3 (.reg .r12), .dp .sub .lr .lr (.reg .r12), .dp .and .lr .lr (.reg .r11),
   .dp .add .r5 .r5 (.reg .lr),
   .dp .eor .lr .r4 (.reg .r12), .dp .sub .lr .lr (.reg .r12), .dp .and .lr .lr (.reg .r11),
   .dp .add .r10 .r10 (.reg .lr),
   .dp .eor .r0 .r0 (.reg .r12), .dp .sub .r0 .r0 (.reg .r12), .dp .add .r0 .r0 (.imm 2),
   .dp .and .lr .r2 (.reg .r12), .dp .add .r1 .r1 (.reg .lr),
   .mov .r2 (.shifted .r2 .lsr 1),
   .dp .and .lr .r5 (.reg .r12), .dp .add .r3 .r3 (.reg .lr), .mov .r3 (.shifted .r3 .lsl 1),
   .dp .and .lr .r10 (.reg .r12), .dp .add .r4 .r4 (.reg .lr), .mov .r4 (.shifted .r4 .lsl 1)]

/-- One divstep, counted down in the low bits of `r6`. -/
def wbody : List Instr := wstepI ++ [.dp .sub .r6 .r6 (.imm 1), .dp .and .r11 .r6 (.imm 31), .cmp .r11 (.imm 0)]

/-- The window loaded: `δ`, the low words of `f` and `g`, the identity, and 30 steps in `r6`. -/
def wload : List Instr :=
  ptr .r12 bF ++ [.ldr .r1 .r12 0] ++ ptr .r12 bG ++ [.ldr .r2 .r12 0, .ldr .r0 .r8 sOdd,
    .mov .r3 (.imm 1), .mov .r4 (.imm 0), .mov .r5 (.imm 0), .mov .r10 (.imm 1), .dp .add .r6 .r6 (.imm 30)]

/-- `δ` and the matrix stored. -/
def wstore : List Instr :=
  [.str .r0 .r8 sOdd] ++ ptr .r12 cU.arr ++ [.str .r3 .r12 cU.off, .str .r4 .r12 cV.off, .str .r5 .r12 cQ.off] ++
    ptr .r12 cR.arr ++ [.str .r10 .r12 cR.off]

def divsteps : Prog isa := seqs [.block wload, .loop (.block wbody) .ne, .block wstore]

/-! ## The batches -/

def update : Prog isa := seqs [
  lin bZ bA1 bF bG cU cV, lin bZ bA2 bF bG cQ cR, shr1 bF bA1, shr1 bG bA2,
  lin bP bA1 bD bE cU cV, lin bP bA2 bD bE cQ cR, redc bA1, redc bA2,
  shr1 bT2 bA1, csub1 bD bT2, shr1 bT2 bA2, csub1 bE bT2,
  .block [.subs .r6 .r6 (.imm 32)]]

def batch : Prog isa := .seq divsteps update

/-- `-m⁻¹ mod 2^32` from `m`'s low word in `r5`: from `x = m`, right modulo 8,
four Newton steps `x (2 - m x)`, then negated. -/
def newtonStep : List Instr :=
  [.mul .r4 .r5 .r2, .movw .r3 2, .dp .sub .r3 .r3 (.reg .r4), .mul .r2 .r2 .r3]

def negInv : List Instr :=
  ptr .r0 bP ++ [.ldr .r5 .r0 0, .mov .r2 (.reg .r5)] ++ newtonStep ++ newtonStep ++ newtonStep ++ newtonStep ++
    [.dp .sub .r2 .r2 (.shifted .r2 .lsl 1), .str .r2 .r8 sB]

/-- `δ = 1`, and `96 (k + 1)` in `r6`: `3 (k + 1)` batches of 32. -/
def start : List Instr :=
  [.mov .r1 (.imm 1), .str .r1 .r8 sOdd, .dp .add .r6 .r9 (.imm 1), .mov .r6 (.shifted .r6 .lsl 5),
   .dp .add .r6 .r6 (.shifted .r6 .lsl 1)]

/-- `[bP] = m` (word `k` zero), `f = m`, `g = a - (-m)` if `a` is even else
`a` (`-m` in `bA1`), `d = 0`, `e = 1`, `[bZ] = 0`. -/
def init : Prog isa := seqs [
  copy1 bP aM true, .block (topZero bP), .block (topZero 0), zero1 bT1, sub1 bA1 bT1 bP,
  .block (ptr .r0 0 ++ [.ldr .r1 .r0 0, .mvn .r1 (.reg .r1), .dp .and .r11 .r1 (.imm 1)]),
  sel1 bT2 bT1 bA1, sub1 bG 0 bT2, copy1 bF bP, zero1 bZ, zero1 bD, zero1 bE,
  .block (setOne bE ++ negInv ++ start)]

/-! ## The end -/

/-- `[o] := 0` to the arrays' width `r7 / 4 - 2`. -/
def zeroW (o : Nat) : Prog isa :=
  .seq (.block (ptr .r0 o ++ [.mov .lr (.shifted .r7 .lsr 2), .dp .sub .lr .lr (.imm 2), .mov .r3 (.imm 0)])) zero

/-- `r11` := the sign bit of `f`. -/
def fSign : List Instr :=
  ptr .r12 bF ++ [.dp .add .r12 .r12 (.shifted .r9 .lsl 2), .ldr .r1 .r12 0, .mov .r11 (.shifted .r1 .lsr 31)]

/-- `[1] = |f|`, `[3] = ±d mod m`, each `k` words of zeros to the width. -/
def finish : Prog isa := seqs [
  zeroW 1, zeroW 3,
  sub1 bT1 bZ bF, .block fSign, sel1 1 bF bT1 true,
  sub1 bT2 bP bD, .block fSign, sel1 bT2 bD bT2, csub1 3 bT2 true]

end Inv

open VG.Impl.Rsa.Arm.Keys.Inv in
def inverse : Prog isa := seqs [init, .loop batch .ne, finish]

end VG.Impl.Rsa.Arm.Keys
