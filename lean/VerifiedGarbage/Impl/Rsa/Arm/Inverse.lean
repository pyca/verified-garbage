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

The state is `δ`, `(f, g)` and `(d, e)`, all two's complement in `k + 1`
words (arrays `bF`, `bG`, `bD`, `bE`), from `(1, m, a', 0, 1)`, with
`a' = a + m` for an even `a`, so that `g` starts odd or zero. Each batch runs
30 divsteps on the low words of `f` and `g` (`wstep`, in registers), which
give the batch's matrix `(u, v, q, r)`, its entries at most `2^30` in
magnitude; then one pass over each pair, both rows at once and in place
(libsecp256k1's `update_fg` and `update_de`, `Proof/Divstep/Libsecp.lean`):

* `f, g := (u f + v g) / 2^30, (q f + r g) / 2^30`;
* `d, e := (u d + v e + md₁ m) / 2^30, (q d + r e + md₂ m) / 2^30`, each `md`
  the multiple of `m` that clears the sum's low 30 bits (with
  `-m⁻¹ mod 2^32`) and keeps `d` and `e` in `(-2m, m)`.

`3 (k + 1)` batches leave `g = 0` and `f = ±gcd(a, m)` with `x a ≡ f d`:
array 1 gets `|f|` and array 3 `±d mod m`, `d` brought into `[0, m)` by two
conditional additions of `m`. The batches count down in the high bits of
`r6` and the divsteps in its low five. Every choice is a masked selection,
so the addresses and branches depend only on `r7`, `r8` and `r9`.
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

/-! ## The batches

A batch's matrix `(u, v; q, r)` is applied in one pass over `(f, g)` and one over `(d, e)`, both
rows at once, in place: word `i` of each input is read before word `i - 1` of each output is
written. A row's sum is unsigned: each input word is XORed with its coefficient's sign mask, its
coefficient taken in magnitude, and the row's carry starts at the magnitudes of its negative
coefficients, so that the sum is the row's value plus `2^(32 (k + 1))` times the magnitudes of the
coefficients whose sign differs from their input's (the row's correction), which the top word
subtracts. A product of a word and a magnitude (at most `2^31`) is four 16 × 16-bit products.

Over `(d, e)` each row also adds `md` times `m`, `md` the multiple of `m` that clears the sum's
low 30 bits (libsecp256k1's `update_de`: `Proof/Divstep/Libsecp.lean`), so `d` and `e` stay in
`(-2m, m)` as signed `k + 1`-word numbers and every output is the sum shifted right by 30.

The scratch is array `bT1` (`r12`), which the batches alone use: coefficient `t` (`u, v, q, r, md₁, md₂`) at `16 + 12 t` as its sign mask and its
magnitude's low and high halves; the rows' corrections at 88 and 92 and their starting carries at
100 and 104. It needs `W ≥ 8`: 27 words of the four arrays from `bT1`.

The terms need every register but `r8`, so a pass keeps nothing public in memory, which the
constant-time analysis could not follow: `lr` holds the words left below the batches left
(`r6`), and after the pass `r6` comes back from `lr`, `r7` (the stride) from the rows' pointers,
which are a stride apart, and `r9` (`k`) from `r0`'s offset in its array. -/

/-- Coefficient `t`'s scratch: its sign mask, then its magnitude's halves at `+ 4` and `+ 8`. -/
def coefOff (t : Nat) : Nat := 16 + 12 * t
def corrOff (row : Nat) : Nat := 88 + 4 * row
def carryOff (row : Nat) : Nat := 100 + 4 * row

/-- `c := |c|` and `m := -(c >>> 31)`, its sign mask. -/
def absMask (c m : Reg) : List Instr :=
  [.mov m (.shifted c .lsr 31), .dp .sub m m (.shifted m .lsl 1), .dp .eor c c (.reg m), .dp .sub c c (.reg m)]

/-- Coefficient `t` from `r1`: its mask (left in `r2`) and halves stored, `|c|` left in `r1`. -/
def coefStore (t : Nat) : List Instr :=
  absMask .r1 .r2 ++ [.str .r2 .r12 (coefOff t), .mov .r3 (.shifted .r1 .lsr 16), .str .r3 .r12 (coefOff t + 8),
    .dp .bic .r3 .r1 (.shifted .r3 .lsl 16), .str .r3 .r12 (coefOff t + 4)]

/-- `hi:lo += |c| (x ^ m)` for coefficient `t` and the word `x` at `[xs + xo]`, through `r6`, `r7`,
`r9`, `r10`. -/
def term (xs : Reg) (xo t : Nat) (lo hi : Reg) : List Instr :=
  [.ldr .r6 xs xo, .ldr .r7 .r12 (coefOff t), .dp .eor .r6 .r6 (.reg .r7),
   .mov .r7 (.shifted .r6 .lsr 16), .dp .bic .r6 .r6 (.shifted .r7 .lsl 16),
   .ldr .r9 .r12 (coefOff t + 4), .mul .r10 .r6 .r9, .adds lo lo (.reg .r10), .adc hi hi (.imm 0),
   .mul .r10 .r7 .r9, .adds lo lo (.shifted .r10 .lsl 16), .adc hi hi (.shifted .r10 .lsr 16),
   .ldr .r9 .r12 (coefOff t + 8), .mul .r10 .r6 .r9, .adds lo lo (.shifted .r10 .lsl 16),
   .adc hi hi (.shifted .r10 .lsr 16), .mla hi .r7 .r9 hi]

/-- Word 0 of a row's sum (`lo`): its top two bits into the row's word 0 (`[p]`), and the carry down. -/
def out0 (p lo hi : Reg) : List Instr :=
  [.mov .r6 (.shifted lo .lsr 30), .str .r6 p 0, .mov lo (.reg hi), .mov hi (.imm 0)]

/-- Word `i` of a row's sum: word `i - 1` of the output completed (`[p]`), its top two bits into
word `i` (`[p + 4]`), and the carry down. -/
def outW (p lo hi : Reg) : List Instr :=
  [.ldr .r6 p 0, .dp .orr .r6 .r6 (.shifted lo .lsl 2), .str .r6 p 0, .mov .r6 (.shifted lo .lsr 30),
   .str .r6 p 4, .mov lo (.reg hi), .mov hi (.imm 0)]

/-- The top word: the carry less the row's correction, shifted into word `k` (`[p]`). -/
def outTop (p lo : Reg) (row : Nat) : List Instr :=
  [.ldr .r6 .r12 (corrOff row), .dp .sub lo lo (.reg .r6), .ldr .r6 p 0, .dp .orr .r6 .r6 (.shifted lo .lsl 2),
   .str .r6 p 0]

/-- `r5 :=` the sign mask of array `a`'s word `k`, through `r3`. -/
def topMask (a : Nat) : List Instr :=
  ptr .r3 a ++ [.dp .add .r3 .r3 (.shifted .r9 .lsl 2), .ldr .r5 .r3 0, .mov .r5 (.shifted .r5 .lsr 31),
    .dp .sub .r5 .r5 (.shifted .r5 .lsl 1)]

/-- `r1 :=` the coefficient `c`, through `r3`. -/
def ldCoef (c : Coef) : List Instr := ptr .r3 c.arr ++ [.ldr .r1 .r3 c.off]

/-- `r4 +=` the correction of coefficient `|c|` (`r1`, mask `r2`) on an input of mask `r5`, and
`r10 +=` its starting carry. -/
def corrAdd : List Instr :=
  [.dp .eor .r3 .r2 (.reg .r5), .dp .and .r3 .r3 (.reg .r1), .dp .add .r4 .r4 (.reg .r3),
   .dp .and .r3 .r1 (.reg .r2), .dp .add .r10 .r10 (.reg .r3)]

/-- A row `c₁ [x] + c₂ [y]`: its coefficients stored as `t₁` and `t₂`, its correction and its
starting carry. -/
def rowPrep (x y : Nat) (c₁ c₂ : Coef) (t₁ t₂ row : Nat) : List Instr :=
  [.mov .r4 (.imm 0), .mov .r10 (.imm 0)] ++
  topMask x ++ ldCoef c₁ ++ coefStore t₁ ++ corrAdd ++
  topMask y ++ ldCoef c₂ ++ coefStore t₂ ++ corrAdd ++
  [.str .r4 .r12 (corrOff row), .str .r10 .r12 (carryOff row)]

/-- The scratch's address, and `lr := (r6 << 11) + k`: the batches left (`r6 / 32`) above the words
left. -/
def spill : List Instr := ptr .r12 bT1 ++ [.dp .add .lr .r9 (.shifted .r6 .lsl 11)]

/-- A word done: `lr`'s low half down by one, `z` iff it is `0`, through `r6`. -/
def wordDone : List Instr := [.dp .sub .lr .lr (.imm 1), .mov .r6 (.shifted .lr .lsl 16), .cmp .r6 (.imm 0)]

/-- `r6`, `r7`, `r9` back from `lr` and the rows' pointers, `r0` at word `k` of array `a` and `r1` of
array `a + 1`: `r7 = r1 - r0`, `r9 = (r0 - r8 - hdr - a r7) / 4`, `a r7` as the shifts `sh`. -/
def restore (sh : List Nat) : List Instr :=
  [.mov .r6 (.shifted .lr .lsr 11), .dp .sub .r7 .r1 (.reg .r0), .dp .sub .r9 .r0 (.reg .r8),
   .dp .sub .r9 .r9 (.imm 160)] ++ sh.map (fun n => .dp .sub .r9 .r9 (.shifted .r7 .lsl n)) ++
  [.mov .r9 (.shifted .r9 .lsr 2)]

/-- The two rows' words `0` (`zo = 0`) or `i` (`zo = 4`) over `[r0]`, `[r1]`. -/
def fgTerms (zo : Nat) : List Instr :=
  term .r0 zo 0 .r2 .r3 ++ term .r0 zo 2 .r4 .r5 ++ term .r1 zo 1 .r2 .r3 ++ term .r1 zo 3 .r4 .r5

/-- `(f, g) := ((u f + v g) / 2^30, (q f + r g) / 2^30)`. -/
def fgPass : Prog isa := seqs [
  .block (spill ++ rowPrep bF bG cU cV 0 1 0 ++ rowPrep bF bG cQ cR 2 3 1 ++
    [.ldr .r2 .r12 (carryOff 0), .mov .r3 (.imm 0), .ldr .r4 .r12 (carryOff 1), .mov .r5 (.imm 0)] ++
    ptr .r0 bF ++ ptr .r1 bG ++ fgTerms 0 ++ out0 .r0 .r2 .r3 ++ out0 .r1 .r4 .r5),
  .loop (.block (fgTerms 4 ++ outW .r0 .r2 .r3 ++ outW .r1 .r4 .r5 ++
    [.dp .add .r0 .r0 (.imm 4), .dp .add .r1 .r1 (.imm 4)] ++ wordDone)) .ne,
  .block (outTop .r0 .r2 0 ++ outTop .r1 .r4 1 ++ restore [2])]

/-- A row's `md` (coefficients `c₁`, `c₂` on `d`, `e`) stored as coefficient `t`, its correction and
starting carry added to the row's: `md = md₀ - ((md₀ - np (c₁ d₀ + c₂ e₀)) mod 2^30)` for
`md₀ = (d < 0 ? c₁ : 0) + (e < 0 ? c₂ : 0)` and `np = -m⁻¹` (`sB`). -/
def mdPrep (c₁ c₂ : Coef) (t row : Nat) : List Instr :=
  topMask bD ++ ldCoef c₁ ++ [.dp .and .r0 .r1 (.reg .r5)] ++ ptr .r3 bD ++ [.ldr .r3 .r3 0, .mul .r11 .r1 .r3] ++
  topMask bE ++ ldCoef c₂ ++ [.dp .and .r4 .r1 (.reg .r5), .dp .add .r0 .r0 (.reg .r4)] ++ ptr .r3 bE ++
  [.ldr .r3 .r3 0, .mla .r11 .r1 .r3 .r11, .ldr .r3 .r8 sB, .mul .r11 .r11 .r3, .dp .sub .r11 .r0 (.reg .r11),
   .dp .bic .r11 .r11 (.imm 0xC0000000), .dp .sub .r1 .r0 (.reg .r11)] ++
  coefStore t ++
  [.dp .and .r3 .r1 (.reg .r2), .ldr .r4 .r12 (corrOff row), .dp .add .r4 .r4 (.reg .r3),
   .str .r4 .r12 (corrOff row), .ldr .r4 .r12 (carryOff row), .dp .add .r4 .r4 (.reg .r3),
   .str .r4 .r12 (carryOff row)]

/-- The two rows' words `0` or `i` over `[r0]`, `[r1]` and `m` at `[r11]`. -/
def deTerms (zo : Nat) : List Instr :=
  fgTerms zo ++ term .r11 zo 4 .r2 .r3 ++ term .r11 zo 5 .r4 .r5

/-- `(d, e) := ((u d + v e + md₁ m) / 2^30, (q d + r e + md₂ m) / 2^30)`. -/
def dePass : Prog isa := seqs [
  .block (spill ++ rowPrep bD bE cU cV 0 1 0 ++ rowPrep bD bE cQ cR 2 3 1 ++
    mdPrep cU cV 4 0 ++ mdPrep cQ cR 5 1 ++
    [.ldr .r2 .r12 (carryOff 0), .mov .r3 (.imm 0), .ldr .r4 .r12 (carryOff 1), .mov .r5 (.imm 0)] ++
    ptr .r0 bD ++ ptr .r1 bE ++ ptr .r11 bP ++ deTerms 0 ++ out0 .r0 .r2 .r3 ++ out0 .r1 .r4 .r5),
  .loop (.block (deTerms 4 ++ outW .r0 .r2 .r3 ++ outW .r1 .r4 .r5 ++
    [.dp .add .r0 .r0 (.imm 4), .dp .add .r1 .r1 (.imm 4), .dp .add .r11 .r11 (.imm 4)] ++ wordDone)) .ne,
  .block (outTop .r0 .r2 0 ++ outTop .r1 .r4 1 ++ restore [2, 1])]

def update : Prog isa := seqs [fgPass, dePass, .block [.subs .r6 .r6 (.imm 32)]]

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

/-- `r11 :=` the sign bit of `[a]`'s word `k`. -/
def signTop (a : Nat) : List Instr :=
  ptr .r12 a ++ [.dp .add .r12 .r12 (.shifted .r9 .lsl 2), .ldr .r1 .r12 0, .mov .r11 (.shifted .r1 .lsr 31)]

/-- `[1] = |f|` and `[3] = ±d mod m` from `d ∈ (-2m, m)`: `m` added where `d` is negative, the
sign of `f` applied, `m` added again where negative; each `k` words of zeros to the width. -/
def finish : Prog isa := seqs [
  zeroW 1, zeroW 3,
  sub1 bT1 bZ bF, .block fSign, sel1 1 bF bT1 true,
  sub1 bT2 bZ bP, sub1 bT1 bD bT2, .block (signTop bD), sel1 bA1 bD bT1,
  sub1 bT2 bZ bA1, .block fSign, sel1 bA2 bA1 bT2,
  sub1 bT2 bZ bP, sub1 bT1 bA2 bT2, .block (signTop bA2), sel1 3 bA2 bT1 true]

/-! ## The gcd alone -/

/-- A batch of the gcd: the divsteps and the pass over `(f, g)`, without `(d, e)`. -/
def batchG : Prog isa := .seq divsteps (seqs [fgPass, .block [.subs .r6 .r6 (.imm 32)]])

/-- `[1] = |f|`, `k` words of zeros to the width. -/
def finishG : Prog isa := seqs [zeroW 1, sub1 bT1 bZ bF, .block fSign, sel1 1 bF bT1 true]

end Inv

open VG.Impl.Rsa.Arm.Keys.Inv in
def inverse : Prog isa := seqs [init, .loop batch .ne, finish]

open VG.Impl.Rsa.Arm.Keys.Inv in
/-- `gcd(a, m)` alone into array 1: `inverse` without `(d, e)` and its end. -/
def gcdOnly : Prog isa := seqs [init, .loop batchG .ne, finishG]

end VG.Impl.Rsa.Arm.Keys
