module

public import VerifiedGarbage.Impl.Rsa.Arm.KeyWs
public import VerifiedGarbage.Impl.Bignum.Arm.Row
public import VerifiedGarbage.Impl.Bignum.Arm.MaskRow
public import VerifiedGarbage.Impl.Bignum.Arm.WideMul

/-!
# Division by words for the RSA key checks on ARMv7

`divW a r m t nm u`: `[r] := [a] mod [m]`, for a divisor `[m]` of `dw = w / 2`
words of 32 bits whose top word is not zero, by long division a word at a
time (Knuth, TAOCP vol. 2, §4.3.1, Algorithm D), in place: `[a]` is copied to
`[r]` (word `w` zero), and for `j = w - dw, …, 0` the window `Y` of `dw + 1`
words at word `j` of `[r]`, below `2^32 [m]`, becomes `Y mod [m]`, its top
word zero:

* `q̂ = min(⌊U / D⌋, 2^32 - 1)` from the top three words `U` of `2^z Y` and
  the top two `D` of `2^z [m]`, for the leading zeros `z` of `[m]`'s top
  word, which gives `q ≤ q̂ ≤ q + 1` for `q = ⌊Y / [m]⌋`: `2^z` (`P`), `d` and
  `d₁` once by doublings under a mask (`norm`), `U` each step by products
  with `P` (`top`), so that nothing is shifted; the 2-by-1 estimate from
  `U`'s top two words by the reciprocal `v = ⌊(2^64 - 1) / d⌋ - 2^32`
  (Möller and Granlund, "Improved division by invariant integers", IEEE
  Trans. Computers 60(2), 2011, Algorithm 4; `quot`), `v` once by restoring
  division a bit at a time (`recip`), then refined by `U - q̂ D` over three
  words and two corrections (`refine3`);
* `Y - q̂ [m]` by a row of `q̂ [m]` into `[t]` (`Bignum.Arm.row`) and its
  subtraction into `[u]` (`subRow`), whose borrow says whether it is
  negative; then `[u]` less `-[m]` (`[nm]`, set once) under that borrow back
  into the window (`selectRow`, `subRow`), which adds `[m]` back once.

Every product is `wideMul`'s, from 16-bit halves with `mul` alone: no
long multiply, so the ARMv7 baseline. Every address and count depends only
on `w`, the base and the step; the arithmetic on the numbers' words is
branch-free. The header holds `P` (136), `d` (140), `v` (144), `d₁` (148),
the mask of `u₂ = d` (152), `q̂` (156), `u₀` (64), `u₂` (68) and the window's
word offset `4 j` (72).
-/

@[expose] public section

namespace VG.Impl.Rsa.Arm.KeyDiv

open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Rsa.Arm.Keys

def sP : Nat := 136
def sD : Nat := 140
def sV : Nat := 144
def sD1 : Nat := 148
def sMk : Nat := 152
def sQ : Nat := 156
def sU0 : Nat := 64
def sU2 : Nat := 68
def sJ : Nat := 72

/-- `w` from the header into `r9`, and the stride into `r7`. -/
def ctx : List Instr := [.ldr .r9 .r8 16] ++ stride

/-- `r :=` the address of word `dw - i` of `[j]`, `dw = w / 2` (`r9 >> 1`),
through `t`. -/
def topPtr (r : Reg) (j i : Nat) (t : Reg) : List Instr :=
  ptr r j ++ [.mov t (.shifted .r9 .lsr 1), .dp .sub t t (.imm (BitVec.ofNat 32 i)),
    .dp .add r r (.shifted t .lsl 2)]

/-! ## `P = 2^z`, `d`, `d₁` -/

/-- A doubling of `r1` and `r2` where the top bit of `r1` is clear; `lr`
counts down. -/
def normBit : List Instr :=
  [.mov .r3 (.shifted .r1 .lsr 31), .dp .sub .r3 .r3 (.imm 1), .dp .and .r4 .r1 (.reg .r3),
    .dp .add .r1 .r1 (.reg .r4), .dp .and .r4 .r2 (.reg .r3), .dp .add .r2 .r2 (.reg .r4),
    .subs .lr .lr (.imm 1)]

/-- `P` (136) by 31 doublings of `[m]`'s top word `T` under a mask, `d = T P +
hi(U P)` (140) and `d₁ = lo(U P) + hi(V P)` (148), for the two words `U`
and `V` below `T`, all three read first (`r1`, `r10`, `r11`). The base is
kept in `r12` and `w` in `lr` around `wideMul`, which uses `r7`–`r9`. -/
def norm (m : Nat) : Prog isa := seqs [
  .block (topPtr .r0 m 3 .r1 ++ [.ldr .r11 .r0 0, .ldr .r10 .r0 4, .ldr .r1 .r0 8, .mov .r2 (.imm 1),
    .mov .lr (.imm 31)]),
  .loop (.block normBit) .ne,
  .block ([.str .r2 .r8 sP, .mov .r12 (.reg .r8), .mov .lr (.reg .r9), .mov .r0 (.reg .r1), .mov .r1 (.reg .r10)] ++
    wideMul ++ [.dp .add .r0 .r0 (.reg .r4), .str .r0 .r12 sD, .mov .r0 (.reg .r3), .mov .r1 (.reg .r11)] ++
    wideMul ++ [.dp .add .r0 .r0 (.reg .r4), .str .r0 .r12 sD1, .mov .r8 (.reg .r12), .mov .r9 (.reg .lr)] ++
    stride)]

/-! ## `v` -/

/-- A bit of restoring division by `d` (`r1`) of the remainder `r < d`
(`r2`) and a one bit: `r := 2 r + 1`, with its carry; `d` subtracted if
the carry is set or `r ≥ d`; the quotient `r3 := 2 r3 + 1` if so, `2 r3`
otherwise; and the count `lr` down. -/
def divBit : List Instr :=
  [.adds .r2 .r2 (.reg .r2), .mov .r4 (.imm 0), .adc .r4 .r4 (.imm 0), .dp .add .r2 .r2 (.imm 1),
    .subs .r5 .r2 (.reg .r1), .mov .r5 (.imm 0), .adc .r5 .r5 (.imm 0), .dp .orr .r4 .r4 (.reg .r5),
    .mov .r5 (.imm 0), .dp .sub .r5 .r5 (.reg .r4), .dp .and .r5 .r5 (.reg .r1), .dp .sub .r2 .r2 (.reg .r5),
    .dp .add .r3 .r3 (.reg .r3), .dp .add .r3 .r3 (.reg .r4), .subs .lr .lr (.imm 1)]

/-- `v = ⌊((2^32 - 1 - d) 2^32 + 2^32 - 1) / d⌋` (144), by 32 bits. -/
def recip : Prog isa := seqs [
  .block [.ldr .r1 .r8 sD, .mvn .r2 (.reg .r1), .mov .r3 (.imm 0), .mov .lr (.imm 32)],
  .loop (.block divBit) .ne,
  .block [.str .r3 .r8 sV]]

/-! ## A step's estimate -/

/-- From `r10` at word `j + dw - 3` of `[r]` (the window's word `dw - 3`):
the window's top four words read first (`r0`, `r11`, `lr`, `r10`), then the
words of `2^z Y` at `dw - 2`, `dw - 1` and `dw`: `u₀` (64), `u₁` (`r11`) and
`u₂` (68), by products with `P` (`r2`), each high word carried in `r0`. The
base is kept in `r12`. -/
def topWords : List Instr :=
  [.mov .r12 (.reg .r8), .ldr .r0 .r10 0, .ldr .r11 .r10 4, .ldr .lr .r10 8, .ldr .r10 .r10 12,
    .ldr .r2 .r12 sP, .mov .r1 (.reg .r0)] ++ wideMul ++ [.mov .r0 (.reg .r4), .mov .r1 (.reg .r11)] ++ wideMul ++
  [.dp .add .r3 .r3 (.reg .r0), .str .r3 .r12 sU0, .mov .r0 (.reg .r4), .mov .r1 (.reg .lr)] ++ wideMul ++
  [.dp .add .r11 .r3 (.reg .r0), .mov .r0 (.reg .r4), .mov .r1 (.reg .r10)] ++ wideMul ++
  [.dp .add .r3 .r3 (.reg .r0), .str .r3 .r12 sU2]

/-- `q̂` (156) from `u₂` (68) and `u₁` (`r11`): the mask of `u₂ = d` (152)
and `u₂` cleared under it; `(q₁, q₀) = v u₂ + (u₂, u₁)`, the candidate
`q₁ + 1` and its remainder `r = u₁ - (q₁ + 1) d mod 2^32`; one less and
`r + d` if `r > q₀`, one more if then `r ≥ d`; and all ones where `u₂ = d`.
The base stays in `r12`. -/
def quot : List Instr :=
  [.ldr .r0 .r12 sD, .ldr .r1 .r12 sU2, .dp .sub .r0 .r0 (.reg .r1), .subs .r0 .r0 (.imm 1), .mov .r0 (.imm 0),
    .adc .r0 .r0 (.imm 0), .dp .sub .r0 .r0 (.imm 1), .str .r0 .r12 sMk, .dp .bic .r1 .r1 (.reg .r0),
    .mov .r10 (.reg .r1), .ldr .r2 .r12 sV] ++ wideMul ++
  [.adds .r3 .r3 (.reg .r11), .adc .r4 .r4 (.reg .r10), .dp .add .r10 .r4 (.imm 1),
    .ldr .r1 .r12 sD, .mul .r2 .r10 .r1, .dp .sub .r2 .r11 (.reg .r2),
    .subs .r0 .r3 (.reg .r2), .mov .r0 (.imm 0), .adc .r0 .r0 (.imm 0), .dp .sub .r0 .r0 (.imm 1),
    .dp .add .r10 .r10 (.reg .r0), .dp .and .r0 .r0 (.reg .r1), .dp .add .r2 .r2 (.reg .r0),
    .subs .r0 .r2 (.reg .r1), .adc .r10 .r10 (.imm 0),
    .ldr .r0 .r12 sMk, .dp .orr .r10 .r10 (.reg .r0), .str .r10 .r12 sQ]

/-- `t = U - q̂ D` over three words, `t₀` (`r10`), `t₁` (`r11`), `t₂` (`lr`),
for `q̂` (156), `U = (u₂, u₁, u₀)` (68, `r11`, 64) and `D = (d, d₁)` (140,
148): `q̂ d₁` and `q̂ d`, `q̂ D` into `r0`, `r1`, `r2`, and its subtraction
with the borrows in `r3`. -/
def quot3 : List Instr :=
  [.ldr .r1 .r12 sQ, .ldr .r2 .r12 sD1] ++ wideMul ++ [.mov .r0 (.reg .r3), .mov .r10 (.reg .r4),
    .ldr .r1 .r12 sQ, .ldr .r2 .r12 sD] ++ wideMul ++
  [.adds .r1 .r3 (.reg .r10), .adc .r2 .r4 (.imm 0),
    .ldr .r10 .r12 sU0, .subs .r10 .r10 (.reg .r0), .mov .r3 (.imm 0), .adc .r3 .r3 (.imm 0),
    .dp .eor .r3 .r3 (.imm 1),
    .subs .r11 .r11 (.reg .r1), .mov .r4 (.imm 1), .adc .r4 .r4 (.imm 0), .subs .r11 .r11 (.reg .r3),
    .adc .r4 .r4 (.imm 0), .dp .eor .r3 .r4 (.imm 3),
    .ldr .lr .r12 sU2, .dp .sub .lr .lr (.reg .r2), .dp .sub .lr .lr (.reg .r3)]

/-- If `t` is negative (the top bit of `t₂`): `q̂ := q̂ - 1` (`r1`) and
`t := t + D`, by a mask. -/
def fix3 : List Instr :=
  [.mov .r0 (.shifted .lr .lsr 31), .mov .r2 (.imm 0), .dp .sub .r0 .r2 (.reg .r0), .dp .add .r1 .r1 (.reg .r0),
    .ldr .r2 .r12 sD1, .dp .and .r2 .r2 (.reg .r0), .ldr .r3 .r12 sD, .dp .and .r3 .r3 (.reg .r0),
    .adds .r10 .r10 (.reg .r2), .mov .r4 (.imm 0), .adc .r4 .r4 (.imm 0),
    .adds .r11 .r11 (.reg .r4), .mov .r4 (.imm 0), .adc .r4 .r4 (.imm 0),
    .adds .r11 .r11 (.reg .r3), .adc .r4 .r4 (.imm 0), .dp .add .lr .lr (.reg .r4)]

/-- `q̂` (156) refined to the 3-by-2 estimate. -/
def refine3 : List Instr := quot3 ++ [.ldr .r1 .r12 sQ] ++ fix3 ++ fix3 ++ [.str .r1 .r12 sQ]

/-- The estimate for the window at word offset `4 j` (72) of `[r]`, the base
put back in `r8` and `w`, the stride after. -/
def estimate (r : Nat) : List Instr :=
  topPtr .r10 r 3 .r0 ++ [.ldr .r0 .r8 sJ, .dp .add .r10 .r10 (.reg .r0)] ++ topWords ++ quot ++ refine3 ++
    [.mov .r8 (.reg .r12)] ++ ctx

/-- `estimate`'s instructions up to the window's offset, read from 72. The
offset is the same in both runs but read from memory, so the address it makes
starts a block of its own (`estB`): each block computes its addresses from
registers the two runs agree on. -/
def estA (r : Nat) : List Instr := topPtr .r10 r 3 .r0 ++ [.ldr .r0 .r8 sJ]

/-- The rest of `estimate`. -/
def estB : List Instr :=
  [.dp .add .r10 .r10 (.reg .r0)] ++ topWords ++ quot ++ refine3 ++ [.mov .r8 (.reg .r12)] ++ ctx

/-! ## A step's subtraction -/

/-- The quotient's digit `q̂ - c` (`c` the borrow, `sC`) at the window's word of `[q]`, from the
window's offset in `r1`. -/
def digit (q : Nat) : List Instr :=
  ptr .r2 q ++ [.dp .add .r2 .r2 (.reg .r1), .ldr .r3 .r8 sQ, .ldr .r12 .r8 sC, .dp .sub .r3 .r3 (.reg .r12),
    .str .r3 .r2 0]

def digitOf : Option Nat → List Instr
  | none => []
  | some q => digit q

/-- `Y := Y - q̂ [m]` in place over the window's `dw + 1` words: a row of `q̂` over `[nm]`'s low `dw` words
(`β^dw - m`), then the top word less `q̂` plus the carry, its sign into `sC`. A block ends after the load of
the window's offset. -/
def mulSubW (r nm : Nat) : Prog isa := seqs [
  .block (ptr .r0 r ++ [.ldr .r1 .r8 sJ]),
  .block ([.dp .add .r0 .r0 (.reg .r1)] ++ ptr .r12 nm ++
    [.mov .lr (.shifted .r9 .lsr 1), .ldr .r1 .r8 sQ, .mov .r11 (.imm 0)]),
  row,
  .block ([.ldr .r2 .r0 0, .dp .add .r2 .r2 (.reg .r11), .dp .sub .r2 .r2 (.reg .r1), .str .r2 .r0 0,
    .mov .r2 (.shifted .r2 .lsr 31), .str .r2 .r8 sC] ++ ctx)]

/-- `[m]` added back to the window under the mask of its sign (`sC`), the carry into its top word, after
the quotient's digit into `[q]` for `qo = some q`. -/
def addBackW (r m : Nat) (qo : Option Nat := none) : Prog isa := seqs [
  .block (ptr .r0 r ++ [.ldr .r1 .r8 sJ]),
  .block (digitOf qo ++ [.dp .add .r0 .r0 (.reg .r1)] ++ ptr .r12 m ++
    [.mov .lr (.shifted .r9 .lsr 1), .ldr .r1 .r8 sC, .mov .r2 (.imm 0), .dp .sub .r1 .r2 (.reg .r1),
      .mov .r11 (.imm 0)]),
  maskRow,
  .block [.ldr .r2 .r0 0, .dp .add .r2 .r2 (.reg .r11), .str .r2 .r0 0]]

/-- A step: the estimate, `Y - q̂ [m]` in place, `[m]` added back where negative (after the quotient's
digit into `[q]` for `qo = some q`), and the window a word down. -/
def step (r m _t nm _u : Nat) (qo : Option Nat := none) : Prog isa := seqs [.block (estA r), .block estB,
  mulSubW r nm, addBackW r m qo, .block [.ldr .r0 .r8 sJ, .subs .r0 .r0 (.imm 4), .str .r0 .r8 sJ]]

/-- The window's first offset: at word `w - dw`, or at word `t` for a dividend
below `2^(32 (t + dw))` (`top = some t`). -/
def winStart : Option Nat → List Instr
  | none => [.mov .r0 (.shifted .r9 .lsr 1), .dp .sub .r0 .r9 (.reg .r0), .mov .r0 (.shifted .r0 .lsl 2),
    .str .r0 .r8 sJ]
  | some t => [.mov .r0 (.imm (BitVec.ofNat 32 (4 * t))), .str .r0 .r8 sJ]

/-- `[r] := [a]`, word `w` of `[r]` zero, `[nm] := -[m]`, `P`, `d`, `d₁`, `v`,
and the window at its first offset (`winStart top`). -/
def prep (a r m nm : Nat) (top : Option Nat) : Prog isa := seqs [
  copy r a,
  .block (ptr .r0 r ++ [.dp .add .r0 .r0 (.shifted .r9 .lsl 2), .mov .r1 (.imm 0), .str .r1 .r0 0]),
  sub3 nm 0 m, norm m, recip, .block (winStart top)]

/-- `[m]`'s top word (`w / 2 - 1`) made not zero, `1` if it is zero: a divisor copied
from a number that may be shorter than `w / 2` words. -/
def fixTop (m : Nat) : List Instr :=
  topPtr .r0 m 1 .r1 ++ [.ldr .r2 .r0 0, .mov .r3 (.imm 0), .dp .sub .r3 .r3 (.reg .r2),
    .dp .orr .r3 .r3 (.reg .r2), .mov .r3 (.shifted .r3 .lsr 31), .dp .eor .r3 .r3 (.imm 1),
    .dp .add .r2 .r2 (.reg .r3), .str .r2 .r0 0]

/-- `[r] := [a] mod [m]`, for `[m]` of `w / 2` words, its top word not zero,
through `[t]`, `[nm]` and `[u]`, and for `qo = some q` the quotient's digits into the zero
`[q]`. The steps run while the window's offset, counted down, does not underflow. -/
def divW (a r m _t nm _u : Nat) (top : Option Nat := none) (qo : Option Nat := none) : Prog isa :=
  seqs [prep a r m nm top, .loop (.seq (step r m _t nm _u qo) (.block [.ldr .r0 .r8 sJ, .cmp .r0 (.imm 0)])) .ne,
    step r m _t nm _u qo]

/-! ## Balanced keys -/

/-- `Z` exactly for a balanced key: `p_len` and `q_len` (the stack words at `oP`
and `oQ`) both `2 w` bytes and `w = ⌈n_len / 4⌉` (from `r11`) even, so that `p` and
`q` have `w / 2` words and `p q` is below `2^(32 w)`. From the lengths alone. -/
def shape (oP oQ : Nat) : List Instr :=
  [.dp .add .r3 .r11 (.imm 3), .mov .r3 (.shifted .r3 .lsr 2), .ldrSp .r0 oP, .ldrSp .r1 oQ,
    .mov .r2 (.shifted .r3 .lsl 1), .dp .eor .r0 .r0 (.reg .r2), .dp .eor .r1 .r1 (.reg .r2),
    .dp .orr .r0 .r0 (.reg .r1), .dp .and .r2 .r3 (.imm 1), .dp .orr .r0 .r0 (.reg .r2), .cmp .r0 (.imm 0)]

/-- `shape`, with the lengths at `oDP` and `oDQ` also `2 w` bytes: for `dP` and `dQ` of
`w / 2` words. -/
def shape4 (oP oQ oDP oDQ : Nat) : List Instr :=
  [.dp .add .r3 .r11 (.imm 3), .mov .r3 (.shifted .r3 .lsr 2), .ldrSp .r0 oP, .ldrSp .r1 oQ,
    .mov .r2 (.shifted .r3 .lsl 1), .dp .eor .r0 .r0 (.reg .r2), .dp .eor .r1 .r1 (.reg .r2),
    .dp .orr .r0 .r0 (.reg .r1), .ldrSp .r1 oDP, .dp .eor .r1 .r1 (.reg .r2), .dp .orr .r0 .r0 (.reg .r1),
    .ldrSp .r1 oDQ, .dp .eor .r1 .r1 (.reg .r2), .dp .orr .r0 .r0 (.reg .r1),
    .dp .and .r2 .r3 (.imm 1), .dp .orr .r0 .r0 (.reg .r2), .cmp .r0 (.imm 0)]

/-! ## Products -/

/-- The rows' end: the offset of row `n` (`w / 2` for `none`) against the next's. -/
def rowsEnd : Option Nat → List Instr
  | none => [.mov .r1 (.shifted .r9 .lsl 1), .cmp .r0 (.reg .r1)]
  | some n => [.cmp .r0 (.imm (BitVec.ofNat 32 (4 * n)))]

/-- Row `i` (`4 i` at 72) of `[o] += x_i [y]` over the `w / 2 + 1` words from word
`i`, for `[y]` of `w / 2` words; then the next row. A block ends after the load of
the offset, as for `estA`. -/
def mulRow (o x y : Nat) (n : Option Nat) : Prog isa :=
  .seq (.block (ptr .r0 o ++ [.ldr .r2 .r8 sJ]))
    (.seq (.block ([.dp .add .r0 .r0 (.reg .r2)] ++ ptr .r12 y ++
      [.mov .lr (.shifted .r9 .lsr 1), .dp .add .lr .lr (.imm 1)] ++ ptr .r1 x ++
      [.dp .add .r1 .r1 (.reg .r2), .ldr .r1 .r1 0, .mov .r11 (.imm 0)]))
    (.seq row (.block (ctx ++ [.ldr .r0 .r8 sJ, .dp .add .r0 .r0 (.imm 4), .str .r0 .r8 sJ] ++ rowsEnd n))))

/-- `[o] := [x] [y]`, for `[x]` of `n` words (`w / 2` for `none`) and `[y]` of `w / 2`. -/
def mulLo (o x y : Nat) (n : Option Nat := none) : Prog isa :=
  seqs [copy o 0, .block [.mov .r0 (.imm 0), .str .r0 .r8 sJ], .loop (mulRow o x y n) .ne]

end VG.Impl.Rsa.Arm.KeyDiv
