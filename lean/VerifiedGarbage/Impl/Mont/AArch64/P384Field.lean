module

public import VerifiedGarbage.Impl.Mont.AArch64

/-!
# P-384's Montgomery product and square on AArch64

For `p = 2^384 - 2^128 - 2^96 + 2^32 - 1`, over 64-bit words, with `x7 = 0`:

* `prod ra rb a b`: `T = [ra + a] [rb + b]`, twelve words, by rows: the words
  of `b` by a word of `a`, the low words of the products added in one chain and
  the high ones in another (`rowAdd`).
* `sqr ra a`: `T = [ra + a]²`: the products of different words, doubled, and
  the squares.
* `round2`: two words of Montgomery's reduction, with no multiplication.
  Modulo `2^128`, `-p⁻¹ = 1 + 2^32 + 2^64`, so the multiplier `M` of the low
  words `t₀`, `t₁` is sums of shifts of them; and
  `T + M p = T + M 2^384 - M (2^128 + 2^96 - 2^32 + 1)`, where
  `M (1 - 2^32 + 2^96)` is `t₀, t₁` modulo `2^128`, and so leaves, above them,
  `⌊M / 2^32⌋ - ⌊M / 2^96⌋` and the carry and borrow of its low words, which
  the additions that follow take as their carry and borrow in.
* `reduce`: three rounds on the low half of `T`, and its high half added.

Every sum is a chain through the carry flag, which `mul`, `umulh` and the
shifts leave alone.
-/

@[expose] public section

namespace VG.Impl.Mont.AArch64.P384Field
open VG.AArch64 VG.Impl.Mont.AArch64

/-- `ds = ns + ms`, with `adds` on the first word and `adcs` on the others. -/
def adds (first : Bool) : List Reg → List Reg → List Reg → List Instr
  | d :: ds, n :: ns, m :: ms =>
    (if first then .adds .x d n m else .adcs .x d n m) :: adds false ds ns ms
  | _, _, _ => []

/-- `ds = ns - ms`, with `subs` on the first word and `sbcs` on the others. -/
def subs (first : Bool) : List Reg → List Reg → List Reg → List Instr
  | d :: ds, n :: ns, m :: ms =>
    (if first then .subs .x d n m else .sbcs .x d n m) :: subs false ds ns ms
  | _, _, _ => []

/-- The low words of `x bs` (the high ones for `hi`) added to `ds`, through `x2`. -/
def muls (hi : Bool) (x : Reg) (first : Bool) : List Reg → List Reg → List Instr
  | d :: ds, b :: bs =>
    (if hi then .umulh .x2 x b else .mul .x .x2 x b) ::
      (if first then .adds .x d d .x2 else .adcs .x d d .x2) :: muls hi x false ds bs
  | _, _ => []

/-- The low words of `x bs` into `ds`. -/
def lows (x : Reg) : List Reg → List Reg → List Instr
  | d :: ds, b :: bs => .mul .x d x b :: lows x ds bs
  | _, _ => []

/-- `q :: qs ++ [l] = x bs`, for `bs` of as many words as `q :: qs`. -/
def row0 (x q : Reg) (qs : List Reg) (l : Reg) (bs : List Reg) (b : Reg) : List Instr :=
  lows x (q :: qs) (bs ++ [b]) ++ muls true x true qs bs ++ ([.umulh .x2 x b, .adc .x l .x2 .x7] : List Instr)

/-- `q :: qs ++ [l] = (q :: qs) + x bs`. -/
def rowAdd (x q : Reg) (qs : List Reg) (l : Reg) (bs : List Reg) (b : Reg) : List Instr :=
  muls false x true (q :: qs) (bs ++ [b]) ++ ([.adc .x l .x7 .x7] : List Instr) ++ muls true x true qs bs ++
    ([.umulh .x2 x b, .adc .x l l .x2] : List Instr)

/-! ## The product -/

/-- The words of the second operand of a product, and of a square's. -/
abbrev bs : List Reg := [.x8, .x9, .x10, .x16, .x24, .x25]
/-- The low half of `T`. -/
abbrev tl : List Reg := [.x17, .x22, .x23, .x11, .x12, .x13]
/-- The high half of `T`. -/
abbrev th : List Reg := [.x14, .x15, .x21, .x4, .x5, .x6]

/-- The next word of the first operand, in `x1`, times the second added to `T`. -/
def mulRow (ra : Reg) (d : Nat) (q : Reg) (qs : List Reg) (l : Reg) : List Instr :=
  Instr.ldr .x .x1 ra d :: rowAdd .x1 q qs l [.x8, .x9, .x10, .x16, .x24] .x25

/-- `T = [ra + a] [rb + b]`: the low half in `tl`, the high one in `th`. -/
def prod (ra rb : Reg) (a b : Nat) : List Instr :=
  loadsR rb bs b ++
  Instr.ldr .x .x1 ra a :: row0 .x1 .x17 [.x22, .x23, .x11, .x12, .x13] .x14 [.x8, .x9, .x10, .x16, .x24] .x25 ++
  mulRow ra (a + 8) .x22 [.x23, .x11, .x12, .x13, .x14] .x15 ++
  mulRow ra (a + 16) .x23 [.x11, .x12, .x13, .x14, .x15] .x21 ++
  mulRow ra (a + 24) .x11 [.x12, .x13, .x14, .x15, .x21] .x4 ++
  mulRow ra (a + 32) .x12 [.x13, .x14, .x15, .x21, .x4] .x5 ++
  mulRow ra (a + 40) .x13 [.x14, .x15, .x21, .x4, .x5] .x6

/-! ## The square -/

/-- The products of different words, in words 1 to 10 of `T`. -/
def cross : List Instr :=
  row0 .x8 .x22 [.x23, .x11, .x12, .x13] .x14 [.x9, .x10, .x16, .x24] .x25 ++
  rowAdd .x9 .x11 [.x12, .x13, .x14] .x15 [.x10, .x16, .x24] .x25 ++
  rowAdd .x10 .x13 [.x14, .x15] .x21 [.x16, .x24] .x25 ++
  rowAdd .x16 .x15 [.x21] .x4 [.x24] .x25 ++
  muls false .x24 true [.x4] [.x25] ++ ([.umulh .x2 .x24 .x25, .adc .x .x5 .x2 .x7] : List Instr)

/-- The words' squares added to `ds`, two words of `ds` to each. -/
def diag : List Reg → List Reg → List Instr
  | d :: e :: ds, x :: xs =>
    [.mul .x .x2 x x, .adcs .x d d .x2, .umulh .x2 x x, .adcs .x e e .x2] ++ diag ds xs
  | _, _ => []

/-- `T = [ra + a]²`. -/
def sqr (ra : Reg) (a : Nat) : List Instr :=
  loadsR ra bs a ++ cross ++
  adds true [.x22, .x23, .x11, .x12, .x13, .x14, .x15, .x21, .x4, .x5]
    [.x22, .x23, .x11, .x12, .x13, .x14, .x15, .x21, .x4, .x5]
    [.x22, .x23, .x11, .x12, .x13, .x14, .x15, .x21, .x4, .x5] ++
  ([.adc .x .x6 .x7 .x7, .mul .x .x17 .x8 .x8, .umulh .x2 .x8 .x8, .adds .x .x22 .x22 .x2] : List Instr) ++
  diag [.x23, .x11, .x12, .x13, .x14, .x15, .x21, .x4] [.x9, .x10, .x16, .x24] ++
  ([.mul .x .x2 .x25 .x25, .adcs .x .x5 .x5 .x2, .umulh .x2 .x25 .x25, .adc .x .x6 .x6 .x2] : List Instr)

/-! ## The reduction -/

/-- Two words of the reduction: `t₀, …, t₅` become `t₂, …, t₅, m₀, m₁`, which
is `(T + M p) / 2^128`; through `v` (which may be `t₁`), `x1`–`x3`, `x16`,
`x24` and `x25`. `m₁` may be `t₀`. -/
def round2 (t0 t1 t2 t3 t4 t5 m0 m1 v : Reg) : List Instr :=
  [.lsl .x m0 t0 32, .extr .x .x1 t1 t0 32, .adds .x m0 t0 m0, .adc .x .x1 t1 .x1, .add .x m1 .x1 t0] ++
  [.lsl .x v m0 32, .extr .x .x1 m1 m0 32, .lsr .x .x2 m1 32] ++
  [.adds .x .x3 m1 v, .adcs .x .x16 m0 .x1, .adcs .x .x24 m1 .x2, .adc .x .x25 .x7 .x7,
    .subs .x v m0 v, .sbcs .x .x3 .x3 .x1, .sbcs .x .x16 .x16 .x2, .sbcs .x .x24 .x24 .x7, .sbc .x .x25 .x25 .x7] ++
  subs true [t2, t3, t4, t5, m0] [t2, t3, t4, t5, m0] [.x16, .x24, .x25, .x7, .x7] ++
  [.sbc .x m1 m1 .x7]

/-- The reduced number's words. -/
abbrev rs : List Reg := [.x8, .x9, .x10, .x22, .x11, .x12]

/-- `rs + 2^384 x13 = (T + M p) / 2^384`, below `2p` if `T` is below `2^384 p`. -/
def reduce : List Instr :=
  round2 .x17 .x22 .x23 .x11 .x12 .x13 .x8 .x9 .x17 ++
  round2 .x23 .x11 .x12 .x13 .x8 .x9 .x10 .x22 .x23 ++
  round2 .x12 .x13 .x8 .x9 .x10 .x22 .x11 .x12 .x13 ++
  adds true rs rs th ++ ([.adc .x .x13 .x7 .x7] : List Instr)

end VG.Impl.Mont.AArch64.P384Field
