module

public import VerifiedGarbage.Impl.Mont.AArch64.P521.Op

/-!
# P-521's field arithmetic on AArch64

Modulo `p = 2^521 - 1`, on numbers below `p` of nine 64-bit words, with
`R = 2^576` (so `R ≡ 2^55`). Every product, sum and difference is a list of
`Op`s and then the result's stores, so that the result may be either operand.

* `mulOps`: `[a] [b] R⁻¹`. Row `i` adds `a_i [b]` to a window of ten words
  (`acc`), its low halves in one chain of additions and its high halves in
  another; the top words of the operands are below `2^9`, so the halves
  that end a chain absorb its carry. A word `t` that is done, at `2^(64 i)`,
  is worth `t 2^(64 i + 521) = (t 2^9) 2^(64 (i + 8))` too: each two rows
  retire two words and add them, shifted left by 9 bits, eight words up
  (`fold`). What is left is below `2^521 + 2^513`.
* `sqrOps`: `[a]^2 R⁻¹`. The multiplicands of row `i` are `a_i` and the words
  of `2 [a]` above it, so that no product is doubled; as the rows get
  shorter, the registers of the words of `2 [a]` no longer needed take the
  product's new words, and all seventeen fit in registers. The nine low
  words are then shifted down by 55 bits onto the eight high ones, after
  the lowest word's share of the ninth.
* `tailOps`: the bits above `2^521` added at the bottom, once. That is the
  number modulo `p`, unless it is `p` itself, which it never is: the product
  of two numbers below `p` is a multiple of the prime `p` only if it is zero,
  and then every word above is.
* `addOps` and `subOps`: a difference is nine subtractions, then the borrow
  subtracted at the bottom and the top word cut to 9 bits (`2^521 = p + 1`);
  a sum has `p` subtracted, and added back, masked, where that borrowed.
* `shlOps`: a multiple by `2^k` is a rotation of the 521 bits.

The only registers written are those of the generic arithmetic for nine
words; nothing branches, and every address is an operand's pointer plus a
constant.
-/

@[expose] public section

namespace VG.Impl.Mont.AArch64.P521

open VG.AArch64

/-- The prime, `2^521 - 1`. -/
def prime : Nat := 2 ^ 521 - 1

/-- `d = n + m`, with the carry unless it starts a chain. -/
def addc (first : Bool) (d n m : Reg) : Op := if first then .adds d n m else .adcs d n m

/-- `d = n - m`, with the borrow unless it starts a chain. -/
def subc (first : Bool) (d n m : Reg) : Op := if first then .subs d n m else .sbcs d n m

/-! ## The product -/

/-- Word `k` of the accumulator, whose registers are used again every eleven words. -/
def acc (k : Nat) : Reg :=
  [Reg.x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x21, .x22, .x23].getD (k % 11) .x8

/-- Word `j` of `[b]`, the lowest eight of which are in registers; the top one is loaded into `x2`. -/
def bReg (j : Nat) : Reg := [Reg.x3, .x4, .x5, .x6, .x16, .x17, .x24, .x25].getD j .x2

/-- The load of word `j` of `[b]`, if it is not in a register. -/
def bLoad (j : Nat) : List Op := if j < 8 then [] else [.ld 1 j .x2]

/-- Row 0, straight into the accumulator. -/
def row0 : List Op :=
  .ld 0 0 .x1 :: ((List.range 9).flatMap fun j => bLoad j ++ [.mul (acc j) .x1 (bReg j)]) ++
    ((List.range 8).flatMap fun j => [.umulh .x2 .x1 (bReg j), addc (j == 0) (acc (j + 1)) (acc (j + 1)) .x2]) ++
    bLoad 8 ++ [.umulh .x2 .x1 .x2, .adc (acc 9) .x2 .x7]

/-- Row `i`: `a_i [b]` added to the accumulator from word `i`, whose words
above `i + 8` are zero. -/
def row (i : Nat) : List Op :=
  .ld 0 i .x1 :: ((List.range 9).flatMap fun j =>
      bLoad j ++ [.mul .x2 .x1 (bReg j), addc (j == 0) (acc (i + j)) (acc (i + j)) .x2]) ++
    bLoad 8 ++ [.umulh .x2 .x1 .x2, .adc (acc (i + 9)) .x2 .x7] ++
    ((List.range 8).flatMap fun j =>
      [.umulh .x2 .x1 (bReg j), addc (j == 0) (acc (i + j + 1)) (acc (i + j + 1)) .x2]) ++
    [.adc (acc (i + 9)) (acc (i + 9)) .x7]

/-- Row 8, whose new word is zero: `a_8` and `b_8` are below `2^9`. -/
def row8 : List Op :=
  .ld 0 8 .x1 :: ((List.range 9).flatMap fun j =>
      bLoad j ++ [.mul .x2 .x1 (bReg j), addc (j == 0) (acc (8 + j)) (acc (8 + j)) .x2]) ++
    (List.range 8).flatMap fun j => [.umulh .x2 .x1 (bReg j), addc (j == 0) (acc (9 + j)) (acc (9 + j)) .x2]

/-- The words `i` and `i + 1`, done, added eight words up, 9 bits up. -/
def fold (i : Nat) : List Op :=
  [.lsl .x2 (acc i) 9, .extr (acc i) (acc (i + 1)) (acc i) 55, .lsr (acc (i + 1)) (acc (i + 1)) 55,
    .adds (acc (i + 8)) (acc (i + 8)) .x2, .adcs (acc (i + 9)) (acc (i + 9)) (acc i),
    .adc (acc (i + 10)) (acc (i + 10)) (acc (i + 1))]

/-- The word 8, done, added eight words up, 9 bits up. -/
def fold8 : List Op :=
  [.lsl .x2 (acc 8) 9, .lsr (acc 17) (acc 8) 55, .adds (acc 16) (acc 16) .x2, .adc (acc 17) (acc 17) .x7]

/-- `[b]` into registers, and `x7 = 0`. -/
def mulSetup : List Op := ((List.range 8).map fun j => .ld 1 j (bReg j)) ++ [.movz .x7 0]

/-- The product, below `2^521 + 2^513`, in `mulOut`. -/
def mulOps : List Op :=
  mulSetup ++ row0 ++ row 1 ++ fold 0 ++ row 2 ++ row 3 ++ fold 2 ++ row 4 ++ row 5 ++ fold 4 ++
    row 6 ++ row 7 ++ fold 6 ++ row8 ++ fold8

/-- The product's words. -/
def mulOut : List Reg := (List.range 9).map fun k => acc (9 + k)

/-! ## The square -/

/-- Word `j` of `2 [a]`, for `2 ≤ j ≤ 8`. -/
def dReg (j : Nat) : Reg := [Reg.x4, .x5, .x6, .x16, .x17, .x24, .x25].getD (j - 2) .x4

/-- Word `k` of the product: from the tenth on, in the register of a word of `2 [a]` no longer needed. -/
def pReg (k : Nat) : Reg :=
  if k < 10 then [Reg.x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x21, .x22].getD k .x8 else dReg (k - 8)

/-- The words of `2 [a]` from the third on, each from two words of `[a]`. -/
def sqrSetup : List Op :=
  .ld 0 1 .x1 :: ((List.range 7).flatMap fun j =>
    let n := if j % 2 = 0 then Reg.x3 else .x1
    let o := if j % 2 = 0 then Reg.x1 else .x3
    [.ld 0 (j + 2) n, .extr (dReg (j + 2)) n o 63]) ++ [.movz .x7 0]

/-- The multiplicand of row `i` at word `i + j`: `a_i`, twice the next word, then words of `2 [a]`. -/
def sReg (i j : Nat) : Reg := if j = 0 then .x1 else if j = 1 then .x3 else dReg (i + j)

/-- `a_i` into `x1` and twice `a_(i+1)` into `x3`. -/
def sLoad (i : Nat) : List Op := [.ld 0 i .x1, .ld 0 (i + 1) .x3, .lsl .x3 .x3 1]

/-- Row 0, straight into the product's words. -/
def sRow0 : List Op :=
  sLoad 0 ++ ((List.range 9).map fun j => .mul (pReg j) .x1 (sReg 0 j)) ++
    ((List.range 8).flatMap fun j => [.umulh .x2 .x1 (sReg 0 j), addc (j == 0) (pReg (j + 1)) (pReg (j + 1)) .x2]) ++
    [.umulh .x2 .x1 (sReg 0 8), .adc (pReg 9) .x2 .x7]

/-- Row `i`, `1 ≤ i ≤ 7`: its `9 - i` products, from word `2 i` to word `i + 8`, and the new word `i + 9`. -/
def sRow (i : Nat) : List Op :=
  sLoad i ++
    ((List.range (9 - i)).flatMap fun j =>
      [.mul .x2 .x1 (sReg i j), addc (j == 0) (pReg (2 * i + j)) (pReg (2 * i + j)) .x2]) ++
    [.umulh .x2 .x1 (sReg i (8 - i)), .adc (pReg (i + 9)) .x2 .x7] ++
    ((List.range (8 - i)).flatMap fun j =>
      [.umulh .x2 .x1 (sReg i j), addc (j == 0) (pReg (2 * i + j + 1)) (pReg (2 * i + j + 1)) .x2]) ++
    [.adc (pReg (i + 9)) (pReg (i + 9)) .x7]

/-- Row 8: the square of the top word. -/
def sRow8 : List Op := [.ld 0 8 .x1, .mul .x2 .x1 .x1, .add (pReg 16) (pReg 16) .x2]

/-- The nine low words, shifted down by 55 bits, added to the eight high
ones, with the lowest word's share of word 8 first. -/
def sFold : List Op :=
  [.lsl .x2 (pReg 0) 9, .adds (pReg 8) (pReg 8) .x2] ++
    ((List.range 8).map fun j => .extr (pReg j) (pReg (j + 1)) (pReg j) 55) ++ [.lsr (pReg 8) (pReg 8) 55] ++
    ((List.range 8).map fun j => .adcs (pReg j) (pReg (9 + j)) (pReg j)) ++ [.adc (pReg 8) (pReg 8) .x7]

/-- The square, below `2^521 + 2^512`, in `sqrOut`. -/
def sqrOps : List Op :=
  sqrSetup ++ sRow0 ++ sRow 1 ++ sRow 2 ++ sRow 3 ++ sRow 4 ++ sRow 5 ++ sRow 6 ++ sRow 7 ++ sRow8 ++ sFold

/-- The square's words. -/
def sqrOut : List Reg := (List.range 9).map pReg

/-! ## The bits above 2^521 -/

/-- The number in `w`, its bits above `2^521` added at the bottom. -/
def tailOps (w : List Reg) : List Op :=
  let t := w.getD 8 .x8
  [.lsr .x1 t 9, .movz .x2 511, .low t t .x2 9, .adds (w.getD 0 .x8) (w.getD 0 .x8) .x1] ++
    ((List.range 7).map fun k => .adcs (w.getD (k + 1) .x8) (w.getD (k + 1) .x8) .x7) ++ [.adc t t .x7]

/-! ## Sums and differences -/

/-- The words of a sum or difference. -/
def lReg (k : Nat) : Reg := acc k

/-- The words of a sum or difference. -/
def linOut : List Reg := (List.range 9).map lReg

/-- `[a] - [b]` modulo `2^576`, and the carry: whether it did not borrow. -/
def subChain : List Op :=
  ((List.range 9).map fun k => .ld 0 k (lReg k)) ++ [.movz .x7 0] ++
    (List.range 9).flatMap fun k => [.ld 1 k .x2, subc (k == 0) (lReg k) (lReg k) .x2]

/-- One less where the carry is clear, and the top word cut to 9 bits. -/
def decOps : List Op :=
  ((List.range 9).map fun k => .sbcs (lReg k) (lReg k) .x7) ++ [.movz .x2 511, .low (lReg 8) (lReg 8) .x2 9]

/-- `[a] - [b] mod p`. -/
def subOps : List Op := subChain ++ decOps

/-- `[a] + [b]`, below `2^576`. -/
def addChain : List Op :=
  ((List.range 9).map fun k => .ld 0 k (lReg k)) ++ [.movz .x7 0] ++
    (List.range 9).flatMap fun k => [.ld 1 k .x2, addc (k == 0) (lReg k) (lReg k) .x2]

/-- The words of `p`: `x1` for the eight low ones, `x2` for the top one. -/
def primeOps : List Op := [.movz .x2 1, .subs .x1 .x7 .x2, .movz .x2 511]

/-- Word `k` of the number in `x1` (its eight low words) and `x2` (its top word). -/
def pWord (k : Nat) : Reg := if k < 8 then .x1 else .x2

/-- `p` subtracted, and the carry: whether it did not borrow. -/
def subPrime : List Op := (List.range 9).map fun k => subc (k == 0) (lReg k) (lReg k) (pWord k)

/-- The words of `p` if it borrowed, and of zero if not. -/
def maskOps : List Op := [.sbcs .x1 .x7 .x7, .low .x2 .x1 .x2 9]

/-- The masked words of `p` added. -/
def addBack : List Op := (List.range 9).map fun k => addc (k == 0) (lReg k) (lReg k) (pWord k)

/-- `[a] + [b] mod p`. -/
def addOps : List Op := addChain ++ primeOps ++ subPrime ++ maskOps ++ addBack

/-! ## Multiples by powers of two -/

/-- `2^k [a] mod p`, `k` at most 8: its 521 bits rotated. The top word's top
`k` bits come down through `x2`. -/
def shlOps (k : Nat) : List Op :=
  ((List.range 9).map fun j => .ld 0 j (lReg j)) ++ [.lsl .x2 (lReg 8) 55] ++
    ((List.range 8).map fun j => .extr (lReg (8 - j)) (lReg (8 - j)) (lReg (7 - j)) (64 - k)) ++
    [.extr (lReg 0) (lReg 0) .x2 (64 - k), .movz .x1 511, .low (lReg 8) (lReg 8) .x1 9]

/-! ## Code -/

/-- The instructions, for operands at `(ra, a)` and `(rb, b)`. -/
def code (ra rb : Reg) (a b : Nat) (os : List Op) : List Instr :=
  os.map (Op.instr fun k => if k = 0 then (ra, a) else (rb, b))

/-- `[ro + o] = [ra + a] [rb + b] R⁻¹ mod p`. -/
def mulR (ra rb ro : Reg) (o a b : Nat) : List Instr :=
  code ra rb a b (mulOps ++ tailOps mulOut) ++ storesR ro mulOut o

/-- `[ro + o] = [ra + a]^2 R⁻¹ mod p`. -/
def sqrR (ra ro : Reg) (o a : Nat) : List Instr :=
  code ra ra a a (sqrOps ++ tailOps sqrOut) ++ storesR ro sqrOut o

/-- `[o] = [a] + [b] mod p`. -/
def add (o a b : Nat) : List Instr := code .x0 .x0 a b addOps ++ storesR .x0 linOut o

/-- `[o] = [a] - [b] mod p`. -/
def sub (o a b : Nat) : List Instr := code .x0 .x0 a b subOps ++ storesR .x0 linOut o

/-- `[o] = 2^k [a] mod p`. -/
def shl (k o a : Nat) : List Instr := code .x0 .x0 a a (shlOps k) ++ storesR .x0 linOut o

end VG.Impl.Mont.AArch64.P521
