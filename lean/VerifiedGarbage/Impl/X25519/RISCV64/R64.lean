module

public import VerifiedGarbage.Impl.X25519.RISCV64
public import VerifiedGarbage.Impl.X448.RISCV64.R64

/-!
# X25519: RISC-V implementation with 64-bit limbs

`vg_x25519(out = a0, scalar = a1, point = a2, scratch = a3)`.

The algorithm and layout of `Impl/X25519/RISCV64.lean` (its ladder, its
inversion, its decoding, its bits of the scalar and its final reduction), but
for the field arithmetic, which takes a field element's 32 bytes as four
64-bit words `x₀ + 2⁶⁴ x₁ + 2¹²⁸ x₂ + 2¹⁹² x₃` (the same number as its eight
32-bit limbs) and multiplies them with `mul` and `mulhu`, the low and high
words of a 128-bit product, carrying with `sltu` (the sum `d := d + x`
wrapped around if and only if `d < x` after it), as X448's
(`Impl/X448/RISCV64/R64.lean`) does. The arithmetic uses only the eleven
registers `t0`, `t3`–`t6`, `a1`, `a2`, `a4`–`a7`, so the ladder's `t1` (the
counter), `t2` (the swap), `a0` (`out`) and `a3` (the working space) stay
where they are; its registers, and the code of a term of a product and of a
word of a sum, a difference and a swap, are X448's. The operations:

* `product`: the eight words of `[a] · [b]` at `acc` (`ACC`), by columns
  (product scanning) into a three-word accumulator, with `b` in registers and
  `a_i` loaded for each product; `square`: the cross products `a_i a_j` (`i < j`),
  once each, then the words of twice their sum plus the squares `a_i²`.
* `reduce`: the product `L + 2²⁵⁶ H` becomes `L + 38 H` (`2²⁵⁶ ≡ 38`), in
  registers, and its top word `c ≤ 40` is folded in as `38 c` twice
  (`fold`) before the words are stored.
* `add`, `sub`: with carries (borrows), the carry folded in (the borrow taken
  out) as 38, twice each.
* `cswap`: with the mask `-swap` (in `t0`), a doubleword at a time.

The only branches are on the loop counters, and every address is a pointer
plus a constant or a counter, so only the pointers can affect timing.
-/

@[expose] public section

namespace VG.Impl.X25519.RISCV64.R64

open VG.RISCV64
open VG.Impl.X25519.RISCV64 (X1 X2 Z2 X3 Z3 A B C D AA BB E DA CB A24 R ACC BITS align setup bits
  freeze one)

/-! ## Registers and products

X448's (`Impl/X448/RISCV64/R64.lean`): `w i` is `t3`–`t6` for `i < 4`, the
accumulator of column `k` is `rr k, rr (k + 1), rr (k + 2)` (`a4`–`a6`,
rotating), `macc` adds a product to it and `zero3` zeroes it; so are the
words of a sum and a difference (`addStep`, `subStep`: word `k` into `w k`,
the carry or borrow in and out in `a5`) and of a swap (`cswapStep`). -/

open VG.Impl.X448.RISCV64.R64 (w rr macc zero3 addStep subStep)

/-- The four words `w i` stored at `[o]`. -/
def st4 (o : Nat) : List Instr := (List.range 4).map fun i => .store .d (w i) .a3 (o + 8 * i)

/-- The four words at `[o]` loaded into `w 0`–`w 3`. -/
def ld4 (o : Nat) : List Instr := (List.range 4).map fun i => .load .d (w i) .a3 (o + 8 * i)

/-- The terms `(i, j)` of column `k` of a product of four words, `i`
descending. -/
def colPairs (k : Nat) : List (Nat × Nat) :=
  ((List.range 4).reverse.filter fun i => i ≤ k ∧ k - i < 4).map fun i => (i, k - i)

/-- A term `a_i b_j` of a product: `a_i` loaded into `t0`, `b_j` in `w j`. -/
def mulTerm (a k : Nat) (p : Nat × Nat) : List Instr :=
  .load .d .t0 .a3 (a + 8 * p.1) :: macc (rr k) (rr (k + 1)) (rr (k + 2)) .t0 (w p.2)

/-- The end of column `k`: its low word stored at `acc + 8k`, and the
register zeroed, which becomes the top word of column `k + 1`'s accumulator. -/
def colEnd (acc k : Nat) : List Instr := [.store .d (rr k) .a3 (acc + 8 * k), .li (rr k) 0]

/-- Column `k` of `[a] · [b]`. -/
def mulCol (acc a k : Nat) : List Instr := (colPairs k).flatMap (mulTerm a k) ++ colEnd acc k

/-- The eight words of `[a] · [b]` at `acc`. -/
def product (acc a b : Nat) : List Instr :=
  ld4 b ++ zero3 ++ (List.range 8).flatMap (mulCol acc a)

/-- A cross term `a_j a_i` (`j < i`) of a square, both in registers. -/
def sqTerm (k : Nat) (p : Nat × Nat) : List Instr :=
  macc (rr k) (rr (k + 1)) (rr (k + 2)) (w p.2) (w p.1)

/-- Column `k` of the cross products of `[a]`. -/
def sqCol (acc k : Nat) : List Instr :=
  ((colPairs k).filter fun p => p.2 < p.1).flatMap (sqTerm k) ++ colEnd acc k

/-- Word `k` of `2 X + Σ a_i² 2¹²⁸ⁱ`, for the cross products' sum `X` at
`acc`, into `acc + 8k`: `a5` holds `X`'s word `k - 1` (then `k`), `a4` the
carry, and `t3` the high word of the last square. -/
def dblStep (acc a k : Nat) : List Instr :=
  [.shift .srl .d .a7 .a5 63, .load .d .a5 .a3 (acc + 8 * k), .shift .sll .d .a6 .a5 1,
   .logic .or .a6 .a6 .a7] ++
  (if k % 2 = 0 then
    [.load .d .t3 .a3 (a + 8 * (k / 2)), .mul .t0 .t3 .t3, .mulhu .t3 .t3 .t3, .add .a6 .a6 .t0,
      .sltu .a7 .a6 .t0]
   else [.add .a6 .a6 .t3, .sltu .a7 .a6 .t3]) ++
  [.add .a6 .a6 .a4, .sltu .t0 .a6 .a4, .add .a4 .a7 .t0, .store .d .a6 .a3 (acc + 8 * k)]

/-- The eight words of `[a]²` at `acc`. -/
def square (acc a : Nat) : List Instr :=
  ld4 a ++ zero3 ++ (List.range 8).flatMap (sqCol acc) ++ [.li .a5 0, .li .a4 0] ++
    (List.range 8).flatMap (dblStep acc a)

/-! ## Reduction -/

/-- `w 0`–`w 3` plus `38 c` (`c` in `a5`, below `2⁵⁸`; 38 in `a4`), the carry
out into `a5`; through `a7` and `t0`. -/
def fold : List Instr :=
  [.mul .a7 .a5 .a4, .add (w 0) (w 0) .a7, .sltu .t0 (w 0) .a7,
   .add (w 1) (w 1) .t0, .sltu .t0 (w 1) .t0,
   .add (w 2) (w 2) .t0, .sltu .t0 (w 2) .t0,
   .add (w 3) (w 3) .t0, .sltu .a5 (w 3) .t0]

/-- `w 0`–`w 3` less `38 c` (`c` in `a5`, below `2⁵⁸`; 38 in `a4`), the
borrow out into `a5`; through `a7` and `t0`. -/
def unfold : List Instr :=
  [.mul .a7 .a5 .a4, .sltu .t0 (w 0) .a7, .sub (w 0) (w 0) .a7,
   .sltu .a7 (w 1) .t0, .sub (w 1) (w 1) .t0,
   .sltu .t0 (w 2) .a7, .sub (w 2) (w 2) .a7,
   .sltu .a5 (w 3) .t0, .sub (w 3) (w 3) .t0]

/-- The register of the high word of `38 H_k`: `a1` and `a2` in turn. -/
def hr (k : Nat) : Reg := if k % 2 = 0 then .a1 else .a2

/-- The carry out of word `k` of the reduction: `a5` and `a6` in turn. -/
def cr (k : Nat) : Reg := if k % 2 = 0 then .a5 else .a6

/-- Word `k` of `L + 38 H` (`L` and `H` the halves of the product at `acc`;
38 in `a4`) into `w k`: `L_k` plus the low word of `38 H_k`, plus the high
word of `38 H_{k-1}` and the carry in for `k > 0`; the high word of `38 H_k`
into `hr k`, the carry out into `cr k`. -/
def redStep (acc k : Nat) : List Instr :=
  [.load .d (w k) .a3 (acc + 8 * k), .load .d .a7 .a3 (acc + 32 + 8 * k), .mul .t0 .a7 .a4,
    .mulhu (hr k) .a7 .a4, .add (w k) (w k) .t0, .sltu (cr k) (w k) .t0] ++
  (if 0 < k then
    [.add (w k) (w k) (hr (k + 1)), .sltu .a7 (w k) (hr (k + 1)), .add (cr k) (cr k) .a7,
     .add (w k) (w k) (cr (k + 1)), .sltu .a7 (w k) (cr (k + 1)), .add (cr k) (cr k) .a7]
   else [])

/-- The product at `acc` reduced into `[o]`. -/
def reduce (acc o : Nat) : List Instr :=
  .li .a4 38 :: (List.range 4).flatMap (redStep acc) ++ [.add .a5 .a2 .a6] ++ fold ++ fold ++ st4 o

/-- `[o] = [a] · [b]`, a square if `a = b`, with the product at `acc`; `o`
may be `a` or `b`. -/
def mulAt (acc o a b : Nat) : Prog isa :=
  .block ((if a = b then square acc a else product acc a b) ++ reduce acc o)

/-- `[o] = [a] · [b]`, with the product at `ACC`. -/
abbrev mul (o a b : Nat) : Prog isa := mulAt ACC o a b

/-! ## Sums and differences -/

/-- `[o] = [a] + [b]`. -/
def add (o a b : Nat) : List Instr :=
  (List.range 4).flatMap (addStep a b) ++ .li .a4 38 :: fold ++ fold ++ st4 o

/-- `[o] = [a] - [b]`. -/
def sub (o a b : Nat) : List Instr :=
  (List.range 4).flatMap (subStep a b) ++ .li .a4 38 :: unfold ++ unfold ++ st4 o

/-! ## The swap -/

/-- Swaps `[x]` and `[y]` if the mask `t0` is all ones (and not if it is zero),
a doubleword at a time (X448's `cswapStep`, named in full: the 32-bit one of
`Impl/X25519/RISCV64.lean` would be found first). -/
def cswap (x y : Nat) : List Instr :=
  (List.range 4).flatMap (VG.Impl.X448.RISCV64.R64.cswapStep x y)

/-! ## The ladder and the inversion, as in `Impl/X25519/RISCV64.lean` -/

/-- The mask `-swap` into `t0`. -/
def mask : List Instr := [.li .t0 0, .sub .t0 .t0 .t2]

/-- The start of an iteration of the ladder, for the bit `t = t1 - 1`: `k_t`
from `BITS`, `swap ^= k_t`, the swaps by the mask `-swap`, and `swap = k_t`. -/
def stepHead : List Instr :=
  [.addi .t1 .t1 (-1), .add .a1 .a3 .t1, .load .b .a1 .a1 BITS, .logic .xor .t2 .t2 .a1] ++ mask ++
    cswap X2 X3 ++ cswap Z2 Z3 ++ [.addi .t2 .a1 0]

/-- One iteration of the ladder: `stepHead`, then the formulas of RFC 7748 §5
in order. -/
def step : Prog isa :=
  .seq (.block stepHead) <|
  .seq (.block (add A X2 Z2)) <| .seq (mul AA A A) <| .seq (.block (sub B X2 Z2)) <|
  .seq (mul BB B B) <| .seq (.block (sub E AA BB)) <| .seq (.block (add C X3 Z3)) <|
  .seq (.block (sub D X3 Z3)) <| .seq (mul DA D A) <| .seq (mul CB C B) <|
  .seq (.block (add X3 DA CB)) <| .seq (mul X3 X3 X3) <| .seq (.block (sub Z3 DA CB)) <|
  .seq (mul Z3 Z3 Z3) <| .seq (mul Z3 X1 Z3) <| .seq (mul X2 AA BB) <| .seq (mul Z2 A24 E) <|
  .seq (.block (add Z2 AA Z2)) <| .seq (mul Z2 E Z2) (.block [])

/-- The 255 iterations, for `t` from 254 down to 0, with `swap = 0`. -/
def ladder : Prog isa :=
  .seq (.block [.li .t1 255, .li .t2 0]) (.loop step (.nonzero .t1))

/-- The swap after the loop. -/
def lastSwap : List Instr := mask ++ cswap X2 X3 ++ cswap Z2 Z3

/-- `R = R²`, then `R = R · Z2` unless `t = t1 - 1` is 4 or 2. -/
def invStep : Prog isa :=
  .seq (.block [.addi .t1 .t1 (-1)]) <| .seq (mul R R R) <|
  .seq (.block [.addi .a2 .t1 (-4)]) <|
  .seq (.ite (.zero .a2) (.block [])
    (.seq (.block [.addi .a2 .t1 (-2)]) (.ite (.zero .a2) (.block []) (mul R R Z2))))
    (.block [])

/-- `[R] = [Z2]^(p-2)`, square-and-multiply over the bits of `p - 2` from 254
down to 0. -/
def invert : Prog isa := .seq (.block (one ++ [.li .t1 255])) (.loop invStep (.nonzero .t1))

def x25519 : Prog isa :=
  .seq (.block (align ++ setup)) <| .seq bits <| .seq ladder <| .seq (.block lastSwap) <|
    .seq invert <| .seq (mul X2 X2 R) (.block freeze)

end VG.Impl.X25519.RISCV64.R64
