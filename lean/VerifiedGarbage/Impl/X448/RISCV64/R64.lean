module

public import VerifiedGarbage.Impl.X448.RISCV64
public import VerifiedGarbage.Impl.Words.RISCV64.Wide

/-!
# X448: RISC-V implementation with 64-bit limbs

`vg_x448(out = a0, scalar = a1, point = a2, scratch = a3)`.

The algorithm and layout of `Impl/X448/RISCV64.lean` (its ladder, its
decoding, its bits of the scalar and its final reduction), but for the
inversion and the field arithmetic, which takes a field element's 56 bytes as seven
64-bit words `x₀ + 2⁶⁴ x₁ + … + 2³⁸⁴ x₆` (the same number as its fourteen
32-bit limbs) and multiplies them with `mul` and `mulhu`, the low and high
words of a 128-bit product, carrying with `sltu` (the sum `d := d + x`
wrapped around if and only if `d < x` after it). The arithmetic uses only the
eleven registers `t0`, `t3`–`t6`, `a1`, `a2`, `a4`–`a7`, so the ladder's
`t1` (the counter), `t2` (the swap), `a0` (`out`) and `a3` (the working
space) stay where they are:

* `product`: the fourteen words of `[a] · [b]` at `ACC`, by columns (product
  scanning): column `k` adds every `a_i b_j` with `i + j = k` into a
  three-word accumulator, whose low word is word `k` of the product; the
  accumulator rotates through `a4`–`a6` (`rr`). The terms are
  software-pipelined (`pipe`): each term's `mul`/`mulhu` (into `a7`, `t0` and
  `t3`, `t6` in turn) and the next term's two operand loads (into `a1`, `a2`)
  are issued a term ahead of its sums, so that an in-order core does not
  wait for them.
* `square`: the same for the cross products `a_i a_j` (`i < j`), once each,
  then the words of twice their sum plus the squares `a_i²` (`dblStep`).
* `reduce`: the product `L + 2⁴⁴⁸ H` becomes `L + H + (H - H mod 2²²⁴) +
  rot(H)` (`rot(H)` is `H` rotated by 224 bits, its words 32 bits off `H`'s),
  since `2⁴⁴⁸ ≡ 2²²⁴ + 1`, in registers, and its top word `c < 4` is folded in
  as `c + 2²²⁴ c` twice (`foldR`) before the words are stored.
* `add`, `sub`: with carries (borrows), the carry folded in (`foldR`), the
  borrow taken out (`unfoldR`) as `1 + 2²²⁴`, twice each.
* `mulSmall`: by a one-word constant (the ladder's `a24`), with `mul` and
  `mulhu` a word at a time, carrying into the next high word, and the top
  word folded in twice (`foldR`).
* `invert`: `z^(p-2)` by the addition chain of `Proof/X448/Invert.lean`
  (`chain223`, runs of squarings `sqn` in a loop on `t1`, then `invTail`),
  which Ed448's square root shares as far as `z^(2²²³ - 1)`.
* `cswap`: with the mask `-swap` (in `t0`), a word at a time.

The only branches are on the loop counters, and every address is a pointer
plus a constant or a counter, so only the pointers can affect timing.
-/

@[expose] public section

namespace VG.Impl.X448.RISCV64.R64

open VG.RISCV64 VG.Impl.Words.RISCV64
open VG.Impl.X448.RISCV64 (X1 X2 Z2 X3 Z3 A B C D AA BB E DA CB A24 R ACC BITS align setup setupBase bits freeze one)

/-! ## Registers -/

/-- An operand's words in a product (the first six) or a result's words. -/
def WR : List Reg := [.t3, .t4, .t5, .t6, .a1, .a2, .a4]

/-- `WR[i]`. -/
def w (i : Nat) : Reg := WR.getD i .t3

/-- A product's three-word accumulator, rotating: column `k`'s is
`rr k, rr (k + 1), rr (k + 2)`. -/
def RR : List Reg := [.a4, .a5, .a6]

def rr (i : Nat) : Reg := RR.getD (i % 3) .a4

/-- The seven words `w i` stored at `[o]`. -/
def stW (o : Nat) : List Instr := (List.range 7).map fun i => .store .d (w i) .a3 (o + 8 * i)

/-- The six words at `[o]` loaded into `w 0`–`w 5`. -/
def ld6 (o : Nat) : List Instr := (List.range 6).map fun i => .load .d (w i) .a3 (o + 8 * i)

/-! ## Products -/

/-- `l + 2⁶⁴ h + 2¹²⁸ t += x · y`, through `a7` (the low word, then the
carry) and `t0` (the high word, then the carry); `x` or `y` may be `t0`. -/
def macc (l h t x y : Reg) : List Instr :=
  [.mul .a7 x y, .mulhu .t0 x y, .add l l .a7, .sltu .a7 l .a7, .add .t0 .t0 .a7,
   .add h h .t0, .sltu .t0 h .t0, .add t t .t0]

/-- The terms `(i, j)` of column `k` of a product of seven words, `i`
descending. -/
def colPairs (k : Nat) : List (Nat × Nat) :=
  ((List.range 7).reverse.filter fun i => i ≤ k ∧ k - i < 7).map fun i => (i, k - i)

/-- The end of column `k`: its low word stored at `ACC + 8k`, and the
register zeroed, which becomes the top word of column `k + 1`'s accumulator. -/
def colEnd (k : Nat) : List Instr := [.store .d (rr k) .a3 (ACC + 8 * k), .li (rr k) 0]

/-- The accumulator zeroed. -/
def zero3 : List Instr := [.li .a4 0, .li .a5 0, .li .a6 0]

/-- Word `k` of `2 X + Σ a_i² 2¹²⁸ⁱ`, for the cross products' sum `X` at
`ACC`, into `ACC + 8k`: `a5` holds `X`'s word `k - 1` (then `k`), `a4` the
carry, and `t3` the high word of the last square. -/
def dblStep (a k : Nat) : List Instr :=
  [.shift .srl .d .a7 .a5 63, .load .d .a5 .a3 (ACC + 8 * k), .shift .sll .d .a6 .a5 1,
   .logic .or .a6 .a6 .a7] ++
  (if k % 2 = 0 then
    [.load .d .t3 .a3 (a + 8 * (k / 2)), .mul .t0 .t3 .t3, .mulhu .t3 .t3 .t3, .add .a6 .a6 .t0,
      .sltu .a7 .a6 .t0]
   else [.add .a6 .a6 .t3, .sltu .a7 .a6 .t3]) ++
  [.add .a6 .a6 .a4, .sltu .t0 .a6 .a4, .add .a4 .a7 .t0, .store .d .a6 .a3 (ACC + 8 * k)]

/-- The registers of term `n`'s product, low and high: `a7`, `t0` and `t3`,
`t6` in turn. -/
def PR (n : Nat) : Reg × Reg := if n % 2 = 0 then (.a7, .t0) else (.t3, .t6)

/-- A product's terms `(k, i, j)`, column by column, from each column's pairs. -/
def terms (ps : Nat → List (Nat × Nat)) : List (Nat × Nat × Nat) :=
  (List.range 14).flatMap fun k => (ps k).map fun p => (k, p.1, p.2)

/-- Term `n` of `ts`. -/
def tm (ts : List (Nat × Nat × Nat)) (n : Nat) : Nat × Nat × Nat := ts.getD n (0, 0, 0)

/-- The index of column `k`'s first term, for `cs c` terms in column `c`. -/
def pstart (cs : Nat → Nat) (k : Nat) : Nat := ((List.range k).map cs).sum

/-- Term `n`'s operands, `a_i` into `a1` and `b_j` into `a2`, if it is one. -/
def ldN (a b : Nat) (ts : List (Nat × Nat × Nat)) (n : Nat) : List Instr :=
  if n < ts.length then [.load .d .a1 .a3 (a + 8 * (tm ts n).2.1), .load .d .a2 .a3 (b + 8 * (tm ts n).2.2)]
  else []

/-- Term `n`'s product, from `a1` and `a2`, if it is one. -/
def mulN (ts : List (Nat × Nat × Nat)) (n : Nat) : List Instr :=
  if n < ts.length then mulWide (PR n).1 (PR n).2 .a1 .a2 else []

/-- Term `n`'s product added to column `k`'s three-word accumulator. -/
def accum (k n : Nat) : List Instr :=
  [.add (rr k) (rr k) (PR n).1, .sltu (PR n).1 (rr k) (PR n).1, .add (PR n).2 (PR n).2 (PR n).1,
    .add (rr (k + 1)) (rr (k + 1)) (PR n).2, .sltu (PR n).2 (rr (k + 1)) (PR n).2,
    .add (rr (k + 2)) (rr (k + 2)) (PR n).2]

/-- Term `n`, of column `k`: the next term's product and the operands of the
one after it, issued before this one's sums, which they do not depend on. -/
def pstep (a b : Nat) (ts : List (Nat × Nat × Nat)) (k n : Nat) : List Instr :=
  mulN ts (n + 1) ++ ldN a b ts (n + 2) ++ accum k n

/-- Column `k`: its `cs k` terms, then its end. -/
def pcol (a b : Nat) (ts : List (Nat × Nat × Nat)) (cs : Nat → Nat) (k : Nat) : List Instr :=
  (List.range' (pstart cs k) (cs k)).flatMap (pstep a b ts k) ++ colEnd k

/-- The terms `ts` of `[a]` and `[b]` into the fourteen columns at `ACC`,
software-pipelined: the first term's product and the second's operands ahead. -/
def pipe (a b : Nat) (ts : List (Nat × Nat × Nat)) (cs : Nat → Nat) : List Instr :=
  zero3 ++ ldN a b ts 0 ++ mulN ts 0 ++ ldN a b ts 1 ++ (List.range 14).flatMap (pcol a b ts cs)

/-- The cross terms `(i, j)` (`j < i`) of a square's column `k`. -/
def sqPairs (k : Nat) : List (Nat × Nat) := (colPairs k).filter fun p => p.2 < p.1

/-- The fourteen words of `[a] · [b]` at `ACC`. -/
def product (a b : Nat) : List Instr := pipe a b (terms colPairs) fun k => (colPairs k).length

/-- The fourteen words of `[a]²` at `ACC`: the cross products, then twice
their sum plus the squares. -/
def square (a : Nat) : List Instr :=
  pipe a a (terms sqPairs) (fun k => (sqPairs k).length) ++ [.li .a5 0, .li .a4 0] ++
    (List.range 14).flatMap (dblStep a)

/-! ## Reduction -/

/-- `w 0`–`w 6` plus `c (1 + 2²²⁴)` (`c < 2³²`), the carry out into `c`;
through `a7` and `t0`. -/
def foldR (c : Reg) : List Instr :=
  [.add (w 0) (w 0) c, .sltu .t0 (w 0) c,
   .add (w 1) (w 1) .t0, .sltu .t0 (w 1) .t0,
   .add (w 2) (w 2) .t0, .sltu .t0 (w 2) .t0,
   .add (w 3) (w 3) .t0, .sltu .t0 (w 3) .t0,
   .shift .sll .d .a7 c 32, .add (w 3) (w 3) .a7, .sltu .a7 (w 3) .a7, .add .t0 .t0 .a7,
   .add (w 4) (w 4) .t0, .sltu .t0 (w 4) .t0,
   .add (w 5) (w 5) .t0, .sltu .t0 (w 5) .t0,
   .add (w 6) (w 6) .t0, .sltu c (w 6) .t0]

/-- `w 0`–`w 6` less `c (1 + 2²²⁴)` (`c < 2³²`), the borrow out into `c`;
through `a7` and `t0`. -/
def unfoldR (c : Reg) : List Instr :=
  [.sltu .t0 (w 0) c, .sub (w 0) (w 0) c,
   .sltu .a7 (w 1) .t0, .sub (w 1) (w 1) .t0,
   .sltu .t0 (w 2) .a7, .sub (w 2) (w 2) .a7,
   .sltu .a7 (w 3) .t0, .sub (w 3) (w 3) .t0,
   .shift .sll .d .t0 c 32, .sltu c (w 3) .t0, .sub (w 3) (w 3) .t0, .add .a7 .a7 c,
   .sltu .t0 (w 4) .a7, .sub (w 4) (w 4) .a7,
   .sltu .a7 (w 5) .t0, .sub (w 5) (w 5) .t0,
   .sltu c (w 6) .a7, .sub (w 6) (w 6) .a7]

/-- Word `k` of `L + H + (H - H mod 2²²⁴) + rot(H)` (`L` and `H` the halves
of the product at `ACC`) into `w k`, with the carry in `cin` and out in
`cout`: `L_k + H_k`, plus `H_k` again for `k ≥ 4` and `H₃`'s upper half for
`k = 3`, plus `rot(H)`'s word `k`, `H_{k+3}`'s upper half and `H_{k+4}`'s
lower half (indices modulo 7), plus the carry in for `k > 0`. -/
def redStep (k : Nat) (cin cout : Reg) : List Instr :=
  [.load .d (w k) .a3 (ACC + 8 * k), .load .d .a7 .a3 (ACC + 56 + 8 * k), .add (w k) (w k) .a7,
    .sltu cout (w k) .a7] ++
  (if 4 ≤ k then [.add (w k) (w k) .a7, .sltu .a7 (w k) .a7, .add cout cout .a7] else []) ++
  (if k = 3 then
    [.shift .srl .d .a7 .a7 32, .shift .sll .d .a7 .a7 32, .add (w k) (w k) .a7,
      .sltu .a7 (w k) .a7, .add cout cout .a7]
   else []) ++
  [.load .d .a7 .a3 (ACC + 56 + 8 * ((k + 3) % 7)), .shift .srl .d .a7 .a7 32,
   .load .d .t0 .a3 (ACC + 56 + 8 * ((k + 4) % 7)), .shift .sll .d .t0 .t0 32,
   .logic .or .a7 .a7 .t0, .add (w k) (w k) .a7, .sltu .a7 (w k) .a7, .add cout cout .a7] ++
  (if 0 < k then [.add (w k) (w k) cin, .sltu .a7 (w k) cin, .add cout cout .a7] else [])

/-- The carry out of word `k` of the reduction: `a5` and `a6` in turn. -/
def cr (k : Nat) : Reg := if k % 2 = 0 then .a5 else .a6

/-- The product at `ACC` reduced into `[o]`. -/
def reduce (o : Nat) : List Instr :=
  (List.range 7).flatMap (fun k => redStep k (cr (k + 1)) (cr k)) ++ foldR .a5 ++ foldR .a5 ++
    stW o

/-- `[o] = [a] · [b]`, a square if `a = b`; `o` may be `a` or `b`. -/
def mul (o a b : Nat) : Prog isa :=
  .block ((if a = b then square a else product a b) ++ reduce o)

/-! ## Sums and differences -/

/-- Word `k` of `[a] + [b]` into `w k`, the carry in `a5` (in and out). -/
def addStep (a b k : Nat) : List Instr :=
  if k = 0 then
    [.load .d (w 0) .a3 a, .load .d .a7 .a3 b, .add (w 0) (w 0) .a7, .sltu .a5 (w 0) .a7]
  else
    [.load .d (w k) .a3 (a + 8 * k), .load .d .a7 .a3 (b + 8 * k), .add (w k) (w k) .a7,
      .sltu .a6 (w k) .a7, .add (w k) (w k) .a5, .sltu .a7 (w k) .a5, .add .a5 .a6 .a7]

/-- `[o] = [a] + [b]`. -/
def add (o a b : Nat) : List Instr :=
  (List.range 7).flatMap (addStep a b) ++ foldR .a5 ++ foldR .a5 ++ stW o

/-- Word `k` of `[a] - [b]` into `w k`, the borrow in `a5` (in and out). -/
def subStep (a b k : Nat) : List Instr :=
  if k = 0 then
    [.load .d (w 0) .a3 a, .load .d .a7 .a3 b, .sltu .a5 (w 0) .a7, .sub (w 0) (w 0) .a7]
  else
    [.load .d (w k) .a3 (a + 8 * k), .load .d .a7 .a3 (b + 8 * k), .sltu .a6 (w k) .a7,
      .sub (w k) (w k) .a7, .sltu .a7 (w k) .a5, .sub (w k) (w k) .a5, .add .a5 .a6 .a7]

/-- `[o] = [a] - [b]`. -/
def sub (o a b : Nat) : List Instr :=
  (List.range 7).flatMap (subStep a b) ++ unfoldR .a5 ++ unfoldR .a5 ++ stW o

/-! ## Multiplication by a one-word constant -/

/-- Word `k` of `c · [a]` (`c` in `a6`) into `w k`, the carry in `a5` (out,
and in for `k > 0`), through `t0` (the word of `[a]`) and `a7` (the high word
of its product). -/
def mulSmallStep (a k : Nat) : List Instr :=
  if k = 0 then
    [.load .d .t0 .a3 a, .mul (w 0) .t0 .a6, .mulhu .a5 .t0 .a6]
  else
    [.load .d .t0 .a3 (a + 8 * k), .mul (w k) .t0 .a6, .mulhu .a7 .t0 .a6,
      .add (w k) (w k) .a5, .sltu .a5 (w k) .a5, .add .a5 .a5 .a7]

/-- `[o] = c · [a]`, for `c < 2³¹` (built in `a6` by `li32`). -/
def mulSmall (o a : Nat) (c : BitVec 32) : List Instr :=
  li32 .a6 c ++ (List.range 7).flatMap (mulSmallStep a) ++ foldR .a5 ++ foldR .a5 ++ stW o

/-! ## The swap -/

/-- Swaps word `k` of `[x]` and `[y]` if the mask `t0` is all ones (and not
if it is zero): `d = t0 ∧ (x ⊕ y)`, `x ⊕= d`, `y ⊕= d`. -/
def cswapStep (x y k : Nat) : List Instr :=
  [.load .d .a2 .a3 (x + 8 * k), .load .d .a4 .a3 (y + 8 * k), .logic .xor .a5 .a2 .a4,
    .logic .and .a5 .a5 .t0, .logic .xor .a2 .a2 .a5, .logic .xor .a4 .a4 .a5,
    .store .d .a2 .a3 (x + 8 * k), .store .d .a4 .a3 (y + 8 * k)]

def cswap (x y : Nat) : List Instr := (List.range 7).flatMap (cswapStep x y)

/-! ## The ladder and the inversion, as in `Impl/X448/RISCV64.lean` -/

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
  .seq (mul Z3 Z3 Z3) <| .seq (mul Z3 X1 Z3) <| .seq (mul X2 AA BB) <| .seq (.block (mulSmall Z2 E 39081)) <|
  .seq (.block (add Z2 AA Z2)) <| .seq (mul Z2 E Z2) (.block [])

/-- The 448 iterations, for `t` from 447 down to 0, with `swap = 0`. -/
def ladder : Prog isa :=
  .seq (.block [.li .t1 448, .li .t2 0]) (.loop step (.nonzero .t1))

/-- The swap after the loop. -/
def lastSwap : List Instr := mask ++ cswap X2 X3 ++ cswap Z2 Z3

/-! ## The inversion

The addition chain of `Proof/X448/Invert.lean`, in the slots `T0`–`T6`
and `R`, which no caller keeps across it: `z^(2^k - 1)` for `k` = 2, 4, 8,
16, 32 and 64 in `T0`–`T5`, the running power in `T6`, then
`z^(2²²³ - 1)` in `R`. -/

def T0 : Nat := 616
def T1 : Nat := 672
def T2 : Nat := 728
def T3 : Nat := 784
def T4 : Nat := 896
def T5 : Nat := 280
def T6 : Nat := 560

/-- `R = R²` (`t1` counting down). -/
def sqStep (o : Nat) : Prog isa := .seq (.block [.addi .t1 .t1 (-1)]) (mul o o o)

/-- `[o] = [x]^(2^n)`, `1 ≤ n ≤ 2048`: one square, then `n - 1` in a loop on
`t1`. -/
def sqn (o x n : Nat) : Prog isa :=
  if n = 1 then mul o x x
  else .seq (mul o x x) (.seq (.block [.li .t1 ((n - 1 : Nat) : Int)]) (.loop (sqStep o) (.nonzero .t1)))

/-- `[R] = [z]^(2²²³ - 1)` and `[T6] = [z]^(2²²² - 1)`, through `T0`–`T5`:
what the inversion and Ed448's square root share. -/
def chain223 (z : Nat) : Prog isa :=
  .seq (sqn T0 z 1) <| .seq (mul T0 T0 z) <|          -- z^(2^2 - 1)
  .seq (sqn T1 T0 2) <| .seq (mul T1 T1 T0) <|        -- z^(2^4 - 1)
  .seq (sqn T2 T1 4) <| .seq (mul T2 T2 T1) <|        -- z^(2^8 - 1)
  .seq (sqn T3 T2 8) <| .seq (mul T3 T3 T2) <|        -- z^(2^16 - 1)
  .seq (sqn T4 T3 16) <| .seq (mul T4 T4 T3) <|       -- z^(2^32 - 1)
  .seq (sqn T5 T4 32) <| .seq (mul T5 T5 T4) <|       -- z^(2^64 - 1)
  .seq (sqn T6 T5 64) <| .seq (mul T6 T6 T5) <|       -- z^(2^128 - 1)
  .seq (sqn T6 T6 64) <| .seq (mul T6 T6 T5) <|       -- z^(2^192 - 1)
  .seq (sqn T6 T6 16) <| .seq (mul T6 T6 T3) <|       -- z^(2^208 - 1)
  .seq (sqn T6 T6 8) <| .seq (mul T6 T6 T2) <|        -- z^(2^216 - 1)
  .seq (sqn T6 T6 4) <| .seq (mul T6 T6 T1) <|        -- z^(2^220 - 1)
  .seq (sqn T6 T6 2) <| .seq (mul T6 T6 T0) <|        -- z^(2^222 - 1)
  .seq (sqn R T6 1) (mul R R z)                       -- z^(2^223 - 1)

/-- From `chain223 Z2`: `[R] = [Z2]^(p - 2)`. -/
def invTail : Prog isa :=
  .seq (sqn R R 225) <| .seq (sqn T6 T6 2) <| .seq (mul T6 T6 Z2) (mul R R T6)

/-- `[R] = [Z2]^(p-2)`. -/
def invert : Prog isa := .seq (chain223 Z2) invTail

/-- What follows the setup. -/
def tail : Prog isa :=
  .seq bits <| .seq ladder <| .seq (.block lastSwap) <| .seq invert <| .seq (mul X2 X2 R) (.block freeze)

/-- Both entry points call the same ladder and inversion. The last doubleword
of the aligned 2048-byte working area holds the caller's return address;
the tail's field area and scalar bits end before it. No stack is used. -/
def tailCall : Prog isa :=
  .seq (.block [.store .d .ra .a3 2040])
    (.seq (.call "vg_x448_tail" tail) (.block [.load .d .ra .a3 2040]))

def x448 : Prog isa := .seq (.block (align ++ setup)) tailCall

/-- `vg_x448_base(out = a0, scalar = a1, scratch = a2)`: the working space into
`a3`, as `vg_x448` has it, and `vg_x448` with the base point's u-coordinate, 5,
written instead of read (`setupBase`). -/
def x448Base : Prog isa := .seq (.block ([.addi .a3 .a2 0] ++ align ++ setupBase)) tailCall

end VG.Impl.X448.RISCV64.R64
