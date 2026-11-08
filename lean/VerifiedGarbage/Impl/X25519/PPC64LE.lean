module

public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# X25519: PPC64LE implementation

`vg_x25519(out = r3, scalar = r4, point = r5, scratch = r6)`.

The ARMv7 implementation's algorithm (`Impl/X25519/Arm.lean`), in 64-bit
registers. A field element is 32 bytes in the working space: eight 32-bit
limbs `x0 + 2³² x1 + … + 2²²⁴ x7`, which the additions, subtractions, swaps
and final reduction use (a product of two limbs and two more limbs fits in
64 bits), and, the same number, four 64-bit words
`w0 + 2⁶⁴ w1 + 2¹²⁸ w2 + 2¹⁹² w3`, which the multiplication uses (`mulld`
and `mulhdu` give the low and high words of a product of words, and `addc`,
`adde` and `addze` add with XER's carry CA). Every element is any number
below `2²⁵⁶`, standing for its residue modulo `p = 2²⁵⁵ - 19`; only the
result is reduced fully. A limb is stored with `stw`, which keeps the low
32 bits of a sum, and the carry is the sum shifted right by 32. Every element
lives in the working space, at a constant offset from its base, which stays
in `r6` (`out` stays in `r3`):

* `x1, x2, z2, x3, z3`, the ladder's temporaries, the inversion's result
  and the final reduction's temporary, 32 bytes each (`X1`, …);
* the 8 words of a product (`ACC`, 64 bytes) and the bits of the scalar
  (`BITS`, byte `t` is bit `t` of the clamped scalar).

The arithmetic (registers `r4`, `r5`, `r7`–`r11`):

* `pass`: the limbs of a number from eight sums `c_k` (below `2⁶⁴` less a
  carry), limb `k` being `c_k` plus the carry from limb `k - 1`, modulo
  `2³²`, and the carry out in `r8`;
* `mul`: the eight words of the product by columns (product scanning: the
  terms `a_i b_j` of column `k = i + j` added into a three-word accumulator,
  `r8`–`r10` in turn, whose low word is stored when the column ends), then
  `L + 38 H` for its halves `L` and `H` in four words `r8`–`r11` and a top
  word `t < 40` (`r7`), folded in as `38 t` twice (`foldTop`: the first
  carries out 0 or 1, and if 1 the words are small);
* `add`: the four words of `a + b` with the carry chain (`addc`, `adde`),
  and its carry `t ≤ 1` folded in as `38 t` twice (`foldTop`);
* `sub`: the four words of `a - b` modulo `2²⁵⁶` with the borrow chain
  (`subc`, `sube`: CA is set if there is no borrow), and 38 subtracted if it
  borrowed (`borrowFold`, by a mask from CA), twice: the second does not
  borrow;
* `cswap`: with the mask `-swap` (in `r11`), as RFC 7748 §5 describes;
* `freeze`: the full reduction of the result: bit 255 folded in as 19
  (`x < 2²⁵⁵ + 19`), then `x + 19 - 2²⁵⁵` selected with a mask if it is not
  negative.

The ladder follows RFC 7748 §5 operation by operation (with `a24 · E` a
multiplication by the word `121665`, `mulA24`), over the bits of the scalar
from 254 down to 0 (the counter `r12`, which indexes `BITS`; `swap` in `r0`).
The inversion `z2^(p-2)` is ref10's addition chain (254 squarings and 11
multiplications), its runs of squarings counted by `r12`.

The function uses only volatile registers. The only branches are on the loop
counters, and every address is a pointer plus a constant or a counter, so
only the pointers can affect timing.
-/

@[expose] public section

namespace VG.Impl.X25519.PPC64LE

open VG.PPC64LE

/-! ## The layout of the working space -/

def X1 : Nat := 0
def X2 : Nat := 32
def Z2 : Nat := 64
def X3 : Nat := 96
def Z3 : Nat := 128
def A : Nat := 160
def B : Nat := 192
def C : Nat := 224
def D : Nat := 256
def AA : Nat := 288
def BB : Nat := 320
def E : Nat := 352
def DA : Nat := 384
def CB : Nat := 416
-- 448 to 480 is unused.
def R : Nat := 480
def Y : Nat := 512
def ACC : Nat := 544
def BITS : Nat := 608

/-! ## Carrying -/

/-- A limb stored at `rb + off`: `r7 + r8` modulo `2³²`, and the carry
`(r7 + r8) >> 32` into `r8`. -/
def carryStep (rb : Reg) (off : Nat) : List Instr :=
  [.add .r7 .r7 .r8, .store .w .r7 rb off, .lsr .d .r8 .r7 32]

/-- The limbs at `rb + o` from the sums `src k` leaves in `r7` and the carry
in `r8`. -/
def pass (rb : Reg) (o : Nat) (src : Nat → List Instr) : List Instr :=
  (List.range 8).flatMap fun k => src k ++ carryStep rb (o + 4 * k)

/-- Limb `k` of `[o]`, into `r7`. -/
def ldSrc (o k : Nat) : List Instr := [.load .w .r7 .r6 (o + 4 * k)]

/-- 38 in `r10` and no carry in `r8`. -/
def prologue : List Instr := [.li .r10 38, .li .r8 0]

/-! ## Field arithmetic

Limb `k` of `[a] + [b]`, a source for `pass` (Ed25519's scalar arithmetic
on PPC64LE uses it). -/
def addSrc (a b k : Nat) : List Instr :=
  [.load .w .r7 .r6 (a + 4 * k), .load .w .r5 .r6 (b + 4 * k), .add .r7 .r7 .r5]

/-- Register `r` stored into the `n` words from `o` of the working space. -/
def storeN (r : Reg) (o n : Nat) : List Instr := (List.range n).flatMap fun k => [.store .w r .r6 (o + 4 * k)]

/-! The 16 limbs of a product, row by row, at an offset `acc` of the working space
(Ed25519's scalar arithmetic on PPC64LE uses these). -/

/-- The words `acc[0, 8)` zeroed. -/
def zeroAcc (acc : Nat) : List Instr := .li .r7 0 :: storeN .r7 acc 8

/-- Limb `j` of row `i` (`r9` = the base plus `4 i`, `a_i` in `r4`) into
`r7`: `a_i b_j + acc[i + j]`. -/
def rowSrc (acc b j : Nat) : List Instr :=
  [.load .w .r5 .r6 (b + 4 * j), .mul .r5 .r4 .r5, .load .w .r7 .r9 (acc + 4 * j), .add .r7 .r7 .r5]

/-- Row `i` of the product: `acc[i, i + 9) = acc[i, i + 8) + a_i · b`. -/
def row (acc a b : Nat) : List Instr :=
  [.load .w .r4 .r9 a, .li .r8 0] ++ pass .r9 acc (rowSrc acc b) ++
    [.store .w .r8 .r9 (acc + 32), .addi .r9 .r9 4, .subi .r11 .r11 1]

/-! The product is eight doublewords at an offset `acc` of the working space
(X25519's `ACC`; Ed25519 on PPC64LE uses the same code with its own): a
field element's 32 bytes, eight 32-bit limbs, are also four 64-bit words
`x₀ + 2⁶⁴ x₁ + 2¹²⁸ x₂ + 2¹⁹² x₃`, which the multiplication loads with `ld`
(so every offset is a multiple of 4). -/

/-- The accumulator of column `k` of a product is `rr k, rr (k + 1),
rr (k + 2)`: `r8`, `r9` and `r10` in turn. -/
def rr (k : Nat) : Reg := if k % 3 = 0 then .r8 else if k % 3 = 1 then .r9 else .r10

/-- The terms `(i, j)` of column `k` of a product of four words, `i`
descending. -/
def colPairs (k : Nat) : List (Nat × Nat) :=
  ((List.range 4).reverse.filter fun i => i ≤ k ∧ k - i < 4).map fun i => (i, k - i)

/-- A term `a_i b_j` of column `k`, both loaded (into `r4` and `r5`), added
to the accumulator: the low word of the product (`mulld`, into `r7`) with
`addc`, the high word (`mulhdu`, into `r4`) with `adde`, and the carry into
the top word with `addze`. -/
def mulTerm (a b k : Nat) (p : Nat × Nat) : List Instr :=
  [.load .d .r4 .r6 (a + 8 * p.1), .load .d .r5 .r6 (b + 8 * p.2), .mul .r7 .r4 .r5,
    .mulhu .r4 .r4 .r5, .addc (rr k) (rr k) .r7, .adde (rr (k + 1)) (rr (k + 1)) .r4,
    .addze (rr (k + 2)) (rr (k + 2))]

/-- The end of column `k`: its low word stored at `acc + 8k`, and the
register zeroed, which becomes the top word of column `k + 1`'s accumulator. -/
def colEnd (acc k : Nat) : List Instr := [.store .d (rr k) .r6 (acc + 8 * k), .li (rr k) 0]

/-- Column `k` of `[a] · [b]`. -/
def mulCol (acc a b k : Nat) : List Instr := (colPairs k).flatMap (mulTerm a b k) ++ colEnd acc k

/-- The eight words of `[a] · [b]` at `acc`, by columns (product scanning). -/
def product (acc a b : Nat) : List Instr :=
  [.li .r8 0, .li .r9 0, .li .r10 0] ++ (List.range 8).flatMap (mulCol acc a b)

/-- Word `k` of the reduced product, in `r8`–`r11`. -/
def wreg (k : Nat) : Reg := if k = 0 then .r8 else if k = 1 then .r9 else if k = 2 then .r10 else .r11

/-- Word `k` of `L + lo(38 H)` (`L`, `H` the halves of the product at `acc`;
38 in `r5`) into `wreg k`, with the carry chain. -/
def redLo (acc k : Nat) : List Instr :=
  [.load .d (wreg k) .r6 (acc + 8 * k), .load .d .r4 .r6 (acc + 32 + 8 * k), .mul .r4 .r4 .r5,
    if k = 0 then .addc (wreg k) (wreg k) .r4 else .adde (wreg k) (wreg k) .r4]

/-- The high word of `38 H_k` added into word `k + 1` (into `r7`, the top
word, for `k = 3`), with the carry chain. -/
def redHi (acc k : Nat) : List Instr :=
  [.load .d .r4 .r6 (acc + 32 + 8 * k), .mulhu .r4 .r4 .r5,
    if k = 0 then .addc (wreg 1) (wreg 1) .r4 else if k = 3 then .adde .r7 .r7 .r4
    else .adde (wreg (k + 1)) (wreg (k + 1)) .r4]

/-- `r8`–`r11` plus `38 t` (`t` in `r7`, 38 in `r5`), the carry out into `r7`. -/
def foldTop : List Instr :=
  [.mul .r4 .r7 .r5, .addc .r8 .r8 .r4, .addze .r9 .r9, .addze .r10 .r10, .addze .r11 .r11,
    .li .r7 0, .addze .r7 .r7]

/-- The product at `acc` reduced into `[o]`: `L + 38 H` (`2²⁵⁶ ≡ 38`) in four
words and a top word below 40, which is folded in as `38 t` twice. -/
def reduce38 (acc o : Nat) : List Instr :=
  .li .r5 38 :: (List.range 4).flatMap (redLo acc) ++ [.li .r7 0, .addze .r7 .r7] ++
    (List.range 4).flatMap (redHi acc) ++ foldTop ++ foldTop ++
    (List.range 4).map fun k => .store .d (wreg k) .r6 (o + 8 * k)

/-- Word `k` of `[a] + [b]` into `wreg k`, with the carry chain. -/
def addW (a b k : Nat) : List Instr :=
  [.load .d (wreg k) .r6 (a + 8 * k), .load .d .r4 .r6 (b + 8 * k),
    if k = 0 then .addc (wreg k) (wreg k) .r4 else .adde (wreg k) (wreg k) .r4]

/-- The four words of `r8`–`r11` stored at `o`. -/
def stores4 (o : Nat) : List Instr := (List.range 4).map fun k => .store .d (wreg k) .r6 (o + 8 * k)

/-- `[o] = [a] + [b]` (`o` may be `a` or `b`): the four words of the sum and
its carry `t ≤ 1` (in `r7`), folded in as `38 t` twice. -/
def add (o a b : Nat) : List Instr :=
  (List.range 4).flatMap (addW a b) ++ [.li .r7 0, .addze .r7 .r7, .li .r5 38] ++ foldTop ++
    foldTop ++ stores4 o

/-- Word `k` of `[a] - [b]` into `wreg k`, with the borrow chain (CA set if
there is no borrow). -/
def subW (a b k : Nat) : List Instr :=
  [.load .d (wreg k) .r6 (a + 8 * k), .load .d .r4 .r6 (b + 8 * k),
    if k = 0 then .subc (wreg k) (wreg k) .r4 else .sube (wreg k) (wreg k) .r4]

/-- `r8`–`r11` less 38 if the last subtraction borrowed (`2²⁵⁶ ≡ 38`; 38 in
`r5`): the mask `CA - 1` into `r7`, `38` masked into `r4`, then the borrow
chain against `r7 = 0`. -/
def borrowFold : List Instr :=
  [.sube .r7 .r7 .r7, .logic .and .r4 .r7 .r5, .li .r7 0, .subc .r8 .r8 .r4, .sube .r9 .r9 .r7,
    .sube .r10 .r10 .r7, .sube .r11 .r11 .r7]

/-- `[o] = [a] - [b]` (`o` may be `a` or `b`): the four words of the
difference modulo `2²⁵⁶`, less 38 if it borrowed, twice (the second does not
borrow). -/
def sub (o a b : Nat) : List Instr :=
  (List.range 4).flatMap (subW a b) ++ [.li .r5 38] ++ borrowFold ++ borrowFold ++ stores4 o

/-- `121665 = 2¹⁶ + 0xdb41` (`a24`) into `r5`. -/
def a24Const : List Instr := [.lis .r5 1, .ori .r5 .r5 0xdb41]

/-- `[o] = 121665 · [a]` (`a24 · [a]`; `o` may be `a`): the words of the
product, each `mulld` plus the previous `mulhdu` by the carry chain, and its
top word `t < 2¹⁷` (in `r7`), folded in as `38 t` twice. -/
def mulA24 (o a : Nat) : List Instr :=
  a24Const ++
  [.load .d .r8 .r6 a, .mulhu .r7 .r8 .r5, .mul .r8 .r8 .r5,
    .load .d .r9 .r6 (a + 8), .mulhu .r4 .r9 .r5, .mul .r9 .r9 .r5, .addc .r9 .r9 .r7,
    .load .d .r10 .r6 (a + 16), .mulhu .r7 .r10 .r5, .mul .r10 .r10 .r5, .adde .r10 .r10 .r4,
    .load .d .r11 .r6 (a + 24), .mulhu .r4 .r11 .r5, .mul .r11 .r11 .r5, .adde .r11 .r11 .r7,
    .addze .r7 .r4, .li .r5 38] ++ foldTop ++ foldTop ++ stores4 o

/-- `[o] = [a] · [b]` (`o` may be `a` or `b`), with the product at `acc`. -/
def mulAt (acc o a b : Nat) : Prog isa := .block (product acc a b ++ reduce38 acc o)

/-- `[o] = [a] · [b]`, with the product in `ACC`. -/
abbrev mul (o a b : Nat) : Prog isa := mulAt ACC o a b

/-- Swaps limb `k` of `[x]` and `[y]` if the mask `r11` is all ones (and not
if it is zero): `d = r11 ∧ (x ⊕ y)`, `x ⊕= d`, `y ⊕= d`. -/
def cswapStep (x y k : Nat) : List Instr :=
  [.load .w .r5 .r6 (x + 4 * k), .load .w .r7 .r6 (y + 4 * k), .logic .xor .r8 .r5 .r7,
    .logic .and .r8 .r8 .r11, .logic .xor .r5 .r5 .r8, .logic .xor .r7 .r7 .r8,
    .store .w .r5 .r6 (x + 4 * k), .store .w .r7 .r6 (y + 4 * k)]

def cswap (x y : Nat) : List Instr := (List.range 8).flatMap (cswapStep x y)

/-! ## The ladder -/

/-- The mask `-swap` into `r11`. -/
def mask : List Instr := [.li .r11 0, .sub .r11 .r11 .r0]

/-- The start of an iteration of the ladder, for the bit `t = r12 - 1`: `k_t`
from `BITS`, `swap ^= k_t`, the swaps by the mask `-swap`, and `swap = k_t`. -/
def stepHead : List Instr :=
  [.subi .r12 .r12 1, .add .r4 .r6 .r12, .lbz .r4 .r4 BITS, .logic .xor .r0 .r0 .r4] ++ mask ++
    cswap X2 X3 ++ cswap Z2 Z3 ++ [.addi .r0 .r4 0]

/-- One iteration of the ladder: `stepHead`, then the formulas of RFC 7748 §5
in order. -/
def step : Prog isa :=
  .seq (.block stepHead) <|
  .seq (.block (add A X2 Z2)) <| .seq (mul AA A A) <| .seq (.block (sub B X2 Z2)) <|
  .seq (mul BB B B) <| .seq (.block (sub E AA BB)) <| .seq (.block (add C X3 Z3)) <|
  .seq (.block (sub D X3 Z3)) <| .seq (mul DA D A) <| .seq (mul CB C B) <|
  .seq (.block (add X3 DA CB)) <| .seq (mul X3 X3 X3) <| .seq (.block (sub Z3 DA CB)) <|
  .seq (mul Z3 Z3 Z3) <| .seq (mul Z3 X1 Z3) <| .seq (mul X2 AA BB) <| .seq (.block (mulA24 Z2 E)) <|
  .seq (.block (add Z2 AA Z2)) <| .seq (mul Z2 E Z2) (.block [])

/-- The 255 iterations, for `t` from 254 down to 0, with `swap = 0`. -/
def ladder : Prog isa :=
  .seq (.block [.li .r12 255, .li .r0 0]) (.loop step (.nonzero .d .r12))

/-- The swap after the loop. -/
def lastSwap : List Instr := mask ++ cswap X2 X3 ++ cswap Z2 Z3

/-! ## Inversion

`[R] = [Z2]^(p-2)` by ref10's addition chain (254 squarings and 11
multiplications; `Proof/X25519/Chain250.lean`'s `chainF`, then five squarings
and `z^11`), in the ladder's temporaries `A`–`D`, free after it; each run of
squarings after the first is a loop counted by `r12`, the ladder's counter. -/

/-- `[a]` squared `n` times into `[o]`, the squarings after the first in a
loop counted by `r12`. -/
def sqn (o a n : Nat) : Prog isa :=
  .seq (mul o a a) <| .seq (.block [.li .r12 (n - 1)]) <|
    .loop (.seq (mul o o o) (.block [.subi .r12 .r12 1])) (.nonzero .d .r12)

def invert : Prog isa :=
  .seq (mul A Z2 Z2) <| .seq (mul B A A) <| .seq (mul B B B) <| .seq (mul B Z2 B) <|
  .seq (mul A A B) <| .seq (mul C A A) <| .seq (mul B B C) <|
  .seq (sqn C B 5) <| .seq (mul B C B) <|
  .seq (sqn C B 10) <| .seq (mul C C B) <|
  .seq (sqn D C 20) <| .seq (mul C D C) <|
  .seq (sqn C C 10) <| .seq (mul B C B) <|
  .seq (sqn C B 50) <| .seq (mul C C B) <|
  .seq (sqn D C 100) <| .seq (mul C D C) <|
  .seq (sqn C C 50) <| .seq (mul B C B) <|
  .seq (sqn B B 5) (mul R B A)

/-! ## Encoding and decoding -/

/-- `r7` modulo `2³¹` (for `r7` below `2⁶⁴`). -/
def low31 : List Instr := [.lsl .r7 .r7 33, .lsr .d .r7 .r7 33]

/-- Bit 255 of `[x]` cleared, and 19 times it into `r8`. -/
def freezeAAt (x : Nat) : List Instr :=
  [.load .w .r7 .r6 (x + 28), .lsr .d .r8 .r7 31] ++ low31 ++
  [.store .w .r7 .r6 (x + 28), .li .r5 19, .mul .r8 .r8 .r5]

/-- The mask `-(bit 255 of [y])` into `r11`, and bit 255 of `[y]` cleared. -/
def freezeBAt (y : Nat) : List Instr :=
  [.load .w .r7 .r6 (y + 28), .lsr .d .r11 .r7 31, .li .r4 0, .sub .r11 .r4 .r11] ++ low31 ++
    [.store .w .r7 .r6 (y + 28)]

abbrev freezeA : List Instr := freezeAAt X2
abbrev freezeB : List Instr := freezeBAt Y

/-- Limb `k` of `[X2]`, or of `[Y]` if the mask `r11` is all ones, as word
`k` of `out` (`r3`). -/
def outStep (k : Nat) : List Instr :=
  [.load .w .r5 .r6 (X2 + 4 * k), .load .w .r7 .r6 (Y + 4 * k), .logic .xor .r7 .r7 .r5,
    .logic .and .r7 .r7 .r11, .logic .xor .r5 .r5 .r7, .store .w .r5 .r3 (4 * k)]

/-- `[X2]` reduced fully, into `out` (`r3`): bit 255 folded in as 19, then
`y = x + 19` into `Y`, and `y - 2²⁵⁵` selected (with the mask `r11`) if
bit 255 of `y` is set. -/
def freeze : List Instr :=
  freezeA ++ pass .r6 X2 (ldSrc X2) ++ [.li .r8 19] ++ pass .r6 Y (ldSrc X2) ++ freezeB ++
    (List.range 8).flatMap outStep

/-- Limb `k` of `u` (word `k` at `r5`, the top bit masked) into `X1` and
`X3`. -/
def decodeStep (k : Nat) : List Instr :=
  [.load .w .r7 .r5 (4 * k)] ++ (if k = 7 then low31 else []) ++
    [.store .w .r7 .r6 (X1 + 4 * k), .store .w .r7 .r6 (X3 + 4 * k)]

/-- `x2 = 1`, `z2 = 0` and `z3 = 1`. -/
def consts : List Instr :=
  [.li .r7 1, .li .r8 0, .store .w .r7 .r6 X2, .store .w .r8 .r6 Z2, .store .w .r7 .r6 Z3] ++
  storeN .r8 (X2 + 4) 7 ++ storeN .r8 (Z2 + 4) 7 ++ storeN .r8 (Z3 + 4) 7

/-- The u-coordinate into `X1` and `X3`, and the constants. -/
def setup : List Instr := (List.range 8).flatMap decodeStep ++ consts

/-- The bits of the byte at `r4` into `BITS` at `r9`, advancing both. -/
def bitsBody : List Instr :=
  [.lbz .r7 .r4 0] ++
  (List.range 8).flatMap (fun j => [.lsl .r8 .r7 (63 - j), .lsr .d .r8 .r8 63, .stb .r8 .r9 (BITS + j)]) ++
  [.addi .r4 .r4 1, .addi .r9 .r9 8, .subi .r11 .r11 1]

/-- `BITS[8i + j] = bit j of scalar[i]`, then the clamping: bits 0, 1 and 2
cleared and bit 254 set. -/
def bits : Prog isa :=
  .seq (.block [.addi .r9 .r6 0, .li .r11 32])
    (.seq (.loop (.block bitsBody) (.nonzero .d .r11))
      (.block [.li .r7 0, .stb .r7 .r6 BITS, .stb .r7 .r6 (BITS + 1), .stb .r7 .r6 (BITS + 2),
        .li .r7 1, .stb .r7 .r6 (BITS + 254)]))

def x25519 : Prog isa :=
  .seq (.block setup) <| .seq bits <| .seq ladder <| .seq (.block lastSwap) <|
    .seq invert <| .seq (mul X2 X2 R) (.block freeze)

end VG.Impl.X25519.PPC64LE
