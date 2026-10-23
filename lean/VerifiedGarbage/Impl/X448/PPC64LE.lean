module

public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# X448: PPC64LE implementation

`vg_x448(out = r3, scalar = r4, point = r5, scratch = r6)`.

X25519's PPC64LE implementation (`Impl/X25519/PPC64LE.lean`) for curve448's
field, `p = 2⁴⁴⁸ - 2²²⁴ - 1`: a field element is fourteen 32-bit limbs
`x0 + 2³² x1 + … + 2⁴¹⁶ x13`, each in a word of the working space, any
number below `2⁴⁴⁸` standing for its residue modulo `p`; only the result is
reduced fully. Every element lives in the working space at a constant offset
from its base, which stays in `r6` (`out` stays in `r3`):

* `x1, x2, z2, x3, z3`, the ladder's temporaries, the constant `a24`, the
  inversion's result and the final reduction's temporary, 56 bytes each
  (`X1`, …);
* the 28 limbs of a product (`ACC`, 112 bytes) and the bits of the scalar
  (`BITS`, byte `t` is bit `t` of the clamped scalar).

The arithmetic (registers `r4`, `r5`, `r7`–`r11`), with `2⁴⁴⁸ ≡ 2²²⁴ + 1`:

* `pass`: the limbs of a number from fourteen sums `c_k` (below `2⁶⁴` less a
  carry), limb `k` being `c_k` plus the carry from limb `k - 1`, modulo
  `2³²`, and the carry out in `r8`;
* `fold`: the carry out `c` folded in as `c + 2²²⁴ c`: added to limbs 0 and
  7 and carried again; `tail` folds twice, after which nothing carries out;
* `mul`: the 28 limbs of the product row by row (Knuth's algorithm M), then,
  for `lo + 2⁴⁴⁸ hi ≡ lo + hi + 2²²⁴ hi`, with `2²²⁴ hi`'s upper half folded
  once more, limb `k` of `lo + hi + hi_{k+7}` (`k < 7`) and of
  `lo + 2 hi + hi_{k-7}` (`k ≥ 7`) (`pass`), then `tail`;
* `add`, `sub`: the limbs of `a + b` and of `a + 4p - b` (every limb of `4p`
  is `2³⁴ - 4`, but limb 7's, `2³⁴ - 8`, so no limb is negative; `r4` holds
  `2³⁴`), then `tail`;
* `cswap`: with the mask `-swap` (in `r11`), as RFC 7748 §5 describes;
* `freeze`: the full reduction of the result: `y = x + 2²²⁴ + 1` carries out
  exactly when `x ≥ p` (`x < 2⁴⁴⁸`), and is then `x - p` modulo `2⁴⁴⁸`,
  selected with a mask.

The ladder follows RFC 7748 §5 operation by operation (with `a24 · E` a
multiplication by the constant element `A24`), over the bits of the scalar
from 447 down to 0 (the counter `r12`, which indexes `BITS`; `swap` in `r0`).
The inversion `z2^(p-2)` is square-and-multiply over the bits of `p - 2 =
2⁴⁴⁸ - 2²²⁴ - 3` from 447 down to 0 (the counter `r12`): every bit but 224
and 1 is 1.

The function uses only volatile registers. The only branches are on the loop
counters, and every address is a pointer plus a constant or a counter, so
only the pointers can affect timing.
-/

@[expose] public section

namespace VG.Impl.X448.PPC64LE

open VG.PPC64LE

/-! ## The layout of the working space -/

def X1 : Nat := 0
def X2 : Nat := 56
def Z2 : Nat := 112
def X3 : Nat := 168
def Z3 : Nat := 224
def A : Nat := 280
def B : Nat := 336
def C : Nat := 392
def D : Nat := 448
def AA : Nat := 504
def BB : Nat := 560
def E : Nat := 616
def DA : Nat := 672
def CB : Nat := 728
def A24 : Nat := 784
def R : Nat := 840
def Y : Nat := 896
def ACC : Nat := 952
def BITS : Nat := 1064

/-! ## Carrying -/

/-- A limb stored at `rb + off`: `r7 + r8` modulo `2³²`, and the carry
`(r7 + r8) >> 32` into `r8`. -/
def carryStep (rb : Reg) (off : Nat) : List Instr :=
  [.add .r7 .r7 .r8, .store .w .r7 rb off, .lsr .d .r8 .r7 32]

/-- The limbs at `rb + o` from the sums `src k` leaves in `r7` and the carry
in `r8`. -/
def pass (rb : Reg) (o : Nat) (src : Nat → List Instr) : List Instr :=
  (List.range 14).flatMap fun k => src k ++ carryStep rb (o + 4 * k)

/-- Limb `k` of `[o]`, into `r7`. -/
def ldSrc (o k : Nat) : List Instr := [.load .w .r7 .r6 (o + 4 * k)]

/-- Limb `k` of `[o]`, with the carry folded in kept in `r10` added to limb 7, into `r7`. -/
def foldSrc (o k : Nat) : List Instr := ldSrc o k ++ (if k = 7 then [.add .r7 .r7 .r10] else [])

/-- The carry out of `[o]`, in `r8`, folded in as `r8 + 2²²⁴ r8`. -/
def fold (o : Nat) : List Instr := .addi .r10 .r8 0 :: pass .r6 o (foldSrc o)

/-- The carry out folded in twice. -/
def tail (o : Nat) : List Instr := fold o ++ fold o

/-! ## Field arithmetic -/

def addSrc (a b k : Nat) : List Instr :=
  [.load .w .r7 .r6 (a + 4 * k), .load .w .r5 .r6 (b + 4 * k), .add .r7 .r7 .r5]

/-- `[o] = [a] + [b]`. -/
def add (o a b : Nat) : List Instr := .li .r8 0 :: pass .r6 o (addSrc a b) ++ tail o

/-- Limb `k` of `4p` is `2³⁴` less `subLo k`. -/
def subLo (k : Nat) : Nat := if k = 7 then 8 else 4

def subSrc (a b k : Nat) : List Instr :=
  [.load .w .r7 .r6 (a + 4 * k), .add .r7 .r7 .r4, .subi .r7 .r7 (subLo k), .load .w .r5 .r6 (b + 4 * k),
    .sub .r7 .r7 .r5]

/-- `[o] = [a] - [b]`, as `[a] + 4p - [b]`. -/
def sub (o a b : Nat) : List Instr :=
  [.li .r8 0, .li .r4 1, .lsl .r4 .r4 34] ++ pass .r6 o (subSrc a b) ++ tail o

/-- Register `r` stored into the `n` words from `o` of the working space. -/
def storeN (r : Reg) (o n : Nat) : List Instr := (List.range n).flatMap fun k => [.store .w r .r6 (o + 4 * k)]

/-- The words `ACC[0, 14)` zeroed. -/
def zeroAcc : List Instr := .li .r7 0 :: storeN .r7 ACC 14

/-- Limb `j` of row `i` (`r9` = the base plus `4 i`, `a_i` in `r4`) into
`r7`: `a_i b_j + acc[i + j]`. -/
def rowSrc (b j : Nat) : List Instr :=
  [.load .w .r5 .r6 (b + 4 * j), .mul .r5 .r4 .r5, .load .w .r7 .r9 (ACC + 4 * j), .add .r7 .r7 .r5]

/-- Row `i` of the product: `acc[i, i + 15) = acc[i, i + 14) + a_i · b`. -/
def row (a b : Nat) : List Instr :=
  [.load .w .r4 .r9 a, .li .r8 0] ++ pass .r9 ACC (rowSrc b) ++
    [.store .w .r8 .r9 (ACC + 56), .addi .r9 .r9 4, .subi .r11 .r11 1]

/-- Limb `k` of `lo + hi + 2²²⁴ hi`, with `2²²⁴ hi`'s upper half folded once more, into `r7`. -/
def mulSrc (k : Nat) : List Instr :=
  [.load .w .r7 .r6 (ACC + 4 * k), .load .w .r5 .r6 (ACC + 56 + 4 * k), .add .r7 .r7 .r5] ++
  (if k < 7 then [.load .w .r5 .r6 (ACC + 56 + 4 * (k + 7)), .add .r7 .r7 .r5]
   else [.add .r7 .r7 .r5, .load .w .r5 .r6 (ACC + 56 + 4 * (k - 7)), .add .r7 .r7 .r5])

/-- `[o] = [a] · [b]` (`o` may be `a` or `b`), with the product in `ACC`. -/
def mul (o a b : Nat) : Prog isa :=
  .seq (.block (zeroAcc ++ [.addi .r9 .r6 0, .li .r11 14]))
    (.seq (.loop (.block (row a b)) (.nonzero .d .r11))
      (.block (.li .r8 0 :: pass .r6 o mulSrc ++ tail o)))

/-- Swaps limb `k` of `[x]` and `[y]` if the mask `r11` is all ones (and not
if it is zero): `d = r11 ∧ (x ⊕ y)`, `x ⊕= d`, `y ⊕= d`. -/
def cswapStep (x y k : Nat) : List Instr :=
  [.load .w .r5 .r6 (x + 4 * k), .load .w .r7 .r6 (y + 4 * k), .logic .xor .r8 .r5 .r7,
    .logic .and .r8 .r8 .r11, .logic .xor .r5 .r5 .r8, .logic .xor .r7 .r7 .r8,
    .store .w .r5 .r6 (x + 4 * k), .store .w .r7 .r6 (y + 4 * k)]

def cswap (x y : Nat) : List Instr := (List.range 14).flatMap (cswapStep x y)

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
  .seq (mul Z3 Z3 Z3) <| .seq (mul Z3 X1 Z3) <| .seq (mul X2 AA BB) <| .seq (mul Z2 A24 E) <|
  .seq (.block (add Z2 AA Z2)) <| .seq (mul Z2 E Z2) (.block [])

/-- The 448 iterations, for `t` from 447 down to 0, with `swap = 0`. -/
def ladder : Prog isa :=
  .seq (.block [.li .r12 448, .li .r0 0]) (.loop step (.nonzero .d .r12))

/-- The swap after the loop. -/
def lastSwap : List Instr := mask ++ cswap X2 X3 ++ cswap Z2 Z3

/-! ## Inversion

`[R] = [Z2]^(p-2)`, square-and-multiply over the bits of `p - 2` from 447
down to 0 (`t = r12 - 1`): `R = R²`, then `R = R · Z2` unless `t` is 224 or 1. -/

/-- `[R] = 1`. -/
def one : List Instr :=
  [.li .r4 1, .li .r5 0, .store .w .r4 .r6 R] ++ storeN .r5 (R + 4) 13

def invStep : Prog isa :=
  .seq (.block [.subi .r12 .r12 1]) <| .seq (mul R R R) <|
  .seq (.block [.subi .r5 .r12 224]) <|
  .seq (.ite (.zero .d .r5) (.block [])
    (.seq (.block [.subi .r5 .r12 1]) (.ite (.zero .d .r5) (.block []) (mul R R Z2))))
    (.block [])

def invert : Prog isa := .seq (.block (one ++ [.li .r12 448])) (.loop invStep (.nonzero .d .r12))

/-! ## Encoding and decoding -/

/-- Limb `k` of `[X2]`, or of `[Y]` if the mask `r11` is all ones, as word
`k` of `out` (`r3`). -/
def outStep (k : Nat) : List Instr :=
  [.load .w .r5 .r6 (X2 + 4 * k), .load .w .r7 .r6 (Y + 4 * k), .logic .xor .r7 .r7 .r5,
    .logic .and .r7 .r7 .r11, .logic .xor .r5 .r5 .r7, .store .w .r5 .r3 (4 * k)]

/-- `[X2]` reduced fully, into `out` (`r3`): `y = x + 2²²⁴ + 1` into `Y`
(the carry into limb 0, `r10` = 1 into limb 7), and `y` selected (with the
mask `r11 = -carry`) if it carries out. -/
def freeze : List Instr :=
  [.li .r8 1, .li .r10 1] ++ pass .r6 Y (foldSrc X2) ++ [.li .r4 0, .sub .r11 .r4 .r8] ++
    (List.range 14).flatMap outStep

/-- Limb `k` of `u` (word `k` at `r5`) into `X1` and `X3`. -/
def decodeStep (k : Nat) : List Instr :=
  [.load .w .r7 .r5 (4 * k), .store .w .r7 .r6 (X1 + 4 * k), .store .w .r7 .r6 (X3 + 4 * k)]

/-- `x2 = 1`, `z2 = 0`, `z3 = 1` and `A24 = 39081 = 0x98a9`. -/
def consts : List Instr :=
  [.li .r7 1, .li .r8 0, .li .r5 0, .ori .r5 .r5 0x98a9, .store .w .r7 .r6 X2,
    .store .w .r8 .r6 Z2, .store .w .r7 .r6 Z3, .store .w .r5 .r6 A24] ++
  storeN .r8 (X2 + 4) 13 ++ storeN .r8 (Z2 + 4) 13 ++ storeN .r8 (Z3 + 4) 13 ++ storeN .r8 (A24 + 4) 13

/-- The u-coordinate into `X1` and `X3`, and the constants. -/
def setup : List Instr := (List.range 14).flatMap decodeStep ++ consts

/-- The bits of the byte at `r4` into `BITS` at `r9`, advancing both. -/
def bitsBody : List Instr :=
  [.lbz .r7 .r4 0] ++
  (List.range 8).flatMap (fun j => [.lsl .r8 .r7 (63 - j), .lsr .d .r8 .r8 63, .stb .r8 .r9 (BITS + j)]) ++
  [.addi .r4 .r4 1, .addi .r9 .r9 8, .subi .r11 .r11 1]

/-- `BITS[8i + j] = bit j of scalar[i]`, then the clamping: bits 0 and 1
cleared and bit 447 set. -/
def bits : Prog isa :=
  .seq (.block [.addi .r9 .r6 0, .li .r11 56])
    (.seq (.loop (.block bitsBody) (.nonzero .d .r11))
      (.block [.li .r7 0, .stb .r7 .r6 BITS, .stb .r7 .r6 (BITS + 1), .li .r7 1, .stb .r7 .r6 (BITS + 447)]))

def x448 : Prog isa :=
  .seq (.block setup) <| .seq bits <| .seq ladder <| .seq (.block lastSwap) <|
    .seq invert <| .seq (mul X2 X2 R) (.block freeze)

end VG.Impl.X448.PPC64LE
