module

public import VerifiedGarbage.TCB.RISCV64.Isa
public import VerifiedGarbage.Impl.Words.RISCV64

/-!
# X448: RISC-V implementation

`vg_x448(out = a0, scalar = a1, point = a2, scratch = a3)`.

The PPC64LE implementation's algorithm (`Impl/X448/PPC64LE.lean`), register
for register (`r3`–`r12` and `r0` are `a0`–`a7`, `t0`, `t1` and `t2`, as in
`Impl/X25519/RISCV64.lean`), with RV64IM's `mul` (the low 64 bits of a
product) for `mulld`. A field element is fourteen 32-bit limbs
`x0 + 2³² x1 + … + 2⁴¹⁶ x13`, each in a word of the working space, any number
below `2⁴⁴⁸` standing for its residue modulo `p = 2⁴⁴⁸ - 2²²⁴ - 1`; only the
result is reduced fully. A limb is stored with `sw`, which keeps the low 32
bits of a sum, and the carry is the sum shifted right by 32.

RISC-V faults on a misaligned access. The working space is rounded up to a
multiple of 8 (`align`), as X25519's is, and the u-coordinate and the result,
whose contract states no alignment, are loaded and stored a byte at a time
(`loadLE32`, `storeLE32`). Every element lives in the working space, at a
constant offset from its rounded base, which stays in `a3` (`out` stays in
`a0`):

* `x1, x2, z2, x3, z3`, the ladder's temporaries, the constant `a24`, the
  inversion's result and the final reduction's temporary, 56 bytes each
  (`X1`, …);
* the 28 limbs of a product (`ACC`, 112 bytes) and the bits of the scalar
  (`BITS`, byte `t` is bit `t` of the clamped scalar).

The arithmetic (registers `a1`, `a2`, `a4`–`a7`, `t0`), with `2⁴⁴⁸ ≡ 2²²⁴ + 1`:

* `pass`: the limbs of a number from fourteen sums `c_k` (below `2⁶⁴` less a
  carry), limb `k` being `c_k` plus the carry from limb `k - 1`, modulo
  `2³²`, and the carry out in `a5`;
* `fold`: the carry out `c` folded in as `c + 2²²⁴ c`: added to limbs 0 and
  7 and carried again; `tail` folds twice, after which nothing carries out;
* `mul`: the 28 limbs of the product row by row (Knuth's algorithm M), then,
  for `lo + 2⁴⁴⁸ hi ≡ lo + hi + 2²²⁴ hi`, with `2²²⁴ hi`'s upper half folded
  once more, limb `k` of `lo + hi + hi_{k+7}` (`k < 7`) and of
  `lo + 2 hi + hi_{k-7}` (`k ≥ 7`) (`pass`), then `tail`;
* `add`, `sub`: the limbs of `a + b` and of `a + 4p - b` (every limb of `4p`
  is `2³⁴ - 4`, but limb 7's, `2³⁴ - 8`, so no limb is negative; `a1` holds
  `2³⁴`), then `tail`;
* `cswap`: with the mask `-swap` (in `t0`), as RFC 7748 §5 describes;
* `freeze`: the full reduction of the result: `y = x + 2²²⁴ + 1` carries out
  exactly when `x ≥ p` (`x < 2⁴⁴⁸`), and is then `x - p` modulo `2⁴⁴⁸`,
  selected with a mask.

The ladder follows RFC 7748 §5 operation by operation (with `a24 · E` a
multiplication by the constant element `A24`), over the bits of the scalar
from 447 down to 0 (the counter `t1`, which indexes `BITS`; `swap` in `t2`).
The inversion `z2^(p-2)` is square-and-multiply over the bits of `p - 2 =
2⁴⁴⁸ - 2²²⁴ - 3` from 447 down to 0 (the counter `t1`): every bit but 224
and 1 is 1.

The function uses only caller-saved registers and no stack. The only branches
are on the loop counters, and every address is a pointer plus a constant or a
counter, so only the pointers can affect timing.
-/

@[expose] public section

namespace VG.Impl.X448.RISCV64

open VG.RISCV64 VG.Impl.Words.RISCV64

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
`(r7 + r8) >> 32` into `a5`. -/
def carryStep (rb : Reg) (off : Nat) : List Instr :=
  [.add .a4 .a4 .a5, .store .w .a4 rb off, .shift .srl .d .a5 .a4 32]

/-- The limbs at `rb + o` from the sums `src k` leaves in `a4` and the carry
in `a5`. -/
def pass (rb : Reg) (o : Nat) (src : Nat → List Instr) : List Instr :=
  (List.range 14).flatMap fun k => src k ++ carryStep rb (o + 4 * k)

/-- Limb `k` of `[o]`, into `a4`. -/
def ldSrc (o k : Nat) : List Instr := [.load .w .a4 .a3 (o + 4 * k)]

/-- Limb `k` of `[o]`, with the carry folded in kept in `a7` added to limb 7, into `a4`. -/
def foldSrc (o k : Nat) : List Instr := ldSrc o k ++ (if k = 7 then [.add .a4 .a4 .a7] else [])

/-- The carry out of `[o]`, in `a5`, folded in as `r8 + 2²²⁴ r8`. -/
def fold (o : Nat) : List Instr := .addi .a7 .a5 0 :: pass .a3 o (foldSrc o)

/-- The carry out folded in twice. -/
def tail (o : Nat) : List Instr := fold o ++ fold o

/-! ## Field arithmetic -/

def addSrc (a b k : Nat) : List Instr :=
  [.load .w .a4 .a3 (a + 4 * k), .load .w .a2 .a3 (b + 4 * k), .add .a4 .a4 .a2]

/-- `[o] = [a] + [b]`. -/
def add (o a b : Nat) : List Instr := .li .a5 0 :: pass .a3 o (addSrc a b) ++ tail o

/-- Limb `k` of `4p` is `2³⁴` less `subLo k`. -/
def subLo (k : Nat) : Nat := if k = 7 then 8 else 4

def subSrc (a b k : Nat) : List Instr :=
  [.load .w .a4 .a3 (a + 4 * k), .add .a4 .a4 .a1, .addi .a4 .a4 (-(subLo k)), .load .w .a2 .a3 (b + 4 * k),
    .sub .a4 .a4 .a2]

/-- `[o] = [a] - [b]`, as `[a] + 4p - [b]`. -/
def sub (o a b : Nat) : List Instr :=
  [.li .a5 0, .li .a1 1, .shift .sll .d .a1 .a1 34] ++ pass .a3 o (subSrc a b) ++ tail o

/-- Register `r` stored into the `n` words from `o` of the working space. -/
def storeN (r : Reg) (o n : Nat) : List Instr := (List.range n).flatMap fun k => [.store .w r .a3 (o + 4 * k)]

/-- The words `ACC[0, 14)` zeroed. -/
def zeroAcc : List Instr := .li .a4 0 :: storeN .a4 ACC 14

/-- Limb `j` of row `i` (`a6` = the base plus `4 i`, `a_i` in `a1`) into
`a4`: `a_i b_j + acc[i + j]`. -/
def rowSrc (b j : Nat) : List Instr :=
  [.load .w .a2 .a3 (b + 4 * j), .mul .a2 .a1 .a2, .load .w .a4 .a6 (ACC + 4 * j), .add .a4 .a4 .a2]

/-- Row `i` of the product: `acc[i, i + 15) = acc[i, i + 14) + a_i · b`. -/
def row (a b : Nat) : List Instr :=
  [.load .w .a1 .a6 a, .li .a5 0] ++ pass .a6 ACC (rowSrc b) ++
    [.store .w .a5 .a6 (ACC + 56), .addi .a6 .a6 4, .addi .t0 .t0 (-1)]

/-- Limb `k` of `lo + hi + 2²²⁴ hi`, with `2²²⁴ hi`'s upper half folded once more, into `a4`. -/
def mulSrc (k : Nat) : List Instr :=
  [.load .w .a4 .a3 (ACC + 4 * k), .load .w .a2 .a3 (ACC + 56 + 4 * k), .add .a4 .a4 .a2] ++
  (if k < 7 then [.load .w .a2 .a3 (ACC + 56 + 4 * (k + 7)), .add .a4 .a4 .a2]
   else [.add .a4 .a4 .a2, .load .w .a2 .a3 (ACC + 56 + 4 * (k - 7)), .add .a4 .a4 .a2])

/-- `[o] = [a] · [b]` (`o` may be `a` or `b`), with the product in `ACC`. -/
def mul (o a b : Nat) : Prog isa :=
  .seq (.block (zeroAcc ++ [.addi .a6 .a3 0, .li .t0 14]))
    (.seq (.loop (.block (row a b)) (.nonzero .t0))
      (.block (.li .a5 0 :: pass .a3 o mulSrc ++ tail o)))

/-- Swaps limb `k` of `[x]` and `[y]` if the mask `t0` is all ones (and not
if it is zero): `d = r11 ∧ (x ⊕ y)`, `x ⊕= d`, `y ⊕= d`. -/
def cswapStep (x y k : Nat) : List Instr :=
  [.load .w .a2 .a3 (x + 4 * k), .load .w .a4 .a3 (y + 4 * k), .logic .xor .a5 .a2 .a4,
    .logic .and .a5 .a5 .t0, .logic .xor .a2 .a2 .a5, .logic .xor .a4 .a4 .a5,
    .store .w .a2 .a3 (x + 4 * k), .store .w .a4 .a3 (y + 4 * k)]

def cswap (x y : Nat) : List Instr := (List.range 14).flatMap (cswapStep x y)

/-! ## The ladder -/

/-- The mask `-swap` into `t0`. -/
def mask : List Instr := [.li .t0 0, .sub .t0 .t0 .t2]

/-- The start of an iteration of the ladder, for the bit `t = r12 - 1`: `k_t`
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

/-- The 448 iterations, for `t` from 447 down to 0, with `swap = 0`. -/
def ladder : Prog isa :=
  .seq (.block [.li .t1 448, .li .t2 0]) (.loop step (.nonzero .t1))

/-- The swap after the loop. -/
def lastSwap : List Instr := mask ++ cswap X2 X3 ++ cswap Z2 Z3

/-! ## Inversion

`[R] = [Z2]^(p-2)`, square-and-multiply over the bits of `p - 2` from 447
down to 0 (`t = r12 - 1`): `R = R²`, then `R = R · Z2` unless `t` is 224 or 1. -/

/-- `[R] = 1`. -/
def one : List Instr :=
  [.li .a1 1, .li .a2 0, .store .w .a1 .a3 R] ++ storeN .a2 (R + 4) 13

def invStep : Prog isa :=
  .seq (.block [.addi .t1 .t1 (-1)]) <| .seq (mul R R R) <|
  .seq (.block [.addi .a2 .t1 (-224)]) <|
  .seq (.ite (.zero .a2) (.block [])
    (.seq (.block [.addi .a2 .t1 (-1)]) (.ite (.zero .a2) (.block []) (mul R R Z2))))
    (.block [])

def invert : Prog isa := .seq (.block (one ++ [.li .t1 448])) (.loop invStep (.nonzero .t1))

/-! ## Encoding and decoding -/

/-- Limb `k` of `[X2]`, or of `[Y]` if the mask `t0` is all ones, as word
`k` of `out` (`a0`), a byte at a time. -/
def outStep (k : Nat) : List Instr :=
  [.load .w .a2 .a3 (X2 + 4 * k), .load .w .a4 .a3 (Y + 4 * k), .logic .xor .a4 .a4 .a2,
    .logic .and .a4 .a4 .t0, .logic .xor .a2 .a2 .a4] ++ storeLE32 .a2 .a4 .a0 (4 * k)

/-- `[X2]` reduced fully, into `out` (`a0`): `y = x + 2²²⁴ + 1` into `Y`
(the carry into limb 0, `a7` = 1 into limb 7), and `y` selected (with the
mask `t0 = -carry`) if it carries out. -/
def freeze : List Instr :=
  [.li .a5 1, .li .a7 1] ++ pass .a3 Y (foldSrc X2) ++ [.li .a1 0, .sub .t0 .a1 .a5] ++
    (List.range 14).flatMap outStep

/-- Limb `k` of `u` (word `k` at `a2`, loaded a byte at a time) into `X1`
and `X3`. -/
def decodeStep (k : Nat) : List Instr :=
  loadLE32 .a4 .a5 .a2 (4 * k) ++ [.store .w .a4 .a3 (X1 + 4 * k), .store .w .a4 .a3 (X3 + 4 * k)]

/-- `x2 = 1`, `z2 = 0`, `z3 = 1` and `A24 = 39081` (`lui`, then `addiw`). -/
def consts : List Instr :=
  [.li .a4 1, .li .a5 0] ++ li32 .a2 39081 ++ [.store .w .a4 .a3 X2,
    .store .w .a5 .a3 Z2, .store .w .a4 .a3 Z3, .store .w .a2 .a3 A24] ++
  storeN .a5 (X2 + 4) 13 ++ storeN .a5 (Z2 + 4) 13 ++ storeN .a5 (Z3 + 4) 13 ++ storeN .a5 (A24 + 4) 13

/-- The u-coordinate into `X1` and `X3`, and the constants. -/
def setup : List Instr := (List.range 14).flatMap decodeStep ++ consts

/-- The bits of the byte at `a1` into `BITS` at `a6`, advancing both. -/
def bitsBody : List Instr :=
  [.load .b .a4 .a1 0] ++
  (List.range 8).flatMap (fun j => [.shift .sll .d .a5 .a4 (63 - j), .shift .srl .d .a5 .a5 63, .store .b .a5 .a6 (BITS + j)]) ++
  [.addi .a1 .a1 1, .addi .a6 .a6 8, .addi .t0 .t0 (-1)]

/-- `BITS[8i + j] = bit j of scalar[i]`, then the clamping: bits 0 and 1
cleared and bit 447 set. -/
def bits : Prog isa :=
  .seq (.block [.addi .a6 .a3 0, .li .t0 56])
    (.seq (.loop (.block bitsBody) (.nonzero .t0))
      (.block [.li .a4 0, .store .b .a4 .a3 BITS, .store .b .a4 .a3 (BITS + 1), .li .a4 1, .store .b .a4 .a3 (BITS + 447)]))

/-- The working space rounded up to a multiple of 8 (`addi 7`, `andi -8`), in
`a3`. -/
def align : List Instr := [.addi .a3 .a3 7, .logicImm .and .a3 .a3 (-8)]

def x448 : Prog isa :=
  .seq (.block (align ++ setup)) <| .seq bits <| .seq ladder <| .seq (.block lastSwap) <|
    .seq invert <| .seq (mul X2 X2 R) (.block freeze)

end VG.Impl.X448.RISCV64
