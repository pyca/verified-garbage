module

public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# X25519: PPC64LE implementation

`vg_x25519(out = r3, scalar = r4, point = r5, scratch = r6)`.

The ARMv7 implementation's algorithm (`Impl/X25519/Arm.lean`), in 64-bit
registers, without the carry bit. Its only multiplication is `mulld` (the
low 64 bits of a product), so a field element is eight 32-bit
limbs `x0 + 2³² x1 + … + 2²²⁴ x7`, each in a word of the working space: a
product of two limbs and two more limbs fits in 64 bits. Every element is any
number below `2²⁵⁶`, standing for its residue modulo `p = 2²⁵⁵ - 19`; only
the result is reduced fully. A limb is stored with `stw`, which keeps the low
32 bits of a sum, and the carry is the sum shifted right by 32. Every element
lives in the working space, at a constant offset from its base, which stays
in `r6` (`out` stays in `r3`):

* `x1, x2, z2, x3, z3`, the ladder's temporaries, the constant `a24`, the
  inversion's result and the final reduction's temporary, 32 bytes each
  (`X1`, …);
* the 16 limbs of a product (`ACC`, 64 bytes) and the bits of the scalar
  (`BITS`, byte `t` is bit `t` of the clamped scalar).

The arithmetic (registers `r4`, `r5`, `r7`–`r11`; `r10` = 38):

* `pass`: the limbs of a number from eight sums `c_k` (below `2⁶⁴` less a
  carry), limb `k` being `c_k` plus the carry from limb `k - 1`, modulo
  `2³²`, and the carry out in `r8`;
* `tail`: the carry out (`2²⁵⁶ ≡ 38`) folded into limb 0 as `38` times itself
  and carried again (`pass` of the limbs themselves); what that carries out is
  0 or 1, and if it is 1 the limbs are small, so `38` more in limb 0 stays
  below `2³²`;
* `mul`: the 16 limbs of the product row by row (Knuth's algorithm M: each
  step `a_i b_j + acc + carry` fits in 64 bits), then the limbs of
  `lo + 38 hi` (`pass`), then `tail`;
* `add`, `sub`: the limbs of `a + b` and of `a + 4p - b` (every limb of `4p`
  is at least `2³² - 1`, so no limb is negative; `r4` holds `2³³`), then
  `tail`;
* `cswap`: with the mask `-swap` (in `r11`), as RFC 7748 §5 describes;
* `freeze`: the full reduction of the result: bit 255 folded in as 19
  (`x < 2²⁵⁵ + 19`), then `x + 19 - 2²⁵⁵` selected with a mask if it is not
  negative.

The ladder follows RFC 7748 §5 operation by operation (with `a24 · E` a
multiplication by the constant element `A24`), over the bits of the scalar
from 254 down to 0 (the counter `r12`, which indexes `BITS`; `swap` in `r0`).
The inversion `z2^(p-2)` is square-and-multiply over the bits of `p - 2 =
2²⁵⁵ - 21` from 254 down to 0 (the counter `r12`): every bit but 4 and 2 is
1.

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
def A24 : Nat := 448
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

/-- The carry out of `[o]`, in `r8`, folded in as 38 times itself, twice. -/
def tail (o : Nat) : List Instr :=
  [.mul .r8 .r8 .r10] ++ pass .r6 o (ldSrc o) ++
    [.mul .r8 .r8 .r10, .load .w .r7 .r6 o, .add .r7 .r7 .r8, .store .w .r7 .r6 o]

/-- 38 in `r10` and no carry in `r8`. -/
def prologue : List Instr := [.li .r10 38, .li .r8 0]

/-! ## Field arithmetic -/

def addSrc (a b k : Nat) : List Instr :=
  [.load .w .r7 .r6 (a + 4 * k), .load .w .r5 .r6 (b + 4 * k), .add .r7 .r7 .r5]

/-- `[o] = [a] + [b]`. -/
def add (o a b : Nat) : List Instr := prologue ++ pass .r6 o (addSrc a b) ++ tail o

/-- Limb `k` of `4p` is `2³³` added `subHi k` times, less `subLo k`. -/
def subHi (k : Nat) : List Instr := if k = 7 then [.add .r7 .r7 .r4] else [.add .r7 .r7 .r4, .add .r7 .r7 .r4]
def subLo (k : Nat) : Nat := if k = 0 then 76 else 4

def subSrc (a b k : Nat) : List Instr :=
  [.load .w .r7 .r6 (a + 4 * k)] ++ subHi k ++
    [.subi .r7 .r7 (subLo k), .load .w .r5 .r6 (b + 4 * k), .sub .r7 .r7 .r5]

/-- `[o] = [a] - [b]`, as `[a] + 4p - [b]`. -/
def sub (o a b : Nat) : List Instr :=
  prologue ++ [.li .r4 1, .lsl .r4 .r4 33] ++ pass .r6 o (subSrc a b) ++ tail o

/-- Register `r` stored into the `n` words from `o` of the working space. -/
def storeN (r : Reg) (o n : Nat) : List Instr := (List.range n).flatMap fun k => [.store .w r .r6 (o + 4 * k)]

/-! The product's 16 limbs are at an offset `acc` of the working space
(X25519's `ACC`; Ed25519 on PPC64LE uses the same code with its own). -/

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

/-- Limb `k` of `lo + 38 hi` for the product at `acc`, into `r7`. -/
def mulSrc (acc k : Nat) : List Instr :=
  [.load .w .r7 .r6 (acc + 4 * k), .load .w .r5 .r6 (acc + 32 + 4 * k), .mul .r5 .r5 .r10,
    .add .r7 .r7 .r5]

/-- `[o] = [a] · [b]` (`o` may be `a` or `b`), with the product at `acc`. -/
def mulAt (acc o a b : Nat) : Prog isa :=
  .seq (.block (prologue ++ zeroAcc acc ++ [.addi .r9 .r6 0, .li .r11 8]))
    (.seq (.loop (.block (row acc a b)) (.nonzero .d .r11))
      (.block (.li .r8 0 :: pass .r6 o (mulSrc acc) ++ tail o)))

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
  .seq (mul Z3 Z3 Z3) <| .seq (mul Z3 X1 Z3) <| .seq (mul X2 AA BB) <| .seq (mul Z2 A24 E) <|
  .seq (.block (add Z2 AA Z2)) <| .seq (mul Z2 E Z2) (.block [])

/-- The 255 iterations, for `t` from 254 down to 0, with `swap = 0`. -/
def ladder : Prog isa :=
  .seq (.block [.li .r12 255, .li .r0 0]) (.loop step (.nonzero .d .r12))

/-- The swap after the loop. -/
def lastSwap : List Instr := mask ++ cswap X2 X3 ++ cswap Z2 Z3

/-! ## Inversion

`[R] = [Z2]^(p-2)`, square-and-multiply over the bits of `p - 2` from 254
down to 0 (`t = r12 - 1`): `R = R²`, then `R = R · Z2` unless `t` is 4 or 2. -/

/-- `[R] = 1`. -/
def one : List Instr :=
  [.li .r4 1, .li .r5 0, .store .w .r4 .r6 R] ++ storeN .r5 (R + 4) 7

def invStep : Prog isa :=
  .seq (.block [.subi .r12 .r12 1]) <| .seq (mul R R R) <|
  .seq (.block [.subi .r5 .r12 4]) <|
  .seq (.ite (.zero .d .r5) (.block [])
    (.seq (.block [.subi .r5 .r12 2]) (.ite (.zero .d .r5) (.block []) (mul R R Z2))))
    (.block [])

def invert : Prog isa := .seq (.block (one ++ [.li .r12 255])) (.loop invStep (.nonzero .d .r12))

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

/-- `x2 = 1`, `z2 = 0`, `z3 = 1` and `A24 = 121665 = 2¹⁶ + 0xdb41`. -/
def consts : List Instr :=
  [.li .r7 1, .li .r8 0, .lis .r5 1, .ori .r5 .r5 0xdb41, .store .w .r7 .r6 X2,
    .store .w .r8 .r6 Z2, .store .w .r7 .r6 Z3, .store .w .r5 .r6 A24] ++
  storeN .r8 (X2 + 4) 7 ++ storeN .r8 (Z2 + 4) 7 ++ storeN .r8 (Z3 + 4) 7 ++ storeN .r8 (A24 + 4) 7

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
