module

public import VerifiedGarbage.TCB.RISCV64.Isa
public import VerifiedGarbage.Impl.Words.RISCV64

/-!
# X448 on RISC-V: fourteen 32-bit limbs

The pieces of the PPC64LE implementation's algorithm (`Impl/X448/PPC64LE.lean`),
register for register (`r3`–`r12` and `r0` are `a0`–`a7`, `t0`, `t1` and `t2`,
as in `Impl/X25519/RISCV64.lean`), that RISC-V code builds on
(`Impl/X448/RISCV64/R64.lean`, Ed448's). A field element is fourteen 32-bit limbs
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
  `2³²`, and the carry out in `a5`; its sources `foldSrc` (the carry out `c`
  folded in as `c + 2²²⁴ c`, added to limbs 0 and 7) and `addSrc`;
* `row`: a row of a product (Knuth's algorithm M), into the 28 limbs at
  `ACC`;
* `cswap`: with the mask `-swap` (in `t0`), as RFC 7748 §5 describes;
* `freeze`: the full reduction of the result: `y = x + 2²²⁴ + 1` carries out
  exactly when `x ≥ p` (`x < 2⁴⁴⁸`), and is then `x - p` modulo `2⁴⁴⁸`,
  selected with a mask.

The pieces use only caller-saved registers and no stack. The only branches
are on the loop counters, and every address is a pointer plus a constant or a
counter.
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

/-! ## Field arithmetic -/

def addSrc (a b k : Nat) : List Instr :=
  [.load .w .a4 .a3 (a + 4 * k), .load .w .a2 .a3 (b + 4 * k), .add .a4 .a4 .a2]

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

/-- Swaps limb `k` of `[x]` and `[y]` if the mask `t0` is all ones (and not
if it is zero): `d = r11 ∧ (x ⊕ y)`, `x ⊕= d`, `y ⊕= d`. -/
def cswapStep (x y k : Nat) : List Instr :=
  [.load .w .a2 .a3 (x + 4 * k), .load .w .a4 .a3 (y + 4 * k), .logic .xor .a5 .a2 .a4,
    .logic .and .a5 .a5 .t0, .logic .xor .a2 .a2 .a5, .logic .xor .a4 .a4 .a5,
    .store .w .a2 .a3 (x + 4 * k), .store .w .a4 .a3 (y + 4 * k)]

def cswap (x y : Nat) : List Instr := (List.range 14).flatMap (cswapStep x y)

/-! ## Inversion -/

/-- `[R] = 1`, where the inversion starts. -/
def one : List Instr :=
  [.li .a1 1, .li .a2 0, .store .w .a1 .a3 R] ++ storeN .a2 (R + 4) 13

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

/-- The base point's u-coordinate, 5, into `X1` and `X3`. -/
def five : List Instr :=
  [.li .a4 5, .li .a5 0, .store .w .a4 .a3 X1, .store .w .a4 .a3 X3] ++ storeN .a5 (X1 + 4) 13 ++
    storeN .a5 (X3 + 4) 13

/-- `setup` for the base point: its u-coordinate, 5, into `X1` and `X3`, and
the constants. -/
def setupBase : List Instr := five ++ consts

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

end VG.Impl.X448.RISCV64
