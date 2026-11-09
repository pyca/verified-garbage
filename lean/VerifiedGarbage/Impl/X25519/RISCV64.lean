module

public import VerifiedGarbage.TCB.RISCV64.Isa
public import VerifiedGarbage.Impl.Words.RISCV64

/-!
# X25519 on RISC-V: field elements in radix `2³²`, and their building blocks

The PPC64LE algorithm's arithmetic (`Impl/X25519/PPC64LE.lean`), register
for register (`r3`–`r12` and `r0` are `a0`–`a7`, `t0`, `t1` and `t2`), with
RV64IM's `mul` (the low 64 bits of a product) for `mulld`, which RISC-V code
of other algorithms builds on. A field element is eight 32-bit limbs
`x0 + 2³² x1 + … + 2²²⁴ x7`, each in a word of the working space: a product
of two limbs and two more limbs fits in 64 bits. Every element is any number
below `2²⁵⁶`, standing for its residue modulo `p = 2²⁵⁵ - 19`. A limb is
stored with `sw`, which keeps the low 32 bits of a sum, and the carry is the
sum shifted right by 32.

RISC-V faults on a misaligned access, so the working space is rounded up to a
multiple of 8 (`align`). Every element lives in the working space, at a
constant offset from its rounded base, which stays in `a3`:

* `x1, x2, z2, x3, z3`, the ladder's temporaries, the constant `a24`, the
  inversion's result and the final reduction's temporary, 32 bytes each
  (`X1`, …);
* the 16 limbs of a product (`ACC`, 64 bytes) and the bits of a scalar
  (`BITS`, byte `t` is bit `t` of the clamped scalar).

The blocks (registers `a1`, `a2`, `a4`–`a7`, `t0`; `a7` = 38):

* `pass`: the limbs of a number from eight sums `c_k` (below `2⁶⁴` less a
  carry), limb `k` being `c_k` plus the carry from limb `k - 1`, modulo
  `2³²`, and the carry out in `a5`;
* `zeroAcc` and `row`: the 16 limbs of a product row by row (Knuth's
  algorithm M: each step `a_i b_j + acc + carry` fits in 64 bits);
* `cswap`: with the mask `-swap` (in `t0`), as RFC 7748 §5 describes;
* `freeze`: `[X2]` reduced fully, into `out` (`a0`): bit 255 folded in as 19
  (`x < 2²⁵⁵ + 19`), then `x + 19 - 2²⁵⁵` selected with a mask if it is not
  negative;
* `setup` and `bits`: the u-coordinate decoded a byte at a time, the
  constants, and the scalar's bits.

They use only caller-saved registers and no stack. The only branches are on
loop counters, and every address is a pointer plus a constant or a counter,
so only the pointers can affect timing.
-/

@[expose] public section

namespace VG.Impl.X25519.RISCV64

open VG.RISCV64 VG.Impl.Words.RISCV64

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

/-- A limb stored at `rb + off`: `a4 + a5` modulo `2³²`, and the carry
`(a4 + a5) >> 32` into `a5`. -/
def carryStep (rb : Reg) (off : Nat) : List Instr :=
  [.add .a4 .a4 .a5, .store .w .a4 rb off, .shift .srl .d .a5 .a4 32]

/-- The limbs at `rb + o` from the sums `src k` leaves in `a4` and the carry
in `a5`. -/
def pass (rb : Reg) (o : Nat) (src : Nat → List Instr) : List Instr :=
  (List.range 8).flatMap fun k => src k ++ carryStep rb (o + 4 * k)

/-- Limb `k` of `[o]`, into `a4`. -/
def ldSrc (o k : Nat) : List Instr := [.load .w .a4 .a3 (o + 4 * k)]

/-- 38 in `a7` and no carry in `a5`. -/
def prologue : List Instr := [.li .a7 38, .li .a5 0]

/-! ## Field arithmetic -/

def addSrc (a b k : Nat) : List Instr :=
  [.load .w .a4 .a3 (a + 4 * k), .load .w .a2 .a3 (b + 4 * k), .add .a4 .a4 .a2]

/-- Register `r` stored into the `n` words from `o` of the working space. -/
def storeN (r : Reg) (o n : Nat) : List Instr := (List.range n).flatMap fun k => [.store .w r .a3 (o + 4 * k)]

/-! The product's 16 limbs are at an offset `acc` of the working space
(X25519's `ACC`). -/

/-- The words `acc[0, 8)` zeroed. -/
def zeroAcc (acc : Nat) : List Instr := .li .a4 0 :: storeN .a4 acc 8

/-- Limb `j` of row `i` (`a6` = the base plus `4 i`, `a_i` in `a1`) into
`a4`: `a_i b_j + acc[i + j]`. -/
def rowSrc (acc b j : Nat) : List Instr :=
  [.load .w .a2 .a3 (b + 4 * j), .mul .a2 .a1 .a2, .load .w .a4 .a6 (acc + 4 * j), .add .a4 .a4 .a2]

/-- Row `i` of the product: `acc[i, i + 9) = acc[i, i + 8) + a_i · b`. -/
def row (acc a b : Nat) : List Instr :=
  [.load .w .a1 .a6 a, .li .a5 0] ++ pass .a6 acc (rowSrc acc b) ++
    [.store .w .a5 .a6 (acc + 32), .addi .a6 .a6 4, .addi .t0 .t0 (-1)]

/-- Swaps limb `k` of `[x]` and `[y]` if the mask `t0` is all ones (and not
if it is zero): `d = t0 ∧ (x ⊕ y)`, `x ⊕= d`, `y ⊕= d`. -/
def cswapStep (x y k : Nat) : List Instr :=
  [.load .w .a2 .a3 (x + 4 * k), .load .w .a4 .a3 (y + 4 * k), .logic .xor .a5 .a2 .a4,
    .logic .and .a5 .a5 .t0, .logic .xor .a2 .a2 .a5, .logic .xor .a4 .a4 .a5,
    .store .w .a2 .a3 (x + 4 * k), .store .w .a4 .a3 (y + 4 * k)]

def cswap (x y : Nat) : List Instr := (List.range 8).flatMap (cswapStep x y)

/-! ## The ladder -/

/-! ## Inversion

`[R] = [Z2]^(p-2)`, square-and-multiply over the bits of `p - 2` from 254
down to 0 (`t = t1 - 1`): `R = R²`, then `R = R · Z2` unless `t` is 4 or 2. -/

/-- `[R] = 1`. -/
def one : List Instr :=
  [.li .a1 1, .li .a2 0, .store .w .a1 .a3 R] ++ storeN .a2 (R + 4) 7

/-! ## Encoding and decoding -/

/-- `a4` modulo `2³¹` (for `a4` below `2⁶⁴`). -/
def low31 : List Instr := [.shift .sll .d .a4 .a4 33, .shift .srl .d .a4 .a4 33]

/-- Bit 255 of `[x]` cleared, and 19 times it into `a5`. -/
def freezeAAt (x : Nat) : List Instr :=
  [.load .w .a4 .a3 (x + 28), .shift .srl .d .a5 .a4 31] ++ low31 ++
  [.store .w .a4 .a3 (x + 28), .li .a2 19, .mul .a5 .a5 .a2]

/-- The mask `-(bit 255 of [y])` into `t0`, and bit 255 of `[y]` cleared. -/
def freezeBAt (y : Nat) : List Instr :=
  [.load .w .a4 .a3 (y + 28), .shift .srl .d .t0 .a4 31, .li .a1 0, .sub .t0 .a1 .t0] ++ low31 ++
    [.store .w .a4 .a3 (y + 28)]

abbrev freezeA : List Instr := freezeAAt X2
abbrev freezeB : List Instr := freezeBAt Y

/-- Limb `k` of `[X2]`, or of `[Y]` if the mask `t0` is all ones, as word
`k` of `out` (`a0`), a byte at a time. -/
def outStep (k : Nat) : List Instr :=
  [.load .w .a2 .a3 (X2 + 4 * k), .load .w .a4 .a3 (Y + 4 * k), .logic .xor .a4 .a4 .a2,
    .logic .and .a4 .a4 .t0, .logic .xor .a2 .a2 .a4] ++ storeLE32 .a2 .a4 .a0 (4 * k)

/-- `[X2]` reduced fully, into `out` (`a0`): bit 255 folded in as 19, then
`y = x + 19` into `Y`, and `y - 2²⁵⁵` selected (with the mask `t0`) if
bit 255 of `y` is set. -/
def freeze : List Instr :=
  freezeA ++ pass .a3 X2 (ldSrc X2) ++ [.li .a5 19] ++ pass .a3 Y (ldSrc X2) ++ freezeB ++
    (List.range 8).flatMap outStep

/-- Limb `k` of `u` (word `k` at `a2`, loaded a byte at a time, the top bit
masked) into `X1` and `X3`. -/
def decodeStep (k : Nat) : List Instr :=
  loadLE32 .a4 .a5 .a2 (4 * k) ++ (if k = 7 then low31 else []) ++
    [.store .w .a4 .a3 (X1 + 4 * k), .store .w .a4 .a3 (X3 + 4 * k)]

/-- `x2 = 1`, `z2 = 0`, `z3 = 1` and `A24 = 121665` (`lui`, then `addiw`). -/
def consts : List Instr :=
  [.li .a4 1, .li .a5 0] ++ li32 .a2 121665 ++ [.store .w .a4 .a3 X2,
    .store .w .a5 .a3 Z2, .store .w .a4 .a3 Z3, .store .w .a2 .a3 A24] ++
  storeN .a5 (X2 + 4) 7 ++ storeN .a5 (Z2 + 4) 7 ++ storeN .a5 (Z3 + 4) 7 ++ storeN .a5 (A24 + 4) 7

/-- The u-coordinate into `X1` and `X3`, and the constants. -/
def setup : List Instr := (List.range 8).flatMap decodeStep ++ consts

/-- The bits of the byte at `a1` into `BITS` at `a6`, advancing both. -/
def bitsBody : List Instr :=
  [.load .b .a4 .a1 0] ++
  (List.range 8).flatMap (fun j => [.shift .sll .d .a5 .a4 (63 - j), .shift .srl .d .a5 .a5 63, .store .b .a5 .a6 (BITS + j)]) ++
  [.addi .a1 .a1 1, .addi .a6 .a6 8, .addi .t0 .t0 (-1)]

/-- `BITS[8i + j] = bit j of scalar[i]`, then the clamping: bits 0, 1 and 2
cleared and bit 254 set. -/
def bits : Prog isa :=
  .seq (.block [.addi .a6 .a3 0, .li .t0 32])
    (.seq (.loop (.block bitsBody) (.nonzero .t0))
      (.block [.li .a4 0, .store .b .a4 .a3 BITS, .store .b .a4 .a3 (BITS + 1), .store .b .a4 .a3 (BITS + 2),
        .li .a4 1, .store .b .a4 .a3 (BITS + 254)]))

/-- The working space rounded up to a multiple of 8 (`addi 7`, `andi -8`), in
`a3`. -/
def align : List Instr := [.addi .a3 .a3 7, .logicImm .and .a3 .a3 (-8)]

end VG.Impl.X25519.RISCV64
