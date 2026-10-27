module

public import VerifiedGarbage.Impl.X448.RISCV64
public import VerifiedGarbage.Spec.Ed448

/-!
# Ed448 on RISC-V: scalars modulo `L`

`vg_ed448_scalar_reduce(out = a0, wide = a1, scratch = a2)` and
`vg_ed448_scalar_mul_add(out = a0, r = a1, k = a2, s = a3, scratch = a4)`.

The PPC64LE functions (`Impl/Ed448/PPC64LE/Scalar.lean`), on X448's RISC-V
field code (`Impl/X448/RISCV64.lean`: fourteen 32-bit limbs, one to a word of
the working space, whose base stays in `a3`): Ed25519's bit-serial
reduction, a remainder below `L < 2⁴⁴⁶` at `o` doubled, plus the next bit of
the input, then `o + (2⁴⁴⁸ - 1 - L) + 1` computed at `SD`, whose carry out is
1 exactly when the doubled remainder is at least `L`, and selected with a
mask. The input's bytes are read from the top, at `t3` (counted by `t4`, the
byte in `t5`).

Multiply-add reduces `k`, `s` and `r` modulo `L` into `SK`, `SS` and `SA`,
multiplies the first two with X448's rows (its field multiplication without
the reduction, into X448's `ACC`), adds the third, and reduces the 112 bytes
of the sum, copied to `WIDE`.

RISC-V faults on a misaligned access and the contracts state no alignment
for the bytes, so `scratch` is rounded up to a multiple of 8 (`align`), and
the inputs are read a byte at a time and the result written a byte at a time
(`storeLE32`). The functions use only caller-saved registers and no stack:
`out` stays in `a0`, which the field code never writes, and the pointers to
`s` and `r` in `t6` and `t2`. The only branches are on the byte counter, and
every address is a pointer plus a constant or the counter, so only the
pointers can affect timing.
-/

@[expose] public section

namespace VG.Impl.Ed448.RISCV64

open VG.RISCV64 VG.Impl.Words.RISCV64
open VG.Impl.X448.RISCV64 (pass storeN cswap zeroAcc row addSrc ldSrc ACC align)

/-! ## The layout of the working space -/

/-- The remainder of a reduction, and its candidate. -/
def SR : Nat := 0
def SD : Nat := 56
/-- The reduced `k`, `s` and `r` of multiply-add. -/
def SK : Nat := 112
def SS : Nat := 168
def SA : Nat := 224
/-- The bytes of `k s + r`. -/
def WIDE : Nat := 280

/-! ## One bit -/

/-- Word `k` of `2⁴⁴⁸ - 1 - L`. -/
def scalarComplement (k : Nat) : Nat := 2 ^ 32 - 1 - Spec.Ed448.L / 2 ^ (32 * k) % 2 ^ 32

def scalarDoubleSrc (o k : Nat) : List Instr := [.load .w .a4 .a3 (o + 4 * k), .add .a4 .a4 .a4]

/-- Word `k` of the remainder at `o` plus that of the complement, which `lui`
and `addiw` build (sign-extended) and two shifts zero-extend. -/
def scalarSubtractSrc (o k : Nat) : List Instr :=
  [.load .w .a4 .a3 (o + 4 * k)] ++ li32 .a2 (BitVec.ofNat 32 (scalarComplement k)) ++
    [.shift .sll .d .a2 .a2 32, .shift .srl .d .a2 .a2 32, .add .a4 .a4 .a2]

/-- Bit `j` of `t5` into the remainder at `o`: doubled with the bit as the
carry in, then `L` subtracted if it is at least `L`. -/
def scalarBit (o j : Nat) : List Instr :=
  [.shift .sll .d .a5 .t5 (63 - j), .shift .srl .d .a5 .a5 63] ++ pass .a3 o (scalarDoubleSrc o) ++
    [.li .a5 1] ++ pass .a3 SD (scalarSubtractSrc o) ++ [.li .t0 0, .sub .t0 .t0 .a5] ++ cswap o SD

/-- The next byte from the top, at `t3 + t4 - 1`, into `t5`. -/
def scalarRead : List Instr := [.addi .t4 .t4 (-1), .add .a4 .t3 .t4, .load .b .t5 .a4 0]

def scalarByte (o : Nat) : List Instr := scalarRead ++ (List.range 8).reverse.flatMap (scalarBit o)

/-- The `n` bytes at `t3` modulo `L`, into the remainder at `o`. -/
def scalarEngine (o n : Nat) : Prog isa :=
  .seq (.block ([.li .a4 0] ++ storeN .a4 o 14 ++ [.li .t4 n])) (.loop (.block (scalarByte o)) (.nonzero .t4))

/-! ## The output -/

/-- Word `k` of the remainder at `SR` as bytes `4 k` to `4 k + 3` of `out`
(`a0`), a byte at a time. -/
def outStep (k : Nat) : List Instr := [.load .w .a4 .a3 (SR + 4 * k)] ++ storeLE32 .a4 .a5 .a0 (4 * k)

/-- The remainder at `SR` as the 57 bytes at `out`: its fourteen words and a
zero byte. -/
def scalarFinish : List Instr := (List.range 14).flatMap outStep ++ [.li .a4 0, .store .b .a4 .a0 56]

/-- The word `k` at `a` stored at `t3 + 4 k`. -/
def packStep (a k : Nat) : List Instr := [.load .w .a4 .a3 (a + 4 * k), .store .w .a4 .t3 (4 * k)]

/-- The `n` words at `a` to the words at `t3`, which is aligned. -/
def packWords (a n : Nat) : List Instr := (List.range n).flatMap (packStep a)

/-! ## `vg_ed448_scalar_reduce(out = a0, wide = a1, scratch = a2)` -/

def scalarReduceSetup : List Instr := [.addi .a3 .a2 0] ++ align ++ [.addi .t3 .a1 0]

def scalarReduce : Prog isa :=
  .seq (.block scalarReduceSetup) (.seq (scalarEngine SR 114) (.block scalarFinish))

/-! ## `vg_ed448_scalar_mul_add(out = a0, r = a1, k = a2, s = a3, scratch = a4)` -/

/-- `s` into `t6`, `r` into `t2`, `k` into `t3`, and the working space,
rounded up, into `a3`. -/
def scalarMulAddArgs : List Instr :=
  [.addi .t6 .a3 0, .addi .t2 .a1 0, .addi .t3 .a2 0, .addi .a3 .a4 0] ++ align

/-- `k`, `s` and `r` modulo `L` into `SK`, `SS` and `SA`. -/
def scalarInputs : Prog isa :=
  .seq (scalarEngine SK 57) <| .seq (.block [.addi .t3 .t6 0]) <| .seq (scalarEngine SS 57) <|
    .seq (.block [.addi .t3 .t2 0]) (scalarEngine SA 57)

/-- The 28 limbs of the product of `SK` and `SS` at `ACC`. -/
def scalarProduct : Prog isa :=
  .seq (.block (zeroAcc ++ [.addi .a6 .a3 0, .li .t0 14])) (.loop (.block (row SK SS)) (.nonzero .t0))

/-- `SA` added to the product, and the sum's 112 bytes to `WIDE` (aligned), at
`t3`. -/
def scalarSum : List Instr :=
  [.li .a5 0] ++ pass .a3 ACC (addSrc ACC SA) ++ pass .a3 (ACC + 56) (ldSrc (ACC + 56)) ++
    [.addi .t3 .a3 WIDE] ++ packWords ACC 28

def scalarMulAdd : Prog isa :=
  .seq (.block scalarMulAddArgs) <| .seq scalarInputs <| .seq scalarProduct <|
    .seq (.block scalarSum) <| .seq (scalarEngine SR 112) (.block scalarFinish)

end VG.Impl.Ed448.RISCV64
