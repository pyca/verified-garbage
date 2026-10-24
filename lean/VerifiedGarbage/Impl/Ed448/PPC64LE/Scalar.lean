module

public import VerifiedGarbage.Impl.X448.PPC64LE
public import VerifiedGarbage.Spec.Ed448

/-!
# Ed448 on PPC64LE: scalars modulo `L`

`vg_ed448_scalar_reduce(out = r3, wide = r4, scratch = r5)` and
`vg_ed448_scalar_mul_add(out = r3, r = r4, k = r5, s = r6, scratch = r7)`.

Ed25519's bit-serial reduction on this target (`Impl/Ed25519/PPC64LE/Scalar.lean`)
in X448's fourteen 32-bit limbs (`Impl/X448/PPC64LE.lean`): a remainder
below `L < 2⁴⁴⁶` at `o` is doubled, plus the next bit of the input, then
`o + (2⁴⁴⁸ - 1 - L) + 1` computed at `SD`, whose carry out is 1 exactly
when the doubled remainder is at least `L`, and selected with a mask. The
input's bytes are read from the top, at `r14` (counted by `r15`, the byte in
`r16`).

Multiply-add reduces `k`, `s` and `r` modulo `L` into `SK`, `SS` and `SA`,
multiplies the first two with X448's rows (its field multiplication without
the reduction, into X448's `ACC`), adds the third, and reduces the 112 bytes
of the sum, copied to `WIDE`.

The working space's base is in `r6`. The nonvolatile registers the functions
use are saved at `SAVE`; the pointers stay in nonvolatile registers (`r14`,
`r17`–`r19`, `r26`, `r27`), which are never stored. The only branches are on
the byte counter, and every address is a pointer plus a constant or the
counter, so only the pointers can affect timing.
-/

@[expose] public section

namespace VG.Impl.Ed448.PPC64LE

open VG.PPC64LE
open VG.Impl.X448.PPC64LE (pass storeN cswap zeroAcc row addSrc ldSrc ACC)

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
/-- Where the functions save the nonvolatile registers. -/
def SAVE : Nat := 1064

/-! ## One bit -/

/-- Word `k` of `2⁴⁴⁸ - 1 - L`. -/
def scalarComplement (k : Nat) : Nat := 2 ^ 32 - 1 - Spec.Ed448.L / 2 ^ (32 * k) % 2 ^ 32

def scalarDoubleSrc (o k : Nat) : List Instr := [.load .w .r7 .r6 (o + 4 * k), .add .r7 .r7 .r7]

/-- Word `k` of the remainder at `o` plus that of the complement, which `lis`
and `ori` build and `rlwinm` zero-extends. -/
def scalarSubtractSrc (o k : Nat) : List Instr :=
  [.load .w .r7 .r6 (o + 4 * k), .lis .r5 (BitVec.ofNat 16 (scalarComplement k / 2 ^ 16)),
    .ori .r5 .r5 (BitVec.ofNat 16 (scalarComplement k)), .rotr .w .r5 .r5 0, .add .r7 .r7 .r5]

/-- Bit `j` of `r16` into the remainder at `o`: doubled with the bit as the
carry in, then `L` subtracted if it is at least `L`. -/
def scalarBit (o j : Nat) : List Instr :=
  [.lsl .r8 .r16 (63 - j), .lsr .d .r8 .r8 63] ++ pass .r6 o (scalarDoubleSrc o) ++ [.li .r8 1] ++
    pass .r6 SD (scalarSubtractSrc o) ++ [.li .r11 0, .sub .r11 .r11 .r8] ++ cswap o SD

/-- The next byte from the top, at `r14 + r15 - 1`, into `r16`. -/
def scalarRead : List Instr := [.subi .r15 .r15 1, .add .r7 .r14 .r15, .lbz .r16 .r7 0]

def scalarByte (o : Nat) : List Instr := scalarRead ++ (List.range 8).reverse.flatMap (scalarBit o)

/-- The `n` bytes at `r14` modulo `L`, into the remainder at `o`. -/
def scalarEngine (o n : Nat) : Prog isa :=
  .seq (.block ([.li .r7 0] ++ storeN .r7 o 14 ++ [.li .r15 n])) (.loop (.block (scalarByte o)) (.nonzero .d .r15))

/-! ## Saving the nonvolatile registers -/

/-- The nonvolatile registers the functions change. -/
def savedRegs : List Reg := [.r14, .r15, .r16, .r17, .r18, .r19, .r26, .r27, .r28, .r29, .r30, .r31]

def scalarSave (base : Reg) : List Instr :=
  (List.range 12).map fun i => .store .d (savedRegs.getD i .r14) base (SAVE + 8 * i)

def scalarRestore : List Instr :=
  (List.range 12).map fun i => .load .d (savedRegs.getD i .r14) .r6 (SAVE + 8 * i)

/-! ## The output -/

def packStep (a k : Nat) : List Instr := [.load .w .r7 .r6 (a + 4 * k), .store .w .r7 .r14 (4 * k)]

/-- The `n` words at `a` to the bytes at `r14`. -/
def packWords (a n : Nat) : List Instr := (List.range n).flatMap (packStep a)

/-- The remainder at `a` as the 57 bytes at `r14`: its fourteen words and a zero byte. -/
def packScalar (a : Nat) : List Instr := packWords a 14 ++ [.li .r7 0, .stb .r7 .r14 56]

/-- The remainder at `SR` to the output (in `r27`), and the registers restored. -/
def scalarFinish : List Instr := [.addi .r14 .r27 0] ++ packScalar SR ++ scalarRestore

/-! ## `vg_ed448_scalar_reduce(out = r3, wide = r4, scratch = r5)` -/

def scalarReduceSetup : List Instr :=
  scalarSave .r5 ++ [.addi .r6 .r5 0, .addi .r27 .r3 0, .addi .r14 .r4 0]

def scalarReduce : Prog isa :=
  .seq (.block scalarReduceSetup) (.seq (scalarEngine SR 114) (.block scalarFinish))

/-! ## `vg_ed448_scalar_mul_add(out = r3, r = r4, k = r5, s = r6, scratch = r7)` -/

/-- The registers saved, the output's address into `r27`, `r` into `r26`, `s`
into `r17`, the working space into `r6`, and `k` into `r14`. -/
def scalarMulAddArgs : List Instr :=
  scalarSave .r7 ++ [.addi .r27 .r3 0, .addi .r26 .r4 0, .addi .r17 .r6 0, .addi .r6 .r7 0, .addi .r14 .r5 0]

/-- `k`, `s` and `r` modulo `L` into `SK`, `SS` and `SA`. -/
def scalarInputs : Prog isa :=
  .seq (scalarEngine SK 57) <| .seq (.block [.addi .r14 .r17 0]) <| .seq (scalarEngine SS 57) <|
    .seq (.block [.addi .r14 .r26 0]) (scalarEngine SA 57)

/-- The 28 limbs of the product of `SK` and `SS` at `ACC`. -/
def scalarProduct : Prog isa :=
  .seq (.block (zeroAcc ++ [.addi .r9 .r6 0, .li .r11 14])) (.loop (.block (row SK SS)) (.nonzero .d .r11))

/-- `SA` added to the product, and the sum's 112 bytes to `WIDE`. -/
def scalarSum : List Instr :=
  [.li .r8 0] ++ pass .r6 ACC (addSrc ACC SA) ++ pass .r6 (ACC + 56) (ldSrc (ACC + 56)) ++
    [.addi .r14 .r6 WIDE] ++ packWords ACC 28

def scalarMulAdd : Prog isa :=
  .seq (.block scalarMulAddArgs) <| .seq scalarInputs <| .seq scalarProduct <|
    .seq (.block scalarSum) <| .seq (scalarEngine SR 112) (.block scalarFinish)

end VG.Impl.Ed448.PPC64LE
