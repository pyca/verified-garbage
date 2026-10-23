module

public import VerifiedGarbage.Impl.Aes.PPC64LE.Sbox
public import VerifiedGarbage.Impl.Sm4.Circuit
import VerifiedGarbage.Impl.Aes.PPC64LE.Alloc
meta import VerifiedGarbage.Impl.Aes.PPC64LE.Alloc
public meta import VerifiedGarbage.Impl.Aes.PPC64LE.Sbox
public meta import VerifiedGarbage.Impl.Sm4.Circuit

/-!
# The bitsliced SM4 S-box on PPC64LE

The circuit `Circuit.sbox` (`Impl/Sm4/Circuit.lean`) on the eight planes of
the bitsliced state in `q 0 … q 7` (`q j` holding bit `j` of 64 bytes), in
place: the code that the AES allocator (`Impl/Aes/PPC64LE/Alloc.lean`)
produces for it with AES's registers (temporaries `r22`–`r30`, `r0` and
`r9`, all ones in `r31`), spilling to the slots 0–47 of the scratch buffer
at `r8` (it uses 0–11). It is written out (and `#guard` checks that it is
what `compile` produces) so that the kernel, which evaluates the code in
the proofs, does not have to run the allocator.
-/

@[expose] public section

namespace VG.Impl.Sm4.PPC64LE

open VG.PPC64LE VG.Impl.Aes.PPC64LE

/-- The variable of all ones and the variables `splitXnor` adds: above the
circuit's (`Circuit.sbox` numbers its variables up to 196). -/
def onesVar : Nat := 200
def freshVar : Nat := 201
def spillSlots : List Nat := List.range 48

/-- The circuit's input `xᵢ` and output `sᵢ` are bit `7 - i`. -/
def sboxIns : List (Nat × Reg) := (List.range 8).map fun i => (Sm4.Circuit.x i, q (7 - i))
def sboxOuts : List (Nat × Reg) := (List.range 8).map fun i => (Sm4.Circuit.s i, q (7 - i))

/-- The S-box on the state in `q 0 … q 7`, in place. -/
def sboxCode : List Instr := [
  .li .r31 0, .subi .r31 .r31 1, xorR .r22 .r18 .r16, xorR .r23 .r17 .r14, xorR .r24 .r15 .r23, xorR
  .r25 .r21 .r22, xorR .r26 .r19 .r24, xorR .r27 .r20 .r16, xorR .r18 .r21 .r18, xorR .r28 .r19 .r25,
  xorR .r29 .r20 .r28, xorR .r30 .r21 .r17, xorR .r0 .r20 .r18, xorR .r9 .r19 .r22, xorR .r28 .r15 .r28,
  xorR .r28 .r28 .r31, stS 0 .r28, xorR .r28 .r23 .r25, stS 1 .r29, xorR .r29 .r14 .r0, xorR .r0 .r26
  .r0, stS 2 .r0, xorR .r0 .r15 .r27, xorR .r20 .r20 .r28, xorR .r14 .r14 .r25, xorR .r14 .r14 .r31,
  xorR .r28 .r15 .r30, xorR .r17 .r17 .r9, xorR .r17 .r17 .r31, xorR .r18 .r24 .r18, stS 3 .r25, xorR
  .r25 .r22 .r26, stS 4 .r25, xorR .r25 .r26 .r27, xorR .r16 .r21 .r16, xorR .r16 .r16 .r31, xorR .r29
  .r15 .r29, xorR .r29 .r29 .r31, xorR .r23 .r23 .r9, xorR .r19 .r19 .r30, xorR .r19 .r19 .r31, ldS .r30
  1, xorR .r9 .r15 .r30, xorR .r22 .r22 .r24, xorR .r22 .r22 .r31, xorR .r21 .r21 .r24, xorR .r21 .r21
  .r31, ldS .r24 0, stS 5 .r31, andR .r31 .r9 .r24, stS 6 .r9, andR .r9 .r26 .r17, xorR .r9 .r9 .r31,
  stS 7 .r26, andR .r26 .r20 .r28, xorR .r26 .r26 .r31, andR .r31 .r15 .r23, stS 8 .r15, andR .r15 .r27
  .r19, xorR .r15 .r15 .r31, stS 9 .r27, andR .r27 .r0 .r14, xorR .r27 .r27 .r31, andR .r31 .r18 .r22,
  stS 10 .r18, andR .r18 .r30 .r21, xorR .r18 .r18 .r31, ldS .r30 3, stS 11 .r0, andR .r0 .r25 .r30,
  xorR .r0 .r0 .r31, xorR .r9 .r9 .r18, xorR .r26 .r26 .r0, xorR .r15 .r15 .r18, xorR .r27 .r27 .r0,
  xorR .r9 .r9 .r16, ldS .r16 2, xorR .r26 .r26 .r16, ldS .r16 4, xorR .r15 .r15 .r16, xorR .r27 .r27
  .r29, xorR .r29 .r9 .r26, andR .r9 .r9 .r15, xorR .r16 .r27 .r9, andR .r0 .r29 .r16, xorR .r0 .r0
  .r26, xorR .r18 .r15 .r27, xorR .r26 .r26 .r9, andR .r26 .r26 .r18, xorR .r26 .r26 .r27, xorR .r15
  .r15 .r26, xorR .r18 .r16 .r26, andR .r27 .r27 .r18, xorR .r15 .r27 .r15, xorR .r16 .r16 .r27, andR
  .r16 .r0 .r16, xorR .r29 .r29 .r16, xorR .r16 .r29 .r15, xorR .r27 .r0 .r26, xorR .r18 .r0 .r29, xorR
  .r9 .r26 .r15, xorR .r31 .r27 .r16, andR .r24 .r9 .r24, andR .r17 .r15 .r17, andR .r28 .r26 .r28, andR
  .r23 .r18 .r23, andR .r19 .r29 .r19, andR .r14 .r0 .r14, andR .r22 .r27 .r22, andR .r21 .r31 .r21,
  andR .r30 .r16 .r30, stS 3 .r28, ldS .r28 6, andR .r9 .r9 .r28, ldS .r28 7, andR .r15 .r15 .r28, andR
  .r26 .r26 .r20, ldS .r20 8, andR .r18 .r18 .r20, ldS .r20 9, andR .r29 .r29 .r20, ldS .r20 11, andR
  .r0 .r0 .r20, ldS .r20 10, andR .r27 .r27 .r20, ldS .r20 1, andR .r31 .r31 .r20, andR .r16 .r16 .r25,
  xorR .r9 .r9 .r27, xorR .r22 .r22 .r15, xorR .r14 .r24 .r14, xorR .r25 .r29 .r22, xorR .r0 .r0 .r25,
  xorR .r30 .r17 .r30, xorR .r25 .r21 .r0, xorR .r16 .r16 .r9, xorR .r20 .r19 .r14, xorR .r28 .r25 .r16,
  stS 1 .r19, xorR .r19 .r26 .r20, stS 10 .r28, xorR .r28 .r31 .r30, xorR .r9 .r9 .r28, xorR .r14 .r23
  .r14, xorR .r14 .r9 .r14, xorR .r26 .r26 .r16, xorR .r29 .r29 .r31, xorR .r18 .r18 .r27, xorR .r22
  .r22 .r20, xorR .r30 .r30 .r19, xorR .r0 .r0 .r30, ldS .r30 5, xorR .r0 .r0 .r30, xorR .r15 .r15 .r14,
  ldS .r14 3, xorR .r14 .r14 .r25, xorR .r21 .r21 .r15, xorR .r21 .r21 .r30, xorR .r29 .r29 .r18, xorR
  .r29 .r29 .r30, xorR .r24 .r24 .r17, ldS .r17 10, xorR .r23 .r23 .r17, xorR .r17 .r17 .r24, xorR .r19
  .r19 .r14, xorR .r20 .r19 .r30, ldS .r19 1, xorR .r16 .r19 .r23, xorR .r9 .r9 .r22, xorR .r18 .r9
  .r30, stS 5 .r21, movR .r21 .r29, movR .r19 .r17, movR .r17 .r26, movR .r15 .r0, ldS .r14 5]

#guard sboxCode == compile sb Sm4.Circuit.sbox sboxIns sboxOuts sboxFree onesReg onesVar freshVar spillSlots

end VG.Impl.Sm4.PPC64LE
