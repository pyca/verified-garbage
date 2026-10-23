module

public import VerifiedGarbage.Impl.Aes.PPC64LE.Sbox
public import VerifiedGarbage.Impl.Camellia.Circuit
import VerifiedGarbage.Impl.Aes.PPC64LE.Alloc
meta import VerifiedGarbage.Impl.Aes.PPC64LE.Alloc
public meta import VerifiedGarbage.Impl.Aes.PPC64LE.Sbox
public meta import VerifiedGarbage.Impl.Camellia.Circuit

/-!
# The bitsliced Camellia S-box on PPC64LE

The circuit `Circuit.sbox` (`SBOX1`) on the eight planes of the bitsliced
state in `q 0 … q 7` (`q j` holding bit `j` of 64 bytes), in place: the
code that the AES allocator (`Impl/Aes/PPC64LE/Alloc.lean`) produces for it
with AES's registers (temporaries `r22`–`r30`, `r0` and `r9`, all ones in
`r31`), spilling to the slots 0–47 of the scratch buffer at `r8` (it uses
0–12). It is written out (and `#guard` checks that it is what `compile`
produces) so that the kernel, which evaluates the code in the proofs, does
not have to run the allocator.
-/

@[expose] public section

namespace VG.Impl.Camellia.PPC64LE

open VG.PPC64LE VG.Impl.Aes.PPC64LE

/-- The variable of all ones and the variables `splitXnor` adds: above the
circuit's (`Circuit.sbox` numbers its variables up to 123). -/
def onesVar : Nat := 200
def freshVar : Nat := 201
def spillSlots : List Nat := List.range 48

/-- The circuit's input `xᵢ` and output `sᵢ` are bit `7 - i`. -/
def sboxIns : List (Nat × Reg) := (List.range 8).map fun i => (Camellia.Circuit.x i, q (7 - i))
def sboxOuts : List (Nat × Reg) := (List.range 8).map fun i => (Camellia.Circuit.s i, q (7 - i))

/-- `SBOX1` on the state in `q 0 … q 7`, in place. -/
def sboxCode : List Instr := [
  .li .r31 0, .subi .r31 .r31 1, xorR .r22 .r21 .r15, xorR .r23 .r19 .r17, xorR .r24 .r16 .r22,
  xorR .r25 .r20 .r14, xorR .r26 .r14 .r23, xorR .r27 .r18 .r15, xorR .r28 .r18 .r24, xorR .r29
  .r20 .r23, xorR .r30 .r16 .r25, xorR .r0 .r24 .r25, xorR .r9 .r21 .r20, stS 0 .r30, xorR .r30
  .r21 .r25, stS 1 .r21, xorR .r21 .r30 .r31, stS 2 .r30, xorR .r30 .r20 .r17, stS 3 .r21, xorR
  .r21 .r19 .r15, stS 4 .r20, xorR .r20 .r19 .r14, xorR .r19 .r19 .r24, xorR .r25 .r18 .r25,
  xorR .r18 .r18 .r9, xorR .r17 .r17 .r14, xorR .r17 .r17 .r31, xorR .r14 .r16 .r26, xorR .r16
  .r16 .r27, xorR .r16 .r16 .r31, xorR .r9 .r15 .r29, xorR .r9 .r9 .r31, stS 5 .r9, xorR .r9
  .r22 .r26, xorR .r22 .r22 .r29, xorR .r29 .r23 .r27, stS 6 .r9, xorR .r9 .r23 .r28, xorR .r23
  .r23 .r0, stS 7 .r23, xorR .r23 .r24 .r26, xorR .r23 .r23 .r31, xorR .r24 .r24 .r30, xorR .r24
  .r24 .r31, xorR .r26 .r26 .r27, xorR .r26 .r26 .r31, xorR .r20 .r28 .r20, xorR .r20 .r20 .r31,
  ldS .r27 0, xorR .r21 .r27 .r21, xorR .r21 .r21 .r31, xorR .r27 .r27 .r29, xorR .r27 .r27
  .r31, ldS .r29 1, ldS .r30 4, stS 0 .r24, xorR .r24 .r29 .r30, xorR .r24 .r24 .r31, xorR .r24
  .r24 .r30, xorR .r29 .r29 .r15, xorR .r29 .r29 .r31, andR .r15 .r16 .r18, andR .r30 .r24 .r21,
  xorR .r30 .r30 .r15, stS 1 .r31, andR .r31 .r28 .r20, xorR .r31 .r31 .r15, andR .r15 .r14
  .r23, stS 4 .r14, andR .r14 .r22 .r19, xorR .r14 .r14 .r15, stS 8 .r22, andR .r22 .r0 .r17,
  xorR .r22 .r22 .r15, andR .r15 .r25 .r9, stS 9 .r25, andR .r25 .r26 .r27, xorR .r25 .r25 .r15,
  stS 10 .r26, ldS .r26 5, stS 11 .r0, ldS .r0 3, stS 12 .r28, andR .r28 .r26 .r0, xorR .r28
  .r28 .r15, xorR .r30 .r30 .r25, xorR .r31 .r31 .r28, xorR .r14 .r14 .r25, xorR .r22 .r22 .r28,
  ldS .r28 7, xorR .r30 .r30 .r28, ldS .r28 6, xorR .r31 .r31 .r28, xorR .r14 .r14 .r29, ldS
  .r29 0, xorR .r22 .r22 .r29, xorR .r29 .r30 .r31, andR .r30 .r30 .r14, xorR .r28 .r22 .r30,
  andR .r25 .r29 .r28, xorR .r25 .r25 .r31, xorR .r15 .r14 .r22, xorR .r31 .r31 .r30, andR .r31
  .r31 .r15, xorR .r31 .r31 .r22, xorR .r14 .r14 .r31, xorR .r15 .r28 .r31, andR .r22 .r22 .r15,
  xorR .r14 .r22 .r14, xorR .r28 .r28 .r22, andR .r28 .r25 .r28, xorR .r29 .r29 .r28, xorR .r28
  .r29 .r14, xorR .r22 .r25 .r31, xorR .r15 .r25 .r29, xorR .r30 .r31 .r14, xorR .r26 .r22 .r28,
  andR .r18 .r30 .r18, andR .r21 .r14 .r21, andR .r20 .r31 .r20, andR .r23 .r15 .r23, andR .r19
  .r29 .r19, andR .r17 .r25 .r17, andR .r9 .r22 .r9, andR .r27 .r26 .r27, andR .r0 .r28 .r0,
  andR .r30 .r30 .r16, andR .r14 .r14 .r24, ldS .r24 12, andR .r31 .r31 .r24, ldS .r24 4, andR
  .r15 .r15 .r24, ldS .r24 8, andR .r29 .r29 .r24, ldS .r24 11, andR .r25 .r25 .r24, ldS .r24 9,
  andR .r22 .r22 .r24, ldS .r24 10, andR .r26 .r26 .r24, ldS .r24 5, andR .r28 .r28 .r24, xorR
  .r27 .r21 .r27, xorR .r23 .r23 .r17, xorR .r24 .r9 .r0, xorR .r16 .r18 .r26, xorR .r31 .r31
  .r27, stS 5 .r27, xorR .r27 .r15 .r23, stS 10 .r23, xorR .r23 .r22 .r24, xorR .r25 .r20 .r25,
  xorR .r9 .r9 .r28, xorR .r0 .r0 .r30, xorR .r30 .r30 .r14, xorR .r29 .r29 .r27, xorR .r26 .r26
  .r23, stS 9 .r26, xorR .r26 .r16 .r31, xorR .r18 .r18 .r20, xorR .r21 .r21 .r19, xorR .r17
  .r17 .r16, xorR .r14 .r14 .r9, xorR .r15 .r15 .r31, ldS .r31 5, xorR .r22 .r22 .r31, xorR .r28
  .r28 .r0, ldS .r31 10, xorR .r31 .r31 .r30, xorR .r18 .r24 .r18, xorR .r27 .r27 .r25, xorR
  .r23 .r23 .r30, xorR .r25 .r25 .r0, xorR .r9 .r9 .r22, ldS .r22 9, xorR .r0 .r29 .r22, xorR
  .r29 .r29 .r26, xorR .r22 .r22 .r31, ldS .r31 1, xorR .r19 .r22 .r31, xorR .r26 .r26 .r14,
  xorR .r16 .r26 .r31, xorR .r21 .r21 .r17, xorR .r15 .r15 .r25, xorR .r17 .r15 .r31, xorR .r28
  .r28 .r29, xorR .r15 .r28 .r31, xorR .r27 .r27 .r9, xorR .r23 .r23 .r21, xorR .r20 .r23 .r31,
  movR .r21 .r27, movR .r14 .r0]

#guard sboxCode == compile sb Camellia.Circuit.sbox sboxIns sboxOuts sboxFree onesReg onesVar freshVar spillSlots

end VG.Impl.Camellia.PPC64LE
