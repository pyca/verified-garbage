module

public import VerifiedGarbage.Impl.Sm4.Circuit
meta import VerifiedGarbage.Impl.Sm4.Circuit
public import VerifiedGarbage.Impl.Aes.Arm.Sbox
meta import VerifiedGarbage.Impl.Aes.Arm.Sbox

/-!
# The bitsliced SM4 S-box on ARMv7

The circuit `Circuit.sbox` on the eight planes of the state (`q j` holds
bit `j` of 32 bytes: a word of eight blocks), in place: the code that the
AES allocator `compile` produces for it, with the temporaries in
`r10`–`r12` and `lr`, all ones in slot 0 of the scratch buffer at `r8`,
and spilling to its next slots. It is written out (and `#guard` checks
that it is what `compile` produces) so that the kernel, which evaluates
the code in the proofs, does not have to run the allocator.
-/

@[expose] public section

namespace VG.Impl.Sm4.Arm

open VG.Arm VG.Impl.Aes.Arm

/-- The circuit's input `xᵢ` and output `sᵢ` are bit `7 - i`, in `q (7 - i)`. -/
def sboxIns : List (Nat × Reg) := (List.range 8).map fun i => (VG.Impl.Sm4.Circuit.x i, q (7 - i))
def sboxOuts : List (Nat × Reg) := (List.range 8).map fun i => (VG.Impl.Sm4.Circuit.s i, q (7 - i))

/-- The variables `compile` uses for all ones and for the gates it splits,
above the circuit's own. -/
def onesVar : Nat := 200
def freshVar : Nat := 201

/-- The S-box on the state in `q 0 … q 7`, in place. -/
def sboxCode : List Instr := [
  .mov .r10 (.imm 0), .dp .sub .r10 .r10 (.imm 1), stS 0 .r10, eorR .r10 .r4 .r2, eorR .r11 .r3 .r0,
  eorR .r12 .r1 .r11, eorR .lr .r7 .r10, stS 1 .r0, eorR .r0 .r5 .r12, stS 2 .r12,
  eorR .r12 .r6 .r2, eorR .r4 .r7 .r4, stS 3 .r2, eorR .r2 .r5 .lr, stS 4 .r12, eorR .r12 .r6 .r2,
  stS 5 .r12, eorR .r12 .r7 .r3, stS 6 .r7, eorR .r7 .r6 .r4, stS 7 .r4, eorR .r4 .r5 .r10,
  eorR .r2 .r1 .r2, stS 8 .r5, ldS .r5 0, eorR .r2 .r2 .r5, stS 9 .r2, eorR .r2 .r11 .lr,
  stS 10 .r11, ldS .r11 1, stS 11 .r10, eorR .r10 .r11 .r7, eorR .r7 .r0 .r7, stS 12 .r7, ldS .r7 4,
  stS 13 .r10, eorR .r10 .r1 .r7, eorR .r6 .r6 .r2, eorR .r11 .r11 .lr, eorR .r11 .r11 .r5,
  eorR .r2 .r1 .r12, eorR .r3 .r3 .r4, eorR .r3 .r3 .r5, stS 1 .lr, ldS .lr 2, stS 14 .r11,
  ldS .r11 7, eorR .r11 .lr .r11, stS 7 .r11, ldS .r11 11, stS 15 .r10, eorR .r10 .r11 .r0,
  stS 16 .r10, eorR .r10 .r0 .r7, stS 17 .r10, ldS .r10 6, ldS .r7 3, eorR .r7 .r10 .r7,
  eorR .r7 .r7 .r5, stS 3 .r7, ldS .r7 13, eorR .r7 .r1 .r7, eorR .r7 .r7 .r5, stS 13 .r7,
  ldS .r7 10, eorR .r7 .r7 .r4, ldS .r4 8, eorR .r4 .r4 .r12, eorR .r4 .r4 .r5, ldS .r12 5,
  stS 8 .r4, eorR .r4 .r1 .r12, eorR .r11 .r11 .lr, eorR .r11 .r11 .r5, eorR .r10 .r10 .lr,
  eorR .r10 .r10 .r5, ldS .lr 9, andR .r5 .r4 .lr, stS 2 .r4, andR .r4 .r0 .r3, eorR .r4 .r4 .r5,
  stS 6 .r0, andR .r0 .r6 .r2, eorR .r0 .r0 .r5, andR .r5 .r1 .r7, stS 11 .r1, ldS .r1 4,
  stS 10 .r6, ldS .r6 8, stS 18 .r7, andR .r7 .r1 .r6, eorR .r7 .r7 .r5, ldS .r1 15, ldS .r6 14,
  stS 19 .r2, andR .r2 .r1 .r6, eorR .r2 .r2 .r5, ldS .r5 7, andR .r1 .r5 .r11, andR .r5 .r12 .r10,
  eorR .r5 .r5 .r1, ldS .r12 17, stS 20 .r10, ldS .r10 1, stS 21 .r11, andR .r11 .r12 .r10,
  eorR .r11 .r11 .r1, eorR .r4 .r4 .r5, eorR .r0 .r0 .r11, eorR .r7 .r7 .r5, eorR .r2 .r2 .r11,
  ldS .r11 3, eorR .r4 .r4 .r11, ldS .r11 12, eorR .r0 .r0 .r11, ldS .r11 16, eorR .r7 .r7 .r11,
  ldS .r11 13, eorR .r2 .r2 .r11, eorR .r11 .r4 .r0, andR .r4 .r4 .r7, eorR .r5 .r2 .r4,
  andR .r1 .r11 .r5, eorR .r1 .r1 .r0, eorR .r12 .r7 .r2, eorR .r0 .r0 .r4, andR .r0 .r0 .r12,
  eorR .r0 .r0 .r2, eorR .r7 .r7 .r0, eorR .r12 .r5 .r0, andR .r2 .r2 .r12, eorR .r7 .r2 .r7,
  eorR .r5 .r5 .r2, andR .r5 .r1 .r5, eorR .r11 .r11 .r5, eorR .r5 .r11 .r7, eorR .r2 .r1 .r0,
  eorR .r12 .r1 .r11, eorR .r4 .r0 .r7, eorR .r10 .r2 .r5, andR .lr .r4 .lr, andR .r3 .r7 .r3,
  stS 9 .r3, ldS .r3 19, andR .r3 .r0 .r3, stS 19 .r3, ldS .r3 18, andR .r3 .r12 .r3, stS 18 .r3,
  ldS .r3 8, andR .r3 .r11 .r3, andR .r6 .r1 .r6, stS 14 .r3, ldS .r3 21, andR .r3 .r2 .r3,
  stS 21 .r6, ldS .r6 20, andR .r6 .r10 .r6, stS 20 .r6, ldS .r6 1, andR .r6 .r5 .r6, stS 1 .r6,
  ldS .r6 2, andR .r4 .r4 .r6, ldS .r6 6, andR .r7 .r7 .r6, ldS .r6 10, andR .r0 .r0 .r6,
  ldS .r6 11, andR .r12 .r12 .r6, ldS .r6 4, andR .r11 .r11 .r6, ldS .r6 15, andR .r1 .r1 .r6,
  ldS .r6 7, andR .r2 .r2 .r6, ldS .r6 5, andR .r10 .r10 .r6, ldS .r6 17, andR .r5 .r5 .r6,
  eorR .r4 .r4 .r2, eorR .r3 .r3 .r7, ldS .r6 21, eorR .r6 .lr .r6, stS 21 .lr, eorR .lr .r11 .r3,
  eorR .r1 .r1 .lr, ldS .lr 9, stS 17 .r7, ldS .r7 1, eorR .r7 .lr .r7, ldS .lr 20, stS 1 .r3,
  eorR .r3 .lr .r1, eorR .r5 .r5 .r4, ldS .lr 14, stS 5 .r1, eorR .r1 .lr .r6, eorR .lr .r3 .r5,
  stS 7 .lr, eorR .lr .r0 .r1, stS 15 .r3, eorR .r3 .r10 .r7, eorR .r4 .r4 .r3, ldS .r3 18,
  eorR .r6 .r3 .r6, eorR .r6 .r4 .r6, eorR .r0 .r0 .r5, eorR .r11 .r11 .r10, eorR .r12 .r12 .r2,
  ldS .r2 1, eorR .r2 .r2 .r1, eorR .r7 .r7 .lr, ldS .r1 5, eorR .r1 .r1 .r7, ldS .r7 0,
  eorR .r1 .r1 .r7, ldS .r10 17, eorR .r10 .r10 .r6, ldS .r6 19, ldS .r5 15, eorR .r6 .r6 .r5,
  ldS .r5 20, eorR .r5 .r5 .r10, eorR .r5 .r5 .r7, eorR .r11 .r11 .r12, eorR .r11 .r11 .r7,
  ldS .r12 21, ldS .r10 9, eorR .r12 .r12 .r10, ldS .r10 7, eorR .r3 .r3 .r10, eorR .r10 .r10 .r12,
  eorR .lr .lr .r6, eorR .r6 .lr .r7, ldS .lr 14, eorR .lr .lr .r3, eorR .r4 .r4 .r2,
  eorR .r4 .r4 .r7, movR .r7 .r11, stS 0 .r5, movR .r5 .r10, movR .r3 .r0, movR .r2 .lr, ldS .r0 0]

#guard sboxCode == compile sb VG.Impl.Sm4.Circuit.sbox sboxIns sboxOuts sboxFree onesSlot onesVar freshVar
  spillSlots

end VG.Impl.Sm4.Arm
