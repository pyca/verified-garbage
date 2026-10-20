module

public import VerifiedGarbage.Impl.Camellia.Circuit
meta import VerifiedGarbage.Impl.Camellia.Circuit
public import VerifiedGarbage.Impl.Aes.Arm.Sbox
meta import VerifiedGarbage.Impl.Aes.Arm.Sbox
meta import VerifiedGarbage.Impl.Aes.Arm.Alloc

/-!
# The bitsliced Camellia S-box on ARMv7

The circuit `Circuit.sbox` (`SBOX1`) on the eight planes of the state
(`q j` holds bit `j` of 32 bytes: a word of eight blocks), in place: the
code that the AES allocator `compile` produces for it, with the
temporaries in `r10`–`r12` and `lr`, all ones in slot 0 of the scratch
buffer at `r8`, and spilling to its next slots (it uses slots 0–21). It is
written out (and `#guard` checks that it is what `compile` produces) so
that the kernel, which evaluates the code in the proofs, does not have to
run the allocator.
-/

@[expose] public section

namespace VG.Impl.Camellia.Arm

open VG.Arm VG.Impl.Aes.Arm

/-- The circuit's input `xᵢ` and output `sᵢ` are bit `7 - i`, in `q (7 - i)`. -/
def sboxIns : List (Nat × Reg) := (List.range 8).map fun i => (VG.Impl.Camellia.Circuit.x i, q (7 - i))
def sboxOuts : List (Nat × Reg) := (List.range 8).map fun i => (VG.Impl.Camellia.Circuit.s i, q (7 - i))

/-- The variables `compile` uses for all ones and for the gates it splits,
above the circuit's own. -/
def onesVar : Nat := 200
def freshVar : Nat := 201

/-- `SBOX1` on the state in `q 0 … q 7`, in place. -/
def sboxCode : List Instr := [
  .mov .r10 (.imm 0), .dp .sub .r10 .r10 (.imm 1), stS 0 .r10, eorR .r10 .r7 .r1, eorR .r11 .r5 .r3,
  eorR .r12 .r2 .r10, eorR .lr .r6 .r0, stS 1 .r10, eorR .r10 .r0 .r11, stS 2 .r10,
  eorR .r10 .r4 .r1, stS 3 .r10, eorR .r10 .r4 .r12, stS 4 .r10, eorR .r10 .r6 .r11, stS 5 .r11,
  eorR .r11 .r2 .lr, stS 6 .r11, eorR .r11 .r12 .lr, stS 7 .r11, eorR .r11 .r7 .r6, stS 8 .r10,
  eorR .r10 .r7 .lr, stS 9 .r7, ldS .r7 0, stS 10 .r2, eorR .r2 .r10 .r7, stS 11 .r10,
  eorR .r10 .r6 .r3, stS 12 .r2, eorR .r2 .r5 .r1, stS 13 .r6, eorR .r6 .r5 .r0, eorR .r5 .r5 .r12,
  eorR .lr .r4 .lr, eorR .r4 .r4 .r11, eorR .r3 .r3 .r0, eorR .r3 .r3 .r7, ldS .r0 10, ldS .r11 2,
  stS 14 .lr, eorR .lr .r0 .r11, stS 15 .r3, ldS .r3 3, eorR .r0 .r0 .r3, eorR .r0 .r0 .r7,
  stS 10 .r5, ldS .r5 8, stS 16 .lr, eorR .lr .r1 .r5, eorR .lr .lr .r7, stS 17 .lr, ldS .lr 1,
  stS 18 .r0, eorR .r0 .lr .r11, eorR .lr .lr .r5, ldS .r5 5, stS 8 .r0, eorR .r0 .r5 .r3,
  stS 1 .lr, ldS .lr 4, stS 19 .r4, eorR .r4 .r5 .lr, stS 20 .r4, ldS .r4 7, eorR .r5 .r5 .r4,
  stS 5 .r5, eorR .r5 .r12 .r11, eorR .r5 .r5 .r7, eorR .r12 .r12 .r10, eorR .r12 .r12 .r7,
  eorR .r11 .r11 .r3, eorR .r11 .r11 .r7, eorR .r6 .lr .r6, eorR .r6 .r6 .r7, ldS .r3 6,
  eorR .r2 .r3 .r2, eorR .r2 .r2 .r7, eorR .r3 .r3 .r0, eorR .r3 .r3 .r7, ldS .r0 9, ldS .r10 13,
  stS 6 .r12, eorR .r12 .r0 .r10, eorR .r12 .r12 .r7, eorR .r12 .r12 .r10, eorR .r0 .r0 .r1,
  eorR .r0 .r0 .r7, ldS .r1 18, ldS .r10 19, andR .r7 .r1 .r10, andR .r1 .r12 .r2, eorR .r1 .r1 .r7,
  stS 9 .r12, andR .r12 .lr .r6, eorR .r12 .r12 .r7, ldS .r7 16, andR .lr .r7 .r5, ldS .r7 1,
  stS 13 .r5, ldS .r5 10, stS 3 .r6, andR .r6 .r7 .r5, eorR .r6 .r6 .lr, ldS .r7 15,
  andR .r5 .r4 .r7, eorR .r5 .r5 .lr, ldS .lr 14, ldS .r4 20, andR .r7 .lr .r4, andR .lr .r11 .r3,
  eorR .lr .lr .r7, stS 2 .r11, ldS .r11 17, stS 21 .r3, ldS .r3 12, andR .r4 .r11 .r3,
  eorR .r4 .r4 .r7, eorR .r1 .r1 .lr, eorR .r12 .r12 .r4, eorR .r6 .r6 .lr, eorR .r5 .r5 .r4,
  ldS .r4 5, eorR .r1 .r1 .r4, ldS .r4 8, eorR .r12 .r12 .r4, eorR .r6 .r6 .r0, ldS .r0 6,
  eorR .r5 .r5 .r0, eorR .r0 .r1 .r12, andR .r1 .r1 .r6, eorR .r4 .r5 .r1, andR .lr .r0 .r4,
  eorR .lr .lr .r12, eorR .r7 .r6 .r5, eorR .r12 .r12 .r1, andR .r12 .r12 .r7, eorR .r12 .r12 .r5,
  eorR .r6 .r6 .r12, eorR .r7 .r4 .r12, andR .r5 .r5 .r7, eorR .r6 .r5 .r6, eorR .r4 .r4 .r5,
  andR .r4 .lr .r4, eorR .r0 .r0 .r4, eorR .r4 .r0 .r6, eorR .r5 .lr .r12, eorR .r7 .lr .r0,
  eorR .r1 .r12 .r6, eorR .r11 .r5 .r4, andR .r10 .r1 .r10, andR .r2 .r6 .r2, stS 19 .r10,
  ldS .r10 3, andR .r10 .r12 .r10, stS 3 .r10, ldS .r10 13, andR .r10 .r7 .r10, stS 13 .r10,
  ldS .r10 10, andR .r10 .r0 .r10, stS 10 .r10, ldS .r10 15, andR .r10 .lr .r10, stS 15 .r10,
  ldS .r10 20, andR .r10 .r5 .r10, stS 20 .r10, ldS .r10 21, andR .r10 .r11 .r10, andR .r3 .r4 .r3,
  stS 12 .r3, ldS .r3 18, andR .r1 .r1 .r3, ldS .r3 9, andR .r6 .r6 .r3, ldS .r3 4,
  andR .r12 .r12 .r3, ldS .r3 16, andR .r7 .r7 .r3, ldS .r3 1, andR .r0 .r0 .r3, ldS .r3 7,
  andR .lr .lr .r3, ldS .r3 14, andR .r5 .r5 .r3, ldS .r3 2, andR .r11 .r11 .r3, ldS .r3 17,
  andR .r4 .r4 .r3, eorR .r10 .r2 .r10, ldS .r3 13, stS 17 .r2, ldS .r2 15, eorR .r3 .r3 .r2,
  ldS .r2 20, stS 13 .r0, ldS .r0 12, stS 2 .r6, eorR .r6 .r2 .r0, ldS .r0 19, stS 14 .r1,
  eorR .r1 .r0 .r11, eorR .r12 .r12 .r10, stS 7 .r10, eorR .r10 .r7 .r3, stS 1 .r3,
  eorR .r3 .r5 .r6, stS 16 .r6, ldS .r6 3, eorR .lr .r6 .lr, eorR .r2 .r2 .r4, stS 20 .lr,
  ldS .lr 12, stS 4 .r4, ldS .r4 14, eorR .lr .lr .r4, stS 12 .lr, ldS .lr 2, eorR .r4 .r4 .lr,
  stS 14 .r4, ldS .r4 13, eorR .r4 .r4 .r10, eorR .r11 .r11 .r3, stS 13 .r11, eorR .r11 .r1 .r12,
  eorR .r0 .r0 .r6, ldS .r6 17, stS 3 .r11, ldS .r11 10, eorR .r6 .r6 .r11, ldS .r11 15,
  eorR .r11 .r11 .r1, eorR .lr .lr .r2, eorR .r7 .r7 .r12, ldS .r12 7, eorR .r5 .r5 .r12,
  ldS .r12 4, ldS .r1 12, eorR .r12 .r12 .r1, stS 4 .r12, ldS .r12 1, stS 7 .r7, ldS .r7 14,
  eorR .r12 .r12 .r7, stS 1 .r11, ldS .r11 16, eorR .r11 .r11 .r0, ldS .r0 20, eorR .r10 .r10 .r0,
  eorR .r3 .r3 .r7, eorR .r0 .r0 .r1, eorR .r2 .r2 .r5, ldS .r5 13, eorR .r1 .r4 .r5, ldS .r7 3,
  eorR .r4 .r4 .r7, eorR .r5 .r5 .r12, ldS .r12 0, eorR .r5 .r5 .r12, eorR .r7 .r7 .lr,
  eorR .r7 .r7 .r12, ldS .lr 1, eorR .r6 .r6 .lr, ldS .lr 7, eorR .lr .lr .r0, eorR .lr .lr .r12,
  ldS .r0 4, eorR .r0 .r0 .r4, eorR .r0 .r0 .r12, eorR .r10 .r10 .r2, eorR .r3 .r3 .r6,
  eorR .r6 .r3 .r12, stS 0 .r7, movR .r7 .r10, movR .r4 .r11, movR .r3 .lr, ldS .r2 0, stS 11 .r1,
  movR .r1 .r0, ldS .r0 11]

#guard sboxCode == compile sb VG.Impl.Camellia.Circuit.sbox sboxIns sboxOuts sboxFree onesSlot onesVar
  freshVar spillSlots

end VG.Impl.Camellia.Arm
