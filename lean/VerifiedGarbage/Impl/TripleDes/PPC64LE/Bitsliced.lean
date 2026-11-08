module

public import VerifiedGarbage.Impl.TripleDes.BitsliceLayout
public import VerifiedGarbage.Impl.Gather.PPC64LE
public import VerifiedGarbage.Impl.TripleDes.PPC64LE.Common
public import VerifiedGarbage.Spec.TripleDes
meta import VerifiedGarbage.Impl.TripleDes.BitsliceLayout
import VerifiedGarbage.Impl.TripleDes.PPC64LE.BitsliceAlloc
meta import VerifiedGarbage.Impl.TripleDes.PPC64LE.BitsliceAlloc

/-!
# Bitsliced Triple DES ECB on PPC64LE

`encrypt` and `decrypt` (schedule = r3, data = r4, n = r5, scratch = r6,
1024 bytes), as `Ecb.lean`'s, which they replace.

Constant-time Triple DES on 64 blocks at a time, bitsliced in 64-bit words
(Biham's bitslicing; the S-box circuits are Rusakov's, `BitsliceCircuit`),
as on RISC-V (`Impl/TripleDes/RISCV64/Bitsliced.lean`). The scratch buffer
holds the 64 state words (`stOff`), the transposition's masks
(`maskOff`) and the callee-saved registers the code uses (`savedOff`).

* The scratch buffer moves to `r10`, the schedule to `r7` and the count of
  blocks left to `r8`; `r11` holds all ones, as the circuits' NOT and the
  key's complement need.
* Up to 64 blocks are copied into the state words a doubleword at a time
  (`Gather.PPC64LE.copyWords`: the model's doubleword accesses need no
  alignment) and transposed in place, so that word `j` holds bit `j` of
  every block (`BitsliceLayout`); IP only renames words. The words of the
  other lanes hold whatever they held: their results are not stored.
* A round loads its key into `r9`, complements it and steps the key pointer
  `r3`. S-box `j`'s input `i` is key bit `inBit j i` as a mask (the
  complemented bit, shifted to the bottom, minus one), XORed with the state
  word of `E`. Each S-box's circuit then runs in registers (`BitsliceAlloc`),
  and its four outputs are XORed into the state words of `L` that P sends
  them to. Rounds alternate between reading the words of `R` (`.ba`) and of
  `L` (`.ab`), so no word moves; a pass of sixteen rounds, eight times both
  (counted in `r5`), ends by exchanging the halves, as DES's swap and the
  next pass's IP do.
* The three passes are unrolled, each with its schedule component and key
  direction.
* The state is transposed back and the blocks copied out; the data pointer
  `r4` and the blocks left `r8` advance.

The scratch buffer's frame zeroes it after the code
(`Proof/TripleDes/PPC64LE/Frame.lean`). Every address and branch depends
only on the pointers, `n` and the loop counters, which stay in registers
(memory is secret to the analysis of constant time).
-/

@[expose] public section

namespace VG.Impl.TripleDes.PPC64LE.Bitslice

open VG.PPC64LE VG.Impl.TripleDes.Bitslice
open VG.Impl.TripleDes.PPC64LE (rr)
open VG.Spec.TripleDes (Direction)

/-! ## Registers and the scratch buffer -/

/-- The scratch buffer's base (the argument `r6`, moved), the schedule, the
blocks left, all ones and the batch's blocks. -/
def base : Reg := .r10
def sched : Reg := .r7
def left : Reg := .r8
def ones : Reg := .r11
def batchN : Reg := .r12
/-- The round key's pointer, the pairs of rounds left, the round key and a
temporary for the state words. -/
def keyPtr : Reg := .r3
def pairs : Reg := .r5
def key : Reg := .r9
def tmp : Reg := .r0

/-- State word `j`. -/
def stOff (j : Nat) : Nat := 8 * j
/-- The transposition's six masks. -/
def maskOff : Nat := 512
/-- The saved registers. -/
def savedOff : Nat := 560

/-- The registers the code saves, and their offsets from `savedOff`. -/
def saved : List (Reg × Nat) :=
  [(.r2, 0), (.r14, 8), (.r15, 16), (.r16, 24), (.r17, 32), (.r18, 40), (.r19, 48), (.r20, 56),
   (.r21, 64), (.r22, 72), (.r23, 80), (.r24, 88), (.r25, 96), (.r26, 104), (.r27, 112),
   (.r28, 120), (.r29, 128), (.r30, 136), (.r31, 144)]

/-! ## S-boxes -/

def inRegs : List Reg := [.r12, .r14, .r15, .r16, .r17, .r18]
def freeRegs : List Reg :=
  [.r6, .r2, .r19, .r20, .r21, .r22, .r23, .r24, .r25, .r26, .r27, .r28, .r29, .r30, .r31]
def inReg (i : Nat) : Reg := inRegs.getD i .r12

/-! The code of the S-boxes, as `compile` allocates it for their circuits. It is written
out (and `#guard` checks that it is what `compile` produces) so that the kernel, which
evaluates the code in the proofs, does not have to run the allocator. -/

/-- The code of S-box 1. -/
def sboxCode0 : List Instr := [
  .logic .or .r6 .r18 .r14, .logic .xor .r6 .r6 .r14, .logic .xor .r2 .r15 .r6,
  .logic .or .r19 .r16 .r12, .logic .xor .r20 .r18 .r16, .logic .and .r21 .r19 .r20,
  .logic .xor .r22 .r15 .r21, .logic .or .r23 .r22 .r2, .logic .xor .r23 .r23 .r2,
  .logic .xor .r24 .r14 .r12, .logic .xor .r25 .r16 .r24, .logic .xor .r25 .r25 .r11,
  .logic .and .r25 .r25 .r2, .logic .or .r21 .r12 .r21, .logic .xor .r25 .r25 .r21,
  .logic .or .r21 .r25 .r23, .logic .xor .r21 .r21 .r23, .logic .or .r12 .r18 .r12,
  .logic .or .r26 .r25 .r12, .logic .xor .r22 .r22 .r11, .logic .and .r22 .r22 .r14,
  .logic .xor .r27 .r26 .r22, .logic .or .r15 .r15 .r12, .logic .xor .r15 .r15 .r12,
  .logic .xor .r15 .r22 .r15, .logic .xor .r20 .r20 .r11, .logic .and .r20 .r20 .r24,
  .logic .or .r15 .r15 .r20, .logic .or .r16 .r16 .r6, .logic .xor .r16 .r16 .r6,
  .logic .xor .r6 .r2 .r26, .logic .or .r6 .r6 .r16, .logic .xor .r6 .r6 .r16,
  .logic .xor .r16 .r6 .r11, .logic .and .r25 .r19 .r25, .logic .xor .r16 .r16 .r25,
  .logic .or .r27 .r27 .r17, .logic .xor .r27 .r27 .r17, .logic .xor .r27 .r27 .r16,
  .logic .xor .r6 .r24 .r6, .logic .or .r22 .r22 .r6, .logic .xor .r22 .r19 .r22,
  .logic .xor .r18 .r18 .r22, .logic .xor .r16 .r16 .r18, .logic .or .r23 .r23 .r17,
  .logic .xor .r23 .r23 .r16, .logic .xor .r19 .r19 .r26, .logic .or .r19 .r15 .r19,
  .logic .xor .r19 .r18 .r19, .logic .or .r24 .r24 .r16, .logic .xor .r24 .r19 .r24,
  .logic .or .r16 .r21 .r17, .logic .xor .r16 .r16 .r24, .logic .or .r14 .r14 .r2,
  .logic .or .r14 .r14 .r19, .logic .xor .r14 .r14 .r19, .logic .and .r21 .r21 .r18,
  .logic .xor .r14 .r14 .r21, .logic .or .r14 .r14 .r17, .logic .xor .r14 .r14 .r15]

/-- The code of S-box 2. -/
def sboxCode1 : List Instr := [
  .logic .xor .r6 .r17 .r14, .logic .or .r2 .r18 .r12, .logic .xor .r2 .r2 .r12,
  .logic .xor .r2 .r2 .r11, .logic .and .r2 .r2 .r14, .logic .or .r19 .r17 .r2,
  .logic .or .r20 .r6 .r12, .logic .xor .r20 .r20 .r12, .logic .and .r21 .r18 .r6,
  .logic .xor .r14 .r14 .r21, .logic .or .r21 .r14 .r20, .logic .xor .r21 .r21 .r20,
  .logic .and .r22 .r16 .r12, .logic .xor .r2 .r2 .r20, .logic .and .r2 .r19 .r2,
  .logic .or .r20 .r2 .r22, .logic .xor .r20 .r20 .r22, .logic .and .r23 .r16 .r2,
  .logic .xor .r18 .r18 .r11, .logic .xor .r18 .r23 .r18, .logic .xor .r12 .r12 .r6,
  .logic .or .r24 .r12 .r22, .logic .xor .r24 .r24 .r22, .logic .xor .r25 .r18 .r24,
  .logic .xor .r20 .r20 .r11, .logic .and .r20 .r20 .r15, .logic .xor .r20 .r20 .r25,
  .logic .or .r17 .r17 .r24, .logic .xor .r17 .r17 .r24, .logic .xor .r14 .r14 .r17,
  .logic .or .r18 .r18 .r14, .logic .xor .r18 .r18 .r14, .logic .xor .r16 .r16 .r12,
  .logic .xor .r18 .r18 .r16, .logic .or .r24 .r19 .r15, .logic .xor .r24 .r24 .r15,
  .logic .xor .r24 .r24 .r18, .logic .xor .r23 .r23 .r17, .logic .or .r16 .r16 .r23,
  .logic .xor .r19 .r19 .r25, .logic .or .r22 .r22 .r19, .logic .xor .r23 .r16 .r22,
  .logic .xor .r2 .r2 .r25, .logic .xor .r18 .r18 .r2, .logic .and .r22 .r22 .r18,
  .logic .and .r6 .r6 .r16, .logic .xor .r22 .r22 .r6, .logic .or .r6 .r22 .r15,
  .logic .xor .r6 .r6 .r23, .logic .or .r22 .r22 .r14, .logic .xor .r22 .r22 .r14,
  .logic .or .r12 .r12 .r19, .logic .xor .r22 .r22 .r12, .logic .or .r21 .r21 .r15,
  .logic .xor .r21 .r21 .r22]

/-- The code of S-box 3. -/
def sboxCode2 : List Instr := [
  .logic .or .r6 .r18 .r17, .logic .xor .r6 .r6 .r17, .logic .xor .r2 .r16 .r12,
  .logic .or .r19 .r6 .r2, .logic .xor .r20 .r15 .r12, .logic .or .r21 .r20 .r18,
  .logic .xor .r21 .r21 .r18, .logic .xor .r22 .r19 .r21, .logic .xor .r23 .r17 .r2,
  .logic .or .r24 .r23 .r12, .logic .xor .r24 .r24 .r12, .logic .xor .r19 .r19 .r24,
  .logic .or .r24 .r22 .r19, .logic .xor .r24 .r24 .r19, .logic .and .r25 .r12 .r22,
  .logic .or .r25 .r15 .r25, .logic .and .r25 .r18 .r25, .logic .xor .r25 .r23 .r25,
  .logic .or .r26 .r22 .r14, .logic .xor .r26 .r26 .r14, .logic .xor .r26 .r26 .r25,
  .logic .and .r2 .r2 .r20, .logic .xor .r20 .r18 .r15, .logic .xor .r27 .r19 .r20,
  .logic .or .r27 .r16 .r27, .logic .or .r27 .r27 .r2, .logic .xor .r27 .r27 .r2,
  .logic .or .r21 .r21 .r20, .logic .or .r20 .r25 .r21, .logic .xor .r20 .r20 .r21,
  .logic .and .r12 .r15 .r12, .logic .or .r2 .r12 .r17, .logic .xor .r2 .r2 .r17,
  .logic .xor .r20 .r20 .r2, .logic .and .r19 .r19 .r20, .logic .or .r12 .r23 .r12,
  .logic .or .r12 .r12 .r19, .logic .xor .r12 .r12 .r19, .logic .xor .r18 .r18 .r12,
  .logic .and .r27 .r27 .r14, .logic .xor .r27 .r27 .r18, .logic .xor .r22 .r22 .r11,
  .logic .or .r17 .r17 .r22, .logic .or .r16 .r16 .r17, .logic .xor .r23 .r23 .r16,
  .logic .xor .r21 .r21 .r23, .logic .xor .r24 .r24 .r11, .logic .and .r24 .r24 .r14,
  .logic .xor .r24 .r24 .r21, .logic .and .r15 .r15 .r22, .logic .xor .r25 .r25 .r15,
  .logic .or .r23 .r23 .r25, .logic .xor .r6 .r6 .r18, .logic .xor .r23 .r23 .r6,
  .logic .or .r20 .r20 .r14, .logic .xor .r20 .r20 .r23]

/-- The code of S-box 4. -/
def sboxCode3 : List Instr := [
  .logic .xor .r18 .r18 .r16, .logic .xor .r16 .r16 .r14, .logic .or .r6 .r17 .r15,
  .logic .xor .r6 .r14 .r6, .logic .xor .r6 .r6 .r11, .logic .and .r6 .r6 .r16,
  .logic .or .r2 .r16 .r17, .logic .xor .r2 .r2 .r17, .logic .xor .r19 .r15 .r2,
  .logic .or .r20 .r18 .r19, .logic .or .r20 .r20 .r6, .logic .xor .r20 .r20 .r6,
  .logic .xor .r21 .r17 .r20, .logic .and .r19 .r19 .r21, .logic .or .r16 .r16 .r19,
  .logic .xor .r16 .r16 .r19, .logic .xor .r18 .r18 .r21, .logic .xor .r16 .r16 .r11,
  .logic .and .r16 .r16 .r18, .logic .xor .r6 .r6 .r16, .logic .xor .r17 .r17 .r15,
  .logic .or .r14 .r14 .r2, .logic .xor .r18 .r18 .r14, .logic .or .r14 .r18 .r17,
  .logic .xor .r14 .r14 .r17, .logic .xor .r20 .r20 .r14, .logic .or .r14 .r12 .r6,
  .logic .xor .r14 .r14 .r6, .logic .xor .r14 .r14 .r20, .logic .xor .r20 .r20 .r11,
  .logic .or .r2 .r6 .r12, .logic .xor .r2 .r2 .r12, .logic .xor .r2 .r2 .r20,
  .logic .xor .r6 .r6 .r20, .logic .or .r6 .r6 .r17, .logic .xor .r6 .r6 .r17,
  .logic .or .r19 .r19 .r6, .logic .xor .r18 .r18 .r19, .logic .or .r19 .r21 .r12,
  .logic .xor .r19 .r19 .r18, .logic .and .r12 .r12 .r21, .logic .xor .r12 .r12 .r18]

/-- The code of S-box 5. -/
def sboxCode4 : List Instr := [
  .logic .or .r6 .r18 .r16, .logic .or .r2 .r6 .r12, .logic .xor .r2 .r2 .r12,
  .logic .xor .r19 .r18 .r2, .logic .xor .r20 .r16 .r19, .logic .or .r21 .r15 .r20,
  .logic .or .r2 .r2 .r15, .logic .xor .r2 .r2 .r15, .logic .xor .r16 .r16 .r2,
  .logic .and .r2 .r14 .r16, .logic .or .r20 .r18 .r20, .logic .xor .r2 .r2 .r20,
  .logic .xor .r2 .r15 .r2, .logic .xor .r12 .r12 .r2, .logic .or .r22 .r19 .r12,
  .logic .and .r23 .r14 .r22, .logic .xor .r24 .r19 .r23, .logic .and .r25 .r15 .r20,
  .logic .xor .r24 .r24 .r25, .logic .or .r22 .r22 .r18, .logic .xor .r22 .r22 .r18,
  .logic .xor .r25 .r16 .r22, .logic .xor .r14 .r14 .r21, .logic .xor .r25 .r25 .r11,
  .logic .and .r25 .r25 .r14, .logic .xor .r25 .r25 .r11, .logic .or .r25 .r25 .r17,
  .logic .xor .r25 .r25 .r17, .logic .xor .r25 .r25 .r2, .logic .or .r2 .r16 .r23,
  .logic .xor .r2 .r2 .r23, .logic .xor .r22 .r22 .r14, .logic .or .r22 .r24 .r22,
  .logic .or .r22 .r22 .r2, .logic .xor .r22 .r22 .r2, .logic .or .r2 .r21 .r22,
  .logic .xor .r2 .r2 .r22, .logic .and .r12 .r12 .r22, .logic .xor .r14 .r14 .r12,
  .logic .and .r20 .r16 .r20, .logic .or .r20 .r14 .r20, .logic .xor .r23 .r23 .r20,
  .logic .and .r23 .r23 .r17, .logic .xor .r23 .r23 .r24, .logic .xor .r18 .r18 .r6,
  .logic .xor .r22 .r22 .r18, .logic .and .r15 .r15 .r14, .logic .xor .r22 .r22 .r15,
  .logic .or .r2 .r2 .r17, .logic .xor .r2 .r2 .r22, .logic .xor .r16 .r21 .r16,
  .logic .or .r16 .r16 .r22, .logic .xor .r16 .r16 .r22, .logic .xor .r19 .r19 .r14,
  .logic .xor .r16 .r16 .r19, .logic .and .r21 .r21 .r17, .logic .xor .r21 .r21 .r16]

/-- The code of S-box 6. -/
def sboxCode5 : List Instr := [
  .logic .xor .r6 .r17 .r14, .logic .or .r2 .r17 .r12, .logic .and .r2 .r18 .r2,
  .logic .xor .r6 .r6 .r2, .logic .xor .r19 .r12 .r6, .logic .or .r20 .r14 .r19,
  .logic .xor .r20 .r20 .r19, .logic .and .r19 .r18 .r19, .logic .xor .r21 .r17 .r19,
  .logic .xor .r22 .r18 .r16, .logic .or .r23 .r21 .r22, .logic .xor .r24 .r6 .r23,
  .logic .and .r25 .r16 .r24, .logic .or .r26 .r25 .r12, .logic .xor .r26 .r26 .r12,
  .logic .or .r21 .r20 .r21, .logic .xor .r27 .r26 .r21, .logic .and .r28 .r27 .r15,
  .logic .xor .r28 .r28 .r24, .logic .xor .r23 .r17 .r23, .logic .or .r29 .r12 .r23,
  .logic .xor .r29 .r29 .r23, .logic .xor .r16 .r16 .r29, .logic .or .r29 .r14 .r25,
  .logic .xor .r29 .r29 .r25, .logic .or .r29 .r16 .r29, .logic .or .r17 .r17 .r22,
  .logic .xor .r27 .r27 .r17, .logic .or .r2 .r2 .r29, .logic .xor .r27 .r27 .r2,
  .logic .or .r24 .r18 .r24, .logic .and .r21 .r21 .r24, .logic .xor .r21 .r16 .r21,
  .logic .xor .r26 .r26 .r11, .logic .and .r26 .r26 .r21, .logic .or .r20 .r20 .r15,
  .logic .xor .r20 .r20 .r26, .logic .xor .r6 .r6 .r21, .logic .or .r14 .r14 .r6,
  .logic .xor .r14 .r14 .r6, .logic .xor .r17 .r17 .r11, .logic .xor .r23 .r23 .r17,
  .logic .xor .r14 .r14 .r23, .logic .or .r14 .r14 .r15, .logic .xor .r14 .r14 .r15,
  .logic .xor .r14 .r14 .r27, .logic .xor .r12 .r12 .r19, .logic .xor .r18 .r18 .r16,
  .logic .and .r12 .r12 .r18, .logic .xor .r25 .r25 .r23, .logic .xor .r12 .r12 .r25,
  .logic .or .r29 .r29 .r15, .logic .xor .r29 .r29 .r15, .logic .xor .r29 .r29 .r12]

/-- The code of S-box 7. -/
def sboxCode6 : List Instr := [
  .logic .xor .r6 .r15 .r14, .logic .xor .r2 .r16 .r6, .logic .and .r19 .r12 .r2,
  .logic .and .r20 .r15 .r6, .logic .xor .r21 .r17 .r20, .logic .and .r22 .r19 .r21,
  .logic .and .r23 .r12 .r20, .logic .xor .r24 .r16 .r23, .logic .or .r25 .r21 .r24,
  .logic .xor .r6 .r12 .r6, .logic .xor .r26 .r25 .r6, .logic .or .r27 .r18 .r22,
  .logic .xor .r27 .r27 .r22, .logic .xor .r27 .r27 .r26, .logic .xor .r2 .r2 .r11,
  .logic .and .r2 .r2 .r14, .logic .or .r26 .r21 .r2, .logic .xor .r24 .r19 .r24,
  .logic .xor .r26 .r26 .r24, .logic .xor .r19 .r19 .r6, .logic .or .r15 .r15 .r19,
  .logic .xor .r15 .r15 .r19, .logic .or .r6 .r21 .r15, .logic .xor .r6 .r6 .r15,
  .logic .xor .r14 .r14 .r24, .logic .xor .r6 .r6 .r14, .logic .or .r19 .r19 .r23,
  .logic .xor .r19 .r19 .r23, .logic .or .r15 .r15 .r19, .logic .xor .r25 .r17 .r25,
  .logic .and .r25 .r6 .r25, .logic .xor .r25 .r15 .r25, .logic .and .r23 .r25 .r18,
  .logic .xor .r23 .r23 .r6, .logic .or .r21 .r21 .r16, .logic .xor .r21 .r21 .r16,
  .logic .or .r19 .r19 .r21, .logic .or .r20 .r20 .r6, .logic .and .r19 .r19 .r20,
  .logic .xor .r25 .r25 .r19, .logic .xor .r2 .r2 .r15, .logic .and .r12 .r12 .r2,
  .logic .or .r22 .r22 .r12, .logic .xor .r19 .r19 .r22, .logic .or .r12 .r19 .r18,
  .logic .xor .r12 .r12 .r18, .logic .xor .r12 .r12 .r26, .logic .and .r17 .r17 .r22,
  .logic .xor .r26 .r26 .r11, .logic .xor .r17 .r17 .r26, .logic .xor .r19 .r19 .r17,
  .logic .or .r25 .r25 .r18, .logic .xor .r25 .r25 .r19]

/-- The code of S-box 8. -/
def sboxCode7 : List Instr := [
  .logic .or .r6 .r16 .r17, .logic .xor .r6 .r6 .r17, .logic .or .r2 .r14 .r16,
  .logic .xor .r2 .r2 .r16, .logic .xor .r2 .r15 .r2, .logic .and .r19 .r18 .r2,
  .logic .or .r20 .r19 .r6, .logic .xor .r20 .r20 .r6, .logic .or .r21 .r17 .r2,
  .logic .xor .r21 .r21 .r2, .logic .or .r22 .r18 .r21, .logic .or .r23 .r17 .r16,
  .logic .xor .r23 .r23 .r16, .logic .xor .r23 .r14 .r23, .logic .and .r24 .r22 .r23,
  .logic .or .r19 .r19 .r24, .logic .xor .r2 .r2 .r11, .logic .xor .r24 .r24 .r2,
  .logic .or .r16 .r16 .r22, .logic .xor .r16 .r16 .r22, .logic .xor .r24 .r24 .r16,
  .logic .xor .r6 .r6 .r24, .logic .or .r16 .r20 .r12, .logic .xor .r16 .r16 .r6,
  .logic .xor .r6 .r18 .r6, .logic .and .r22 .r14 .r6, .logic .xor .r24 .r17 .r24,
  .logic .xor .r22 .r22 .r24, .logic .xor .r21 .r21 .r22, .logic .xor .r22 .r19 .r22,
  .logic .or .r17 .r17 .r22, .logic .xor .r14 .r14 .r6, .logic .xor .r17 .r17 .r14,
  .logic .and .r19 .r19 .r12, .logic .xor .r19 .r19 .r17, .logic .xor .r23 .r23 .r21,
  .logic .or .r24 .r15 .r24, .logic .xor .r24 .r23 .r24, .logic .xor .r18 .r18 .r24,
  .logic .and .r18 .r18 .r12, .logic .xor .r18 .r18 .r21, .logic .or .r23 .r23 .r15,
  .logic .xor .r23 .r23 .r15, .logic .and .r17 .r17 .r23, .logic .xor .r20 .r20 .r24,
  .logic .xor .r17 .r17 .r20, .logic .or .r17 .r17 .r12, .logic .xor .r17 .r17 .r21]

/-- Each S-box's code and the registers of its outputs. -/
def sboxCompiled : Nat → List Instr × List Reg
  | 0 => (sboxCode0, [.r14, .r27, .r16, .r23])
  | 1 => (sboxCode1, [.r21, .r6, .r20, .r24])
  | 2 => (sboxCode2, [.r26, .r20, .r27, .r24])
  | 3 => (sboxCode3, [.r12, .r19, .r2, .r14])
  | 4 => (sboxCode4, [.r23, .r25, .r21, .r2])
  | 5 => (sboxCode5, [.r28, .r20, .r14, .r29])
  | 6 => (sboxCode6, [.r27, .r23, .r25, .r12])
  | _ => (sboxCode7, [.r18, .r19, .r16, .r17])

#guard (List.range 8).all fun j =>
  let c := compile (box j) inRegs (outputs j) freeRegs ones
  c.2.2 && (c.1, c.2.1) == sboxCompiled j

def sboxCode (j : Nat) : List Instr := (sboxCompiled j).1

/-- The registers of each S-box's outputs. -/
def outRegsTable : List (List Reg) := (List.range 8).map fun j => (sboxCompiled j).2

/-- The register of S-box `j`'s output `i`. -/
def outReg (j i : Nat) : Reg := (outRegsTable.getD j []).getD i .r12

/-- S-box `j`'s input `i`: key bit `inBit j i` as a mask (the complemented
key's bit, at the bottom, minus one), ⊕ the word of `E`. -/
def inputStep (ρ : Role) (j i : Nat) : List Instr :=
  [.lsl (inReg i) key (63 - inBit j i), .lsr .d (inReg i) (inReg i) 63, .subi (inReg i) (inReg i) 1,
   .load .d tmp base (stOff (readWord ρ (eBit (inBit j i)))), .logic .xor (inReg i) (inReg i) tmp]

def inputCode (ρ : Role) (j : Nat) : List Instr := (List.range 6).flatMap (inputStep ρ j)

/-- XOR S-box `j`'s outputs into their words. -/
def outputCode (ρ : Role) (j : Nat) : List Instr :=
  (List.range 4).flatMap fun i =>
    [.load .d tmp base (stOff (writeWord ρ (outBit j i))), .logic .xor tmp tmp (outReg j i),
     .store .d tmp base (stOff (writeWord ρ (outBit j i)))]

def sboxStep (ρ : Role) (j : Nat) : List Instr := inputCode ρ j ++ sboxCode j ++ outputCode ρ j

/-! ## Rounds and passes -/

/-- Load the round key, complement it and step the key pointer. -/
def keyLoad (d : Direction) : List Instr :=
  [.load .d key keyPtr 0, .logic .xor key key ones,
   if d = .encrypt then .addi keyPtr keyPtr 8 else .subi keyPtr keyPtr 8]

def round (d : Direction) (ρ : Role) : List Instr := keyLoad d ++ (List.range 8).flatMap (sboxStep ρ)

/-- Two rounds, and the count of pairs left. -/
def roundPair (d : Direction) : List Instr :=
  round d .ba ++ round d .ab ++ ([.subi pairs pairs 1] : List Instr)

/-- Exchange the halves. -/
def swapHalves : List Instr :=
  (List.range 32).flatMap fun q =>
    [.load .d .r12 base (stOff (lWord q)), .load .d .r14 base (stOff (rWord q)),
     .store .d .r14 base (stOff (lWord q)), .store .d .r12 base (stOff (rWord q))]

/-- A DES pass with schedule component `c`, in direction `d`. -/
def pass (c : Nat) (d : Direction) : Prog isa :=
  .seq (.block [.addi keyPtr sched (128 * c + if d = .encrypt then 0 else 120), .li pairs 8])
    (.seq (.loop (.block (roundPair d)) (.nonzero .d pairs)) (.block swapHalves))

/-- The three passes of the operation. -/
def passes : Direction → Prog isa
  | .encrypt => .seq (pass 0 .encrypt) (.seq (pass 1 .decrypt) (pass 2 .encrypt))
  | .decrypt => .seq (pass 2 .decrypt) (.seq (pass 1 .encrypt) (pass 0 .decrypt))

/-! ## Transposition -/

/-- The bits `p` with `p &&& s = 0`. -/
def swapMask (s : Nat) : BitVec 64 :=
  BitVec.ofNat 64 ((List.range 64).foldl (fun m p => if p &&& s = 0 then m ||| 2 ^ p else m) 0)

/-- The masks' shifts, in the order of their words. -/
def maskShifts : List Nat := [32, 16, 8, 4, 2, 1]

/-- `d := v` for a 64-bit constant: the high word with `lis` and `ori`,
shifted up by `sldi`, then the low word with `oris` and `ori`. -/
def movImm64 (d : Reg) (v : BitVec 64) : List Instr :=
  [.lis d (v.extractLsb' 48 16), .ori d d (v.extractLsb' 32 16), .lsl d d 32,
   .oris d d (v.extractLsb' 16 16), .ori d d (v.extractLsb' 0 16)]

/-- The masks to their words, through `r12`. -/
def storeMasks : List Instr :=
  (List.range 6).flatMap fun k =>
    movImm64 .r12 (swapMask (maskShifts.getD k 1)) ++ ([.store .d .r12 base (maskOff + 8 * k)] : List Instr)

/-- Exchange the bits `p + s` of `a` and `p` of `b` (`p &&& s = 0`), masked
by `m`: the bits moved up are rotated, since those at the top are zero. -/
def swapBits (a b t m : Reg) (s : Nat) : List Instr :=
  [.lsr .d t a s, .logic .xor t t b, .logic .and t t m, .logic .xor b b t,
   .rotr .d t t (64 - s), .logic .xor a a t]

def groupRegs : List Reg := [.r12, .r14, .r15, .r16, .r17, .r18, .r19, .r20]
def groupReg (k : Nat) : Reg := groupRegs.getD k .r12

/-- Three stages on eight words, the state words `word k`: the stage of
shift `unit * d` pairs the words `k` and `k + d`, for `d` = 4, 2, 1, with
the masks in `r21`, `r22` and `r23`. -/
def group (word : Nat → Nat) (unit : Nat) : List Instr :=
  (List.range 8).map (fun k => .load .d (groupReg k) base (stOff (word k))) ++
  ([(4, Reg.r21), (2, .r22), (1, .r23)].flatMap fun (d, m) =>
    ((List.range 8).filter (fun k => k &&& d = 0)).flatMap fun k =>
      swapBits (groupReg k) (groupReg (k + d)) .r24 m (unit * d)) ++
  (List.range 8).map (fun k => .store .d (groupReg k) base (stOff (word k)))

/-- The masks of words `3 h`–`3 h + 2` into `r21`–`r23`, from `r25`. -/
def masks (h : Nat) : List Instr :=
  [.load .d .r21 .r25 (24 * h), .load .d .r22 .r25 (24 * h + 8), .load .d .r23 .r25 (24 * h + 16)]

/-- Transpose the 64 state words in place, with `r25` at the masks: stages
32, 16, 8 on the words `i + 8 k` of each `i`, then 4, 2, 1 on the words
`8 g + k` of each `g`. -/
def transposeBody : List Instr :=
  masks 0 ++ (List.range 8).flatMap (fun i => group (fun k => i + 8 * k) 8) ++
  masks 1 ++ (List.range 8).flatMap (fun g => group (fun k => 8 * g + k) 1)

/-- `r25` at the masks, and the transposition. -/
def transpose : List Instr := .addi .r25 base maskOff :: transposeBody

/-! ## Batches -/

/-- The batch's blocks, `min(n, 64)`, into `r12`. -/
def batchBlocks : Prog isa :=
  .seq (.block [.lsr .d batchN left 6])
    (.ite (.zero .d batchN) (.block [rr batchN left]) (.block [.li batchN 64]))

/-- Copy the batch's doublewords from `src` to `dst` (`Gather.PPC64LE.copyWords`,
through `r0`, `r3`, `r5` and `r9`). -/
def copyBatch (src dst : Reg) : Prog isa :=
  .seq (.block [rr .r3 src, rr .r9 dst, rr .r5 batchN]) Gather.PPC64LE.copyWords

/-- One batch: the next `min(n, 64)` blocks into the state words, through
the three passes, and back; then the next blocks. -/
def batch (d : Direction) : Prog isa :=
  .seq batchBlocks (.seq (copyBatch .r4 base)
    (.seq (.block transpose) (.seq (passes d) (.seq (.block transpose) (.seq batchBlocks
      (.seq (copyBatch base .r4) (.block [rr .r4 .r9, .sub left left batchN])))))))

/-! ## The function -/

/-- The registers saved in the scratch buffer, the arguments moved, all ones
and the masks stored. -/
def setup : List Instr :=
  saved.map (fun (r, o) => .store .d r .r6 (savedOff + o)) ++
    [rr base .r6, rr sched .r3, rr left .r5, .lis ones 0xFFFF, .ori ones ones 0xFFFF] ++ storeMasks

/-- The registers back. -/
def finish : List Instr := saved.map fun (r, o) => .load .d r base (savedOff + o)

def ecb (d : Direction) : Prog isa :=
  .ite (.zero .d .r5) (.block [])
    (.seq (.block setup) (.seq (.loop (batch d) (.nonzero .d left)) (.block finish)))

def encrypt : Prog isa := ecb .encrypt
def decrypt : Prog isa := ecb .decrypt

end VG.Impl.TripleDes.PPC64LE.Bitslice
