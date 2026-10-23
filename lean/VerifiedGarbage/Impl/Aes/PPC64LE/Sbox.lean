module

public import VerifiedGarbage.Impl.Aes.Circuit
public import VerifiedGarbage.TCB.PPC64LE.Isa
import VerifiedGarbage.Impl.Aes.PPC64LE.Alloc
meta import VerifiedGarbage.Impl.Aes.PPC64LE.Alloc
public meta import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# The bitsliced AES S-box on PPC64LE

The circuit `Circuit.sbox` on the eight words of the bitsliced state
(`q j` holds bit `j` of 64 bytes: four blocks), in place, with the
temporaries in `r22`–`r30`, `r0` and `r9`, all ones in `r31`, and spilling
to the first slots of the scratch buffer at `r8`: the code that `compile`
allocates for it. It is written out (and `#guard` checks that it is what
`compile` produces) so that the kernel, which evaluates the code in the
proofs, does not have to run the allocator.
-/

@[expose] public section

namespace VG.Impl.Aes.PPC64LE

open VG.PPC64LE VG.Impl.Aes.Circuit

/-- The registers of the bitsliced state: word `j` is in `q j`. -/
def q : Nat → Reg
  | 0 => .r14 | 1 => .r15 | 2 => .r16 | 3 => .r17
  | 4 => .r18 | 5 => .r19 | 6 => .r20 | _ => .r21

/-- The scratch buffer's base. -/
def sb : Reg := .r8

/-- The registers the S-box may use for its temporaries, and the one it
sets to all ones. -/
def sboxFree : List Reg := [.r22, .r23, .r24, .r25, .r26, .r27, .r28, .r29, .r30, .r0, .r9]
def onesReg : Reg := .r31

/-- The variable of all ones, the variables `splitXnor` adds, and the slots
the S-box may spill to. -/
def onesVar : Nat := 124
def freshVar : Nat := 125
def spillSlots : List Nat := List.range 40

/-- The circuit's input `xᵢ` and output `sᵢ` are bit `7 - i`. -/
def sboxIns : List (Nat × Reg) := (List.range 8).map fun i => (x i, q (7 - i))
def sboxOuts : List (Nat × Reg) := (List.range 8).map fun i => (s i, q (7 - i))

/-! Short forms of the instructions, on slots of `sb`. -/
def movR (d n : Reg) : Instr := .logic .or d n n
def xorR (d n m : Reg) : Instr := .logic .xor d n m
def andR (d n m : Reg) : Instr := .logic .and d n m
def ldS (d : Reg) (k : Nat) : Instr := .load .d d sb (8 * k)
def stS (k : Nat) (r : Reg) : Instr := .store .d r sb (8 * k)

/-- The S-box on the state in `q 0 … q 7`, in place. -/
def sboxCode : List Instr := [
  .li .r31 0, .subi .r31 .r31 1, xorR .r22 .r18 .r16, xorR .r23 .r21 .r15, xorR .r24 .r21 .r18,
  xorR .r25 .r21 .r16, xorR .r19 .r20 .r19, xorR .r26 .r19 .r14, xorR .r18 .r26 .r18, xorR .r27
  .r23 .r22, xorR .r28 .r26 .r21, xorR .r15 .r26 .r15, xorR .r29 .r15 .r25, xorR .r17 .r17 .r27,
  xorR .r16 .r17 .r16, xorR .r17 .r17 .r20, xorR .r20 .r16 .r14, xorR .r30 .r16 .r19, xorR .r0
  .r17 .r24, xorR .r9 .r14 .r0, stS 0 .r31, xorR .r31 .r30 .r0, stS 1 .r17, xorR .r17 .r30 .r25,
  xorR .r19 .r19 .r0, stS 2 .r17, xorR .r17 .r23 .r19, xorR .r21 .r21 .r19, stS 3 .r21, andR
  .r21 .r27 .r16, stS 4 .r27, andR .r27 .r29 .r20, xorR .r27 .r27 .r21, stS 5 .r29, andR .r29
  .r18 .r14, xorR .r29 .r29 .r21, andR .r21 .r23 .r19, stS 6 .r23, andR .r23 .r15 .r26, xorR
  .r23 .r23 .r21, stS 7 .r15, andR .r15 .r28 .r9, xorR .r15 .r15 .r21, andR .r21 .r24 .r0, stS 8
  .r24, andR .r24 .r22 .r31, xorR .r24 .r24 .r21, stS 9 .r22, andR .r22 .r25 .r30, xorR .r22
  .r22 .r21, xorR .r27 .r27 .r24, xorR .r29 .r29 .r22, xorR .r23 .r23 .r24, xorR .r15 .r15 .r22,
  ldS .r22 1, xorR .r27 .r27 .r22, ldS .r22 2, xorR .r29 .r29 .r22, xorR .r23 .r23 .r17, ldS
  .r17 3, xorR .r15 .r15 .r17, xorR .r17 .r27 .r29, andR .r27 .r27 .r23, xorR .r22 .r15 .r27,
  andR .r24 .r17 .r22, xorR .r24 .r24 .r29, xorR .r21 .r23 .r15, xorR .r29 .r29 .r27, andR .r29
  .r29 .r21, xorR .r29 .r29 .r15, xorR .r23 .r23 .r29, xorR .r21 .r22 .r29, andR .r15 .r15 .r21,
  xorR .r23 .r15 .r23, xorR .r22 .r22 .r15, andR .r22 .r24 .r22, xorR .r17 .r17 .r22, xorR .r22
  .r17 .r23, xorR .r15 .r24 .r29, xorR .r21 .r24 .r17, xorR .r27 .r29 .r23, stS 3 .r25, xorR
  .r25 .r15 .r22, andR .r16 .r27 .r16, andR .r20 .r23 .r20, andR .r14 .r29 .r14, andR .r19 .r21
  .r19, andR .r26 .r17 .r26, andR .r9 .r24 .r9, andR .r0 .r15 .r0, andR .r31 .r25 .r31, andR
  .r30 .r22 .r30, stS 2 .r20, ldS .r20 4, andR .r27 .r27 .r20, ldS .r20 5, andR .r23 .r23 .r20,
  andR .r29 .r29 .r18, ldS .r18 6, andR .r21 .r21 .r18, ldS .r18 7, andR .r17 .r17 .r18, andR
  .r24 .r24 .r28, ldS .r28 8, andR .r15 .r15 .r28, ldS .r28 9, andR .r25 .r25 .r28, ldS .r28 3,
  andR .r22 .r22 .r28, xorR .r15 .r15 .r25, xorR .r29 .r23 .r29, xorR .r17 .r9 .r17, xorR .r27
  .r27 .r23, xorR .r23 .r14 .r21, xorR .r14 .r14 .r9, xorR .r30 .r31 .r30, xorR .r16 .r16 .r19,
  xorR .r0 .r0 .r31, xorR .r25 .r25 .r22, xorR .r21 .r21 .r17, xorR .r23 .r23 .r16, xorR .r22
  .r26 .r15, xorR .r19 .r19 .r0, xorR .r15 .r15 .r23, xorR .r24 .r24 .r23, xorR .r30 .r30 .r22,
  xorR .r27 .r27 .r22, xorR .r26 .r26 .r19, xorR .r24 .r24 .r30, ldS .r22 2, xorR .r22 .r22
  .r27, xorR .r19 .r19 .r27, xorR .r21 .r21 .r30, ldS .r30 0, xorR .r21 .r21 .r30, xorR .r17
  .r17 .r15, xorR .r17 .r17 .r30, xorR .r15 .r26 .r24, xorR .r18 .r16 .r22, xorR .r14 .r14 .r22,
  xorR .r16 .r29 .r24, xorR .r26 .r26 .r18, xorR .r20 .r26 .r30, xorR .r25 .r25 .r15, xorR .r25
  .r25 .r30, stS 0 .r21, movR .r21 .r19, movR .r19 .r25, stS 2 .r17, movR .r17 .r14, ldS .r15 0,
  ldS .r14 2]

#guard sboxCode == compile sb sbox sboxIns sboxOuts sboxFree onesReg onesVar freshVar spillSlots

end VG.Impl.Aes.PPC64LE
