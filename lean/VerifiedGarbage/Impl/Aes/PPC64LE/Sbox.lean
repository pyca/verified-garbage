module

public import VerifiedGarbage.Impl.Aes.PPC64LE.Alloc
meta import VerifiedGarbage.Impl.Aes.PPC64LE.Alloc

/-!
# Bit slices on PPC64LE: registers, short forms, and the AES S-box

The registers of eight 64-bit slices (`q j`), the scratch buffer's base
(`sb`), short forms of the instructions on them and on slots of the buffer,
and the circuit `Circuit.sbox` on the slices (bit `j` of 64 bytes is in
`q j`), in place, spilling to slots of the scratch buffer: the code
`compile` allocates for it, written out (`#guard` checks that it is that) so
that the kernel need not run the allocator.
-/

@[expose] public section

namespace VG.Impl.Aes.PPC64LE

open VG.PPC64LE VG.Impl.Aes.Circuit

/-- The slices. -/
def q : Nat → Reg
  | 0 => .r14 | 1 => .r15 | 2 => .r16 | 3 => .r17
  | 4 => .r18 | 5 => .r19 | 6 => .r20 | _ => .r21

/-- The scratch buffer's base. -/
def sb : Reg := .r8

/-- Temporaries. -/
def t0 : Reg := .r22
def t1 : Reg := .r23
def t2 : Reg := .r24
def u7 : Reg := .r25

/-- The address of a round key. -/
def kp : Reg := .r4

/-- All ones, as a circuit starts. -/
def onesReg : Reg := .r31

/-- The registers circuits may use besides these. -/
def sboxFree : List Reg := [.r22, .r23, .r24, .r25, .r26, .r27, .r28, .r29, .r30, .r0, .r9]

/-- The slots circuits may spill to. -/
def spillSlots : List Nat := List.range 48

/-- The variable of all ones, and the first that `splitXnor` adds. -/
def onesVar : Nat := 150
def freshVar : Nat := 151

def sboxIns : List (Nat × Reg) := (List.range 8).map fun i => (x i, q i)
def sboxOuts : List (Nat × Reg) := (List.range 8).map fun i => (s i, q i)

/-! Short forms. -/

def movR (d n : Reg) : Instr := .logic .or d n n
def xorR (d n m : Reg) : Instr := .logic .xor d n m
def andR (d n m : Reg) : Instr := .logic .and d n m
def orR (d n m : Reg) : Instr := .logic .or d n m
def rorI (d n : Reg) (k : Nat) : Instr := .rotr .d d n k
def shrI (d n : Reg) (k : Nat) : Instr := .lsr .d d n k
def stS (k : Nat) (r : Reg) : Instr := .store .d r sb (8 * k)
def ldS (r : Reg) (k : Nat) : Instr := .load .d r sb (8 * k)

/-- The S-box on the slices in `q 0 … q 7`, in place. -/
def sboxCode : List Instr := [
  .li .r31 0, .subi .r31 .r31 1, xorR .r16 .r19 .r16, xorR .r22 .r16 .r15, xorR .r23 .r22 .r20,
  xorR .r14 .r22 .r14, xorR .r17 .r23 .r17, xorR .r17 .r17 .r21, xorR .r24 .r17 .r16,
  xorR .r25 .r24 .r14, xorR .r19 .r25 .r19, xorR .r26 .r14 .r21, xorR .r27 .r25 .r18,
  xorR .r28 .r25 .r23, xorR .r29 .r19 .r21, xorR .r30 .r27 .r29, andR .r0 .r27 .r25,
  xorR .r9 .r24 .r18, xorR .r18 .r17 .r18, xorR .r17 .r27 .r17, stS 0 .r25, andR .r25 .r29 .r23,
  stS 1 .r31, andR .r31 .r9 .r17, xorR .r15 .r9 .r15, xorR .r25 .r31 .r25, stS 2 .r27,
  andR .r27 .r30 .r28, xorR .r31 .r31 .r27, xorR .r27 .r28 .r15, stS 3 .r17, xorR .r17 .r9 .r19,
  stS 4 .r9, andR .r9 .r26 .r15, stS 5 .r26, andR .r26 .r17 .r27, xorR .r9 .r31 .r9,
  xorR .r31 .r31 .r26, andR .r26 .r14 .r18, stS 6 .r15, andR .r15 .r21 .r22, xorR .r9 .r9 .r0,
  xorR .r31 .r31 .r26, xorR .r0 .r0 .r15, xorR .r26 .r25 .r26, xorR .r15 .r29 .r20,
  xorR .r9 .r9 .r16, xorR .r0 .r0 .r25, andR .r25 .r19 .r20, xorR .r0 .r0 .r15,
  xorR .r26 .r26 .r25, xorR .r25 .r19 .r22, xorR .r26 .r26 .r25, xorR .r31 .r31 .r24,
  xorR .r24 .r9 .r31, andR .r25 .r0 .r9, xorR .r15 .r31 .r25, xorR .r25 .r26 .r25,
  andR .r25 .r25 .r24, xorR .r0 .r0 .r26, xorR .r25 .r31 .r25, xorR .r9 .r9 .r25,
  andR .r21 .r25 .r21, xorR .r24 .r15 .r25, andR .r31 .r31 .r24, xorR .r9 .r31 .r9,
  andR .r29 .r9 .r29, xorR .r31 .r15 .r31, andR .r15 .r0 .r15, xorR .r26 .r26 .r15,
  andR .r23 .r9 .r23, andR .r31 .r26 .r31, xorR .r31 .r31 .r0, xorR .r0 .r26 .r31,
  andR .r17 .r0 .r17, xorR .r15 .r26 .r25, andR .r18 .r15 .r18, andR .r0 .r0 .r27,
  andR .r30 .r31 .r30, andR .r14 .r15 .r14, xorR .r14 .r14 .r17, andR .r28 .r31 .r28,
  xorR .r31 .r31 .r9, xorR .r15 .r15 .r31, xorR .r17 .r21 .r17, xorR .r9 .r25 .r9,
  andR .r25 .r25 .r22, xorR .r0 .r0 .r28, xorR .r18 .r0 .r18, ldS .r22 3, andR .r22 .r15 .r22,
  xorR .r0 .r0 .r22, xorR .r0 .r0 .r25, xorR .r23 .r23 .r25, andR .r20 .r9 .r20,
  andR .r9 .r9 .r19, xorR .r0 .r0 .r20, ldS .r20 4, andR .r15 .r15 .r20, ldS .r20 6,
  andR .r20 .r26 .r20, xorR .r15 .r15 .r30, xorR .r28 .r28 .r20, ldS .r20 2, andR .r20 .r31 .r20,
  ldS .r19 5, andR .r26 .r26 .r19, xorR .r20 .r15 .r20, xorR .r28 .r28 .r23, xorR .r17 .r17 .r20,
  xorR .r20 .r20 .r26, ldS .r19 1, xorR .r20 .r20 .r19, ldS .r25 0, andR .r31 .r31 .r25,
  xorR .r16 .r17 .r9, xorR .r17 .r0 .r31, xorR .r14 .r14 .r15, xorR .r14 .r14 .r28,
  xorR .r14 .r14 .r19, xorR .r28 .r28 .r20, xorR .r22 .r20 .r22, xorR .r22 .r22 .r19,
  xorR .r23 .r22 .r23, xorR .r22 .r22 .r16, xorR .r26 .r14 .r26, xorR .r26 .r26 .r19,
  xorR .r26 .r26 .r29, xorR .r22 .r22 .r18, xorR .r22 .r22 .r19, xorR .r23 .r23 .r31,
  xorR .r26 .r26 .r30, xorR .r18 .r26 .r21, movR .r15 .r20, movR .r19 .r28, movR .r20 .r22,
  movR .r21 .r23]

#guard sboxCode == compile sb sbox sboxIns sboxOuts sboxFree onesReg onesVar freshVar spillSlots

end VG.Impl.Aes.PPC64LE
