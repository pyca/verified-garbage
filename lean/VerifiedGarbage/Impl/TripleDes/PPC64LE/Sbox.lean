module

public import VerifiedGarbage.Impl.TripleDes.Circuit
public import VerifiedGarbage.TCB.PPC64LE.Isa
meta import VerifiedGarbage.Impl.TripleDes.Circuit
import VerifiedGarbage.Impl.Aes.PPC64LE.Alloc
meta import VerifiedGarbage.Impl.Aes.PPC64LE.Alloc
public meta import VerifiedGarbage.TCB.PPC64LE.Isa
public import VerifiedGarbage.TCB.Code
meta import VerifiedGarbage.TCB.Code

/-!
# DES S-box circuits on PPC64LE

The circuit of S-box `i` (`Circuit.gates i`) on its six input bits, one in
the low bit of each of `r6`–`r11` (`q 0`–`q 5`), leaving its four output bits
in `q 0`–`q 3`, with the temporaries in `r20`–`r28` and `r0`, all ones in
`r12`, and spilling to slots 15–63 of the scratch buffer at `r5` (slots 0–14
hold the saved registers; `r29`–`r31` are left to the callers): the code that `compile` allocates for it. It is
written out (and `#guard` checks that it is what `compile` produces) so that
the kernel, which evaluates the code in the proofs, does not have to run the
allocator.
-/

@[expose] public section

namespace VG.Impl.TripleDes.PPC64LE

open VG.PPC64LE

def q : Nat → Reg
  | 0 => .r6 | 1 => .r7 | 2 => .r8 | 3 => .r9 | 4 => .r10 | _ => .r11

def sboxIns : List (Nat × Reg) := (List.range 6).map fun i => (i, q i)

def sboxOuts (i : Nat) : List (Nat × Reg) :=
  (List.range 4).map fun j => ((Circuit.outputs i).getD j 0, q j)

/-- The registers the S-boxes may use for their temporaries, and the one
they set to all ones. -/
def sboxFree : List Reg :=
  [.r20, .r21, .r22, .r23, .r24, .r25, .r26, .r27, .r28, .r0]
def onesReg : Reg := .r12

/-- The variable of all ones, the variables `splitXnor` adds (above every
variable of the circuits), and the slots the S-boxes may spill to. -/
def onesVar : Nat := 1000
def freshVar : Nat := 1001
def spillSlots : List Nat := List.range' 15 49

/-! Short forms of the instructions, on slots of the scratch buffer at `r5`. -/
def movR (d n : Reg) : Instr := .logic .or d n n
def xorR (d n m : Reg) : Instr := .logic .xor d n m
def andR (d n m : Reg) : Instr := .logic .and d n m
def ldS (d : Reg) (k : Nat) : Instr := .load .d d .r5 (8 * k)
def stS (k : Nat) (r : Reg) : Instr := .store .d r .r5 (8 * k)

/-- The code of S-box 1. -/
def sboxCode0 : List Instr := [
  .li .r12 0, .subi .r12 .r12 1, xorR .r20 .r6 .r6, xorR .r21 .r6 .r20, xorR .r21 .r21 .r12,
  andR .r22 .r10 .r21, xorR .r23 .r6 .r10, andR .r24 .r7 .r23, xorR .r24 .r22 .r24,
  xorR .r25 .r21 .r22, andR .r26 .r7 .r25, xorR .r26 .r6 .r26, andR .r26 .r11 .r26,
  xorR .r24 .r24 .r26, andR .r26 .r10 .r6, xorR .r27 .r26 .r20, xorR .r27 .r27 .r12,
  andR .r28 .r7 .r27, xorR .r0 .r26 .r28, stS 15 .r23, xorR .r23 .r10 .r20, xorR .r23 .r23 .r12,
  stS 16 .r6, xorR .r6 .r23 .r28, stS 17 .r28, andR .r28 .r11 .r6, xorR .r0 .r0 .r28,
  andR .r0 .r9 .r0, xorR .r24 .r24 .r0, andR .r10 .r7 .r10, xorR .r0 .r27 .r10,
  andR .r28 .r7 .r23, stS 18 .r10, xorR .r10 .r21 .r28, andR .r10 .r11 .r10, xorR .r0 .r0 .r10,
  andR .r10 .r7 .r21, stS 19 .r23, xorR .r23 .r25 .r10, andR .r23 .r11 .r23, andR .r23 .r9 .r23,
  xorR .r0 .r0 .r23, andR .r0 .r8 .r0, xorR .r24 .r24 .r0, xorR .r21 .r21 .r26,
  xorR .r26 .r21 .r28, xorR .r0 .r22 .r20, xorR .r0 .r0 .r12, andR .r21 .r7 .r21,
  xorR .r21 .r0 .r21, andR .r23 .r11 .r21, xorR .r26 .r26 .r23, xorR .r23 .r25 .r20,
  xorR .r23 .r23 .r12, xorR .r28 .r23 .r28, stS 20 .r24, andR .r24 .r7 .r22, xorR .r22 .r22 .r24,
  andR .r22 .r11 .r22, xorR .r24 .r28 .r22, andR .r24 .r9 .r24, xorR .r26 .r26 .r24,
  xorR .r21 .r21 .r22, ldS .r22 16, andR .r24 .r7 .r22, stS 21 .r6, xorR .r6 .r0 .r24,
  andR .r6 .r11 .r6, stS 22 .r12, xorR .r12 .r25 .r6, andR .r12 .r9 .r12, xorR .r21 .r21 .r12,
  andR .r21 .r8 .r21, xorR .r26 .r26 .r21, xorR .r21 .r25 .r24, andR .r12 .r11 .r28,
  xorR .r21 .r21 .r12, xorR .r27 .r27 .r10, andR .r23 .r7 .r23, xorR .r0 .r0 .r23,
  andR .r0 .r11 .r0, xorR .r27 .r27 .r0, andR .r27 .r9 .r27, xorR .r21 .r21 .r27, ldS .r27 17,
  andR .r0 .r11 .r27, xorR .r28 .r28 .r0, xorR .r22 .r22 .r24, xorR .r22 .r22 .r6,
  andR .r22 .r9 .r22, xorR .r28 .r28 .r22, andR .r28 .r8 .r28, xorR .r21 .r21 .r28, ldS .r28 15,
  xorR .r28 .r28 .r20, ldS .r22 22, xorR .r28 .r28 .r22, xorR .r28 .r28 .r7, xorR .r27 .r27 .r20,
  xorR .r27 .r27 .r22, andR .r27 .r11 .r27, xorR .r27 .r28 .r27, ldS .r6 21, xorR .r6 .r6 .r20,
  xorR .r6 .r6 .r22, andR .r6 .r11 .r6, ldS .r22 19, xorR .r22 .r22 .r6, andR .r22 .r9 .r22,
  xorR .r27 .r27 .r22, ldS .r22 18, xorR .r22 .r25 .r22, andR .r22 .r11 .r22, xorR .r24 .r24 .r22,
  xorR .r25 .r25 .r7, andR .r11 .r11 .r25, xorR .r28 .r28 .r11, andR .r9 .r9 .r28,
  xorR .r24 .r24 .r9, andR .r8 .r8 .r24, xorR .r9 .r27 .r8, ldS .r6 20, movR .r7 .r26,
  movR .r8 .r21]

/-- The code of S-box 2. -/
def sboxCode1 : List Instr := [
  .li .r12 0, .subi .r12 .r12 1, xorR .r20 .r6 .r6, xorR .r21 .r6 .r6, xorR .r21 .r21 .r12,
  xorR .r22 .r11 .r20, xorR .r22 .r22 .r12, andR .r23 .r7 .r11, xorR .r24 .r11 .r23,
  andR .r25 .r6 .r24, xorR .r25 .r22 .r25, xorR .r26 .r23 .r20, xorR .r26 .r26 .r12,
  andR .r27 .r6 .r26, xorR .r28 .r24 .r27, andR .r28 .r10 .r28, xorR .r25 .r25 .r28,
  andR .r0 .r7 .r22, stS 15 .r27, xorR .r27 .r22 .r0, xorR .r24 .r24 .r20, xorR .r24 .r24 .r12,
  stS 16 .r22, andR .r22 .r6 .r24, stS 17 .r26, xorR .r26 .r27 .r22, stS 18 .r22,
  xorR .r22 .r27 .r20, xorR .r22 .r22 .r12, stS 19 .r27, andR .r27 .r6 .r22, xorR .r27 .r7 .r27,
  andR .r27 .r10 .r27, xorR .r26 .r26 .r27, andR .r26 .r9 .r26, xorR .r25 .r25 .r26,
  andR .r26 .r6 .r0, xorR .r26 .r21 .r26, xorR .r27 .r11 .r7, stS 20 .r0, andR .r0 .r6 .r27,
  stS 21 .r21, xorR .r21 .r7 .r0, andR .r21 .r10 .r21, xorR .r26 .r26 .r21, andR .r26 .r8 .r26,
  xorR .r25 .r25 .r26, xorR .r27 .r27 .r20, xorR .r27 .r27 .r12, andR .r23 .r6 .r23,
  xorR .r26 .r27 .r23, xorR .r24 .r24 .r0, andR .r24 .r10 .r24, xorR .r26 .r26 .r24,
  xorR .r22 .r22 .r28, andR .r22 .r9 .r22, xorR .r26 .r26 .r22, ldS .r22 19, andR .r28 .r6 .r22,
  xorR .r28 .r11 .r28, andR .r28 .r10 .r28, ldS .r24 17, xorR .r28 .r24 .r28, ldS .r0 16,
  andR .r21 .r6 .r0, xorR .r22 .r22 .r21, andR .r11 .r10 .r11, xorR .r22 .r22 .r11,
  andR .r22 .r9 .r22, xorR .r28 .r28 .r22, andR .r28 .r8 .r28, xorR .r26 .r26 .r28,
  xorR .r28 .r27 .r6, xorR .r28 .r28 .r10, xorR .r22 .r24 .r23, andR .r22 .r10 .r22,
  xorR .r22 .r6 .r22, andR .r22 .r9 .r22, xorR .r28 .r28 .r22, andR .r6 .r6 .r7, ldS .r7 21,
  xorR .r7 .r7 .r6, ldS .r22 15, xorR .r24 .r24 .r22, andR .r24 .r10 .r24, xorR .r7 .r7 .r24,
  andR .r6 .r9 .r6, xorR .r7 .r7 .r6, andR .r7 .r8 .r7, xorR .r28 .r28 .r7, xorR .r27 .r27 .r22,
  ldS .r22 18, andR .r22 .r10 .r22, xorR .r27 .r27 .r22, xorR .r22 .r23 .r20, xorR .r22 .r22 .r12,
  xorR .r0 .r0 .r21, andR .r0 .r10 .r0, xorR .r22 .r22 .r0, andR .r9 .r9 .r22, xorR .r27 .r27 .r9,
  ldS .r9 20, xorR .r9 .r9 .r23, xorR .r20 .r9 .r20, xorR .r20 .r20 .r12, andR .r10 .r10 .r20,
  xorR .r9 .r9 .r10, andR .r8 .r8 .r9, xorR .r9 .r27 .r8, movR .r6 .r25, movR .r7 .r26,
  movR .r8 .r28]

/-- The code of S-box 3. -/
def sboxCode2 : List Instr := [
  .li .r12 0, .subi .r12 .r12 1, xorR .r20 .r6 .r6, xorR .r21 .r6 .r6, xorR .r21 .r21 .r12,
  xorR .r22 .r11 .r20, xorR .r22 .r22 .r12, andR .r23 .r10 .r22, xorR .r24 .r11 .r23,
  andR .r25 .r10 .r11, xorR .r26 .r22 .r25, andR .r27 .r6 .r26, xorR .r28 .r24 .r27,
  xorR .r0 .r26 .r20, xorR .r0 .r0 .r12, andR .r25 .r6 .r25, stS 15 .r24, xorR .r24 .r0 .r25,
  stS 16 .r0, andR .r0 .r7 .r24, xorR .r0 .r28 .r0, stS 17 .r28, andR .r28 .r7 .r26,
  xorR .r24 .r24 .r28, andR .r24 .r9 .r24, xorR .r0 .r0 .r24, andR .r11 .r6 .r11,
  xorR .r21 .r21 .r11, andR .r24 .r7 .r22, xorR .r21 .r21 .r24, andR .r25 .r9 .r25,
  xorR .r21 .r21 .r25, andR .r21 .r8 .r21, xorR .r0 .r0 .r21, xorR .r21 .r22 .r10,
  xorR .r27 .r21 .r27, xorR .r25 .r23 .r20, xorR .r25 .r25 .r12, andR .r24 .r6 .r23,
  xorR .r24 .r25 .r24, andR .r28 .r7 .r24, stS 18 .r0, xorR .r0 .r27 .r28, stS 19 .r26,
  xorR .r26 .r10 .r20, xorR .r26 .r26 .r12, stS 20 .r21, andR .r21 .r6 .r26, xorR .r10 .r10 .r21,
  stS 21 .r26, andR .r26 .r6 .r22, xorR .r22 .r22 .r26, andR .r22 .r7 .r22, xorR .r10 .r10 .r22,
  andR .r10 .r9 .r10, xorR .r0 .r0 .r10, ldS .r10 17, xorR .r10 .r10 .r20, xorR .r10 .r10 .r12,
  xorR .r27 .r27 .r20, xorR .r27 .r27 .r12, andR .r27 .r7 .r27, xorR .r10 .r10 .r27, ldS .r27 15,
  xorR .r22 .r27 .r20, xorR .r22 .r22 .r12, andR .r27 .r6 .r22, stS 17 .r22, xorR .r22 .r25 .r27,
  stS 22 .r27, xorR .r27 .r26 .r20, xorR .r27 .r27 .r12, andR .r27 .r7 .r27, xorR .r22 .r22 .r27,
  andR .r22 .r9 .r22, xorR .r10 .r10 .r22, andR .r10 .r8 .r10, xorR .r0 .r0 .r10,
  andR .r10 .r6 .r25, ldS .r22 16, xorR .r22 .r22 .r10, xorR .r10 .r24 .r20, xorR .r10 .r10 .r12,
  andR .r10 .r7 .r10, xorR .r22 .r22 .r10, xorR .r24 .r24 .r28, andR .r24 .r9 .r24,
  xorR .r22 .r22 .r24, xorR .r21 .r23 .r21, xorR .r21 .r21 .r27, andR .r27 .r7 .r11,
  xorR .r23 .r23 .r27, andR .r23 .r9 .r23, xorR .r21 .r21 .r23, andR .r21 .r8 .r21,
  xorR .r22 .r22 .r21, xorR .r25 .r25 .r11, xorR .r25 .r25 .r7, ldS .r11 20, xorR .r11 .r11 .r20,
  xorR .r11 .r11 .r12, andR .r6 .r6 .r11, ldS .r11 21, xorR .r11 .r11 .r6, andR .r11 .r7 .r11,
  ldS .r6 19, xorR .r6 .r6 .r11, andR .r6 .r9 .r6, xorR .r25 .r25 .r6, ldS .r6 15,
  xorR .r6 .r6 .r26, ldS .r11 17, ldS .r12 22, xorR .r12 .r11 .r12, andR .r12 .r7 .r12,
  xorR .r6 .r6 .r12, andR .r7 .r7 .r26, xorR .r11 .r11 .r7, andR .r9 .r9 .r11, xorR .r6 .r6 .r9,
  andR .r8 .r8 .r6, xorR .r9 .r25 .r8, ldS .r6 18, movR .r7 .r0, movR .r8 .r22]

/-- The code of S-box 4. -/
def sboxCode3 : List Instr := [
  .li .r12 0, .subi .r12 .r12 1, xorR .r20 .r6 .r6, xorR .r21 .r6 .r6, xorR .r21 .r21 .r12,
  xorR .r22 .r9 .r20, xorR .r22 .r22 .r12, andR .r23 .r7 .r9, xorR .r24 .r22 .r23,
  andR .r25 .r11 .r24, xorR .r26 .r22 .r25, xorR .r27 .r9 .r7, xorR .r28 .r27 .r20,
  xorR .r28 .r28 .r12, andR .r0 .r11 .r28, stS 15 .r25, xorR .r25 .r27 .r0, andR .r25 .r10 .r25,
  xorR .r26 .r26 .r25, xorR .r25 .r7 .r20, xorR .r25 .r25 .r12, stS 16 .r9, xorR .r9 .r7 .r0,
  stS 17 .r0, andR .r0 .r10 .r9, stS 18 .r6, xorR .r6 .r25 .r0, andR .r6 .r8 .r6,
  xorR .r26 .r26 .r6, xorR .r6 .r24 .r20, xorR .r6 .r6 .r12, andR .r6 .r11 .r6, xorR .r6 .r28 .r6,
  andR .r6 .r10 .r6, xorR .r9 .r9 .r6, xorR .r23 .r23 .r20, xorR .r23 .r23 .r12,
  andR .r6 .r7 .r22, xorR .r21 .r21 .r6, stS 19 .r0, andR .r0 .r11 .r21, xorR .r23 .r23 .r0,
  andR .r27 .r10 .r27, xorR .r23 .r23 .r27, andR .r23 .r8 .r23, xorR .r9 .r9 .r23, ldS .r23 18,
  stS 20 .r27, andR .r27 .r23 .r9, xorR .r26 .r26 .r27, andR .r27 .r11 .r6, xorR .r28 .r28 .r27,
  stS 21 .r26, xorR .r26 .r0 .r20, xorR .r26 .r26 .r12, andR .r26 .r10 .r26, xorR .r26 .r28 .r26,
  stS 22 .r11, xorR .r11 .r6 .r0, stS 23 .r6, ldS .r6 16, stS 24 .r25, ldS .r25 17,
  xorR .r25 .r6 .r25, andR .r25 .r10 .r25, xorR .r11 .r11 .r25, andR .r11 .r8 .r11,
  xorR .r26 .r26 .r11, xorR .r9 .r9 .r20, xorR .r9 .r9 .r12, andR .r9 .r23 .r9,
  xorR .r26 .r26 .r9, xorR .r24 .r24 .r0, andR .r22 .r10 .r22, xorR .r24 .r24 .r22,
  xorR .r7 .r7 .r25, andR .r7 .r8 .r7, xorR .r24 .r24 .r7, xorR .r28 .r28 .r20,
  xorR .r28 .r28 .r12, xorR .r21 .r21 .r27, andR .r21 .r10 .r21, xorR .r28 .r28 .r21, ldS .r21 24,
  ldS .r7 15, xorR .r21 .r21 .r7, ldS .r25 20, xorR .r21 .r21 .r25, andR .r21 .r8 .r21,
  xorR .r28 .r28 .r21, andR .r21 .r23 .r28, xorR .r24 .r24 .r21, ldS .r21 23, ldS .r25 22,
  xorR .r25 .r21 .r25, xorR .r6 .r6 .r21, xorR .r6 .r6 .r27, andR .r10 .r10 .r6,
  xorR .r25 .r25 .r10, xorR .r7 .r7 .r20, xorR .r7 .r7 .r12, ldS .r10 19, xorR .r7 .r7 .r10,
  andR .r8 .r8 .r7, xorR .r25 .r25 .r8, xorR .r28 .r28 .r20, xorR .r28 .r28 .r12,
  andR .r23 .r23 .r28, xorR .r9 .r25 .r23, ldS .r6 21, movR .r7 .r26, movR .r8 .r24]

/-- The code of S-box 5. -/
def sboxCode4 : List Instr := [
  .li .r12 0, .subi .r12 .r12 1, xorR .r20 .r6 .r6, xorR .r21 .r6 .r6, xorR .r21 .r21 .r12,
  xorR .r22 .r9 .r20, xorR .r22 .r22 .r12, andR .r23 .r22 .r11, xorR .r24 .r21 .r23,
  xorR .r6 .r6 .r20, xorR .r6 .r6 .r12, andR .r25 .r6 .r24, xorR .r26 .r11 .r25,
  xorR .r27 .r11 .r20, xorR .r27 .r27 .r12, andR .r28 .r22 .r27, xorR .r0 .r27 .r28,
  xorR .r10 .r10 .r20, xorR .r10 .r10 .r12, stS 15 .r25, andR .r25 .r10 .r0, xorR .r25 .r26 .r25,
  stS 16 .r26, xorR .r26 .r27 .r23, stS 17 .r21, andR .r21 .r10 .r26, xorR .r21 .r9 .r21,
  xorR .r8 .r8 .r20, xorR .r8 .r8 .r12, andR .r21 .r8 .r21, xorR .r25 .r25 .r21,
  andR .r21 .r6 .r27, xorR .r21 .r22 .r21, stS 18 .r9, xorR .r9 .r11 .r22, andR .r23 .r6 .r23,
  xorR .r23 .r9 .r23, andR .r23 .r10 .r23, xorR .r21 .r21 .r23, xorR .r23 .r0 .r20,
  xorR .r23 .r23 .r12, andR .r23 .r6 .r23, stS 19 .r22, xorR .r22 .r27 .r6, andR .r22 .r10 .r22,
  xorR .r23 .r23 .r22, andR .r23 .r8 .r23, xorR .r21 .r21 .r23, xorR .r7 .r7 .r20,
  xorR .r7 .r7 .r12, andR .r21 .r7 .r21, xorR .r25 .r25 .r21, andR .r21 .r6 .r0,
  xorR .r23 .r24 .r21, xorR .r23 .r23 .r10, xorR .r22 .r28 .r20, xorR .r22 .r22 .r12, stS 20 .r25,
  andR .r25 .r6 .r22, stS 21 .r24, ldS .r24 17, xorR .r24 .r24 .r25, andR .r28 .r6 .r28,
  stS 17 .r12, andR .r12 .r10 .r28, xorR .r24 .r24 .r12, andR .r24 .r8 .r24, xorR .r23 .r23 .r24,
  xorR .r28 .r26 .r28, andR .r28 .r10 .r28, ldS .r24 18, xorR .r28 .r24 .r28, andR .r11 .r6 .r11,
  xorR .r27 .r27 .r11, andR .r12 .r10 .r27, xorR .r12 .r25 .r12, andR .r12 .r8 .r12,
  xorR .r28 .r28 .r12, andR .r28 .r7 .r28, xorR .r23 .r23 .r28, xorR .r28 .r0 .r6,
  xorR .r28 .r28 .r10, xorR .r22 .r22 .r21, xorR .r21 .r9 .r25, andR .r21 .r10 .r21,
  xorR .r22 .r22 .r21, andR .r22 .r8 .r22, xorR .r28 .r28 .r22, xorR .r22 .r9 .r20, ldS .r21 17,
  xorR .r22 .r22 .r21, andR .r12 .r6 .r22, xorR .r0 .r0 .r12, andR .r0 .r8 .r0, stS 22 .r23,
  ldS .r23 21, xorR .r23 .r23 .r0, andR .r23 .r7 .r23, xorR .r28 .r28 .r23, ldS .r23 19,
  xorR .r23 .r23 .r25, ldS .r25 16, andR .r25 .r10 .r25, xorR .r23 .r23 .r25, xorR .r25 .r26 .r6,
  andR .r25 .r10 .r25, xorR .r27 .r27 .r25, andR .r27 .r8 .r27, xorR .r23 .r23 .r27, ldS .r27 15,
  xorR .r22 .r22 .r27, andR .r6 .r6 .r24, xorR .r9 .r9 .r6, andR .r9 .r10 .r9, xorR .r22 .r22 .r9,
  xorR .r26 .r26 .r20, xorR .r26 .r26 .r21, xorR .r26 .r26 .r12, xorR .r11 .r11 .r20,
  xorR .r11 .r11 .r21, andR .r10 .r10 .r11, xorR .r26 .r26 .r10, andR .r8 .r8 .r26,
  xorR .r22 .r22 .r8, andR .r7 .r7 .r22, xorR .r9 .r23 .r7, ldS .r6 20, ldS .r7 22, movR .r8 .r28]

/-- The code of S-box 6. -/
def sboxCode5 : List Instr := [
  .li .r12 0, .subi .r12 .r12 1, xorR .r20 .r6 .r6, xorR .r21 .r6 .r6, xorR .r21 .r21 .r12,
  xorR .r22 .r10 .r20, xorR .r22 .r22 .r12, andR .r23 .r9 .r22, xorR .r24 .r23 .r7,
  xorR .r25 .r10 .r23, andR .r26 .r7 .r9, xorR .r27 .r25 .r26, andR .r27 .r8 .r27,
  xorR .r24 .r24 .r27, xorR .r27 .r26 .r20, xorR .r27 .r27 .r12, xorR .r28 .r9 .r20,
  xorR .r28 .r28 .r12, andR .r0 .r7 .r28, stS 15 .r26, xorR .r26 .r9 .r0, stS 16 .r28,
  andR .r28 .r8 .r26, xorR .r27 .r27 .r28, andR .r27 .r11 .r27, xorR .r24 .r24 .r27,
  xorR .r27 .r22 .r9, stS 17 .r26, andR .r26 .r7 .r27, stS 18 .r28, xorR .r28 .r23 .r26,
  andR .r28 .r8 .r28, andR .r9 .r9 .r10, stS 19 .r0, xorR .r0 .r22 .r9, stS 20 .r22,
  xorR .r22 .r27 .r20, xorR .r22 .r22 .r12, xorR .r22 .r22 .r26, andR .r22 .r8 .r22,
  xorR .r22 .r0 .r22, andR .r22 .r11 .r22, xorR .r28 .r28 .r22, andR .r28 .r6 .r28,
  xorR .r24 .r24 .r28, andR .r28 .r7 .r23, xorR .r22 .r9 .r28, andR .r10 .r7 .r10,
  xorR .r21 .r21 .r10, stS 21 .r24, andR .r24 .r8 .r21, xorR .r22 .r22 .r24, ldS .r24 19,
  xorR .r25 .r25 .r24, andR .r10 .r8 .r10, xorR .r25 .r25 .r10, andR .r25 .r11 .r25,
  xorR .r22 .r22 .r25, andR .r25 .r8 .r7, xorR .r21 .r21 .r25, ldS .r25 16, xorR .r25 .r25 .r28,
  stS 16 .r0, ldS .r0 20, stS 22 .r28, andR .r28 .r7 .r0, stS 23 .r10, andR .r10 .r8 .r28,
  xorR .r25 .r25 .r10, andR .r25 .r11 .r25, xorR .r21 .r21 .r25, andR .r21 .r6 .r21,
  xorR .r22 .r22 .r21, xorR .r27 .r27 .r24, ldS .r21 15, xorR .r0 .r0 .r21, andR .r0 .r8 .r0,
  xorR .r27 .r27 .r0, xorR .r0 .r23 .r20, xorR .r0 .r0 .r12, andR .r21 .r7 .r9,
  xorR .r21 .r0 .r21, andR .r26 .r8 .r26, xorR .r21 .r21 .r26, andR .r21 .r11 .r21,
  xorR .r27 .r27 .r21, ldS .r21 23, xorR .r21 .r21 .r20, xorR .r21 .r21 .r12, ldS .r12 22,
  xorR .r23 .r23 .r12, xorR .r9 .r9 .r7, andR .r9 .r8 .r9, xorR .r23 .r23 .r9,
  andR .r23 .r11 .r23, xorR .r21 .r21 .r23, andR .r21 .r6 .r21, xorR .r27 .r27 .r21, ldS .r21 16,
  xorR .r23 .r21 .r7, ldS .r9 18, xorR .r23 .r23 .r9, ldS .r9 17, andR .r12 .r11 .r9,
  xorR .r23 .r23 .r12, xorR .r24 .r0 .r24, andR .r24 .r8 .r24, xorR .r9 .r9 .r24,
  andR .r7 .r7 .r0, xorR .r0 .r0 .r7, xorR .r21 .r21 .r28, andR .r8 .r8 .r21, xorR .r0 .r0 .r8,
  andR .r11 .r11 .r0, xorR .r9 .r9 .r11, andR .r6 .r6 .r9, xorR .r9 .r23 .r6, ldS .r6 21,
  movR .r7 .r22, movR .r8 .r27]

/-- The code of S-box 7. -/
def sboxCode6 : List Instr := [
  .li .r12 0, .subi .r12 .r12 1, xorR .r20 .r6 .r6, xorR .r21 .r6 .r6, xorR .r21 .r21 .r12,
  xorR .r22 .r11 .r6, andR .r23 .r6 .r11, andR .r24 .r8 .r23, xorR .r25 .r22 .r24,
  xorR .r26 .r23 .r20, xorR .r26 .r26 .r12, andR .r27 .r8 .r26, xorR .r28 .r21 .r27,
  andR .r0 .r9 .r28, xorR .r25 .r25 .r0, xorR .r0 .r11 .r20, xorR .r0 .r0 .r12, stS 15 .r24,
  andR .r24 .r6 .r0, stS 16 .r0, andR .r0 .r8 .r24, stS 17 .r24, xorR .r24 .r21 .r0, stS 18 .r21,
  andR .r21 .r9 .r26, xorR .r24 .r24 .r21, andR .r24 .r10 .r24, xorR .r25 .r25 .r24,
  andR .r24 .r9 .r27, xorR .r28 .r28 .r24, andR .r24 .r8 .r6, xorR .r24 .r23 .r24,
  andR .r24 .r10 .r24, xorR .r28 .r28 .r24, andR .r28 .r7 .r28, xorR .r25 .r25 .r28,
  xorR .r28 .r23 .r8, xorR .r24 .r22 .r20, xorR .r24 .r24 .r12, stS 19 .r25, xorR .r25 .r24 .r0,
  andR .r25 .r9 .r25, xorR .r28 .r28 .r25, andR .r25 .r8 .r11, stS 20 .r21, ldS .r21 18,
  stS 21 .r22, xorR .r22 .r21 .r25, xorR .r23 .r11 .r23, xorR .r21 .r23 .r0, andR .r21 .r9 .r21,
  xorR .r22 .r22 .r21, andR .r22 .r10 .r22, xorR .r28 .r28 .r22, ldS .r22 16, stS 22 .r0,
  ldS .r0 17, stS 23 .r25, xorR .r25 .r22 .r0, xorR .r6 .r6 .r20, xorR .r6 .r6 .r12,
  andR .r6 .r8 .r6, xorR .r6 .r25 .r6, xorR .r6 .r6 .r21, andR .r21 .r8 .r24, stS 24 .r25,
  andR .r25 .r9 .r23, xorR .r21 .r21 .r25, andR .r21 .r10 .r21, xorR .r6 .r6 .r21,
  andR .r6 .r7 .r6, xorR .r28 .r28 .r6, xorR .r23 .r23 .r20, xorR .r23 .r23 .r12,
  andR .r22 .r8 .r22, xorR .r12 .r23 .r22, andR .r20 .r9 .r11, xorR .r12 .r12 .r20,
  xorR .r24 .r24 .r27, ldS .r27 23, xorR .r26 .r26 .r27, andR .r26 .r9 .r26, xorR .r24 .r24 .r26,
  andR .r24 .r10 .r24, xorR .r12 .r12 .r24, ldS .r24 21, andR .r24 .r8 .r24, andR .r24 .r9 .r24,
  ldS .r26 18, xorR .r26 .r26 .r24, ldS .r24 22, andR .r24 .r10 .r24, xorR .r26 .r26 .r24,
  andR .r26 .r7 .r26, xorR .r12 .r12 .r26, xorR .r0 .r0 .r27, ldS .r26 20, xorR .r0 .r0 .r26,
  xorR .r22 .r11 .r22, ldS .r26 24, andR .r8 .r8 .r26, xorR .r26 .r26 .r8, andR .r26 .r9 .r26,
  xorR .r22 .r22 .r26, andR .r22 .r10 .r22, xorR .r0 .r0 .r22, ldS .r22 15, xorR .r23 .r23 .r22,
  xorR .r11 .r11 .r8, andR .r9 .r9 .r11, xorR .r23 .r23 .r9, xorR .r27 .r27 .r20,
  andR .r10 .r10 .r27, xorR .r23 .r23 .r10, andR .r7 .r7 .r23, xorR .r9 .r0 .r7, ldS .r6 19,
  movR .r7 .r28, movR .r8 .r12]

/-- The code of S-box 8. -/
def sboxCode7 : List Instr := [
  .li .r12 0, .subi .r12 .r12 1, xorR .r20 .r6 .r6, xorR .r21 .r6 .r6, xorR .r21 .r21 .r12,
  xorR .r22 .r6 .r20, xorR .r22 .r22 .r12, xorR .r23 .r11 .r22, xorR .r9 .r9 .r20,
  xorR .r9 .r9 .r12, xorR .r24 .r23 .r9, xorR .r7 .r7 .r20, xorR .r7 .r7 .r12, xorR .r24 .r24 .r7,
  andR .r25 .r9 .r6, andR .r26 .r22 .r11, andR .r27 .r9 .r26, xorR .r28 .r22 .r27,
  andR .r28 .r7 .r28, xorR .r28 .r25 .r28, xorR .r10 .r10 .r20, xorR .r10 .r10 .r12,
  andR .r28 .r10 .r28, xorR .r24 .r24 .r28, xorR .r28 .r11 .r20, xorR .r28 .r28 .r12,
  andR .r0 .r22 .r28, stS 15 .r6, xorR .r6 .r21 .r0, stS 16 .r23, xorR .r23 .r6 .r25,
  andR .r23 .r7 .r23, xorR .r22 .r22 .r23, xorR .r23 .r11 .r26, stS 17 .r6, andR .r6 .r9 .r23,
  xorR .r21 .r21 .r6, stS 18 .r25, andR .r25 .r7 .r28, xorR .r21 .r21 .r25, andR .r21 .r10 .r21,
  xorR .r22 .r22 .r21, xorR .r8 .r8 .r20, xorR .r8 .r8 .r12, andR .r22 .r8 .r22,
  xorR .r24 .r24 .r22, xorR .r22 .r26 .r20, xorR .r22 .r22 .r12, xorR .r21 .r22 .r6,
  xorR .r23 .r23 .r20, xorR .r23 .r23 .r12, stS 19 .r24, andR .r24 .r9 .r23, xorR .r28 .r28 .r24,
  andR .r28 .r7 .r28, xorR .r21 .r21 .r28, xorR .r28 .r27 .r20, xorR .r28 .r28 .r12, stS 20 .r23,
  andR .r23 .r7 .r27, xorR .r23 .r28 .r23, andR .r23 .r10 .r23, xorR .r21 .r21 .r23,
  xorR .r23 .r11 .r0, stS 21 .r6, ldS .r6 18, xorR .r6 .r23 .r6, stS 18 .r28, ldS .r28 16,
  andR .r28 .r7 .r28, stS 16 .r26, xorR .r26 .r6 .r28, xorR .r6 .r6 .r20, xorR .r6 .r6 .r12,
  xorR .r23 .r23 .r20, xorR .r23 .r23 .r12, andR .r23 .r7 .r23, xorR .r6 .r6 .r23,
  andR .r6 .r10 .r6, xorR .r26 .r26 .r6, andR .r26 .r8 .r26, xorR .r21 .r21 .r26,
  xorR .r26 .r0 .r27, andR .r6 .r9 .r22, xorR .r11 .r11 .r6, andR .r6 .r7 .r11,
  xorR .r26 .r26 .r6, xorR .r24 .r22 .r24, andR .r24 .r10 .r24, xorR .r26 .r26 .r24,
  xorR .r22 .r22 .r25, ldS .r24 16, xorR .r27 .r24 .r27, xorR .r27 .r27 .r25, andR .r27 .r10 .r27,
  xorR .r22 .r22 .r27, andR .r22 .r8 .r22, xorR .r26 .r26 .r22, ldS .r22 18, andR .r22 .r7 .r22,
  xorR .r11 .r11 .r22, andR .r9 .r9 .r0, xorR .r24 .r24 .r9, ldS .r9 15, ldS .r0 21,
  xorR .r9 .r9 .r0, andR .r9 .r7 .r9, xorR .r9 .r24 .r9, andR .r9 .r10 .r9, xorR .r11 .r11 .r9,
  ldS .r9 17, xorR .r9 .r9 .r28, xorR .r24 .r24 .r20, xorR .r24 .r24 .r12, ldS .r12 20,
  andR .r7 .r7 .r12, xorR .r24 .r24 .r7, andR .r10 .r10 .r24, xorR .r9 .r9 .r10, andR .r8 .r8 .r9,
  xorR .r9 .r11 .r8, ldS .r6 19, movR .r7 .r21, movR .r8 .r26]

/-- Six input planes; scratch slots 0–14 are reserved. -/
def sboxCode : Nat → List Instr
  | 0 => sboxCode0 | 1 => sboxCode1 | 2 => sboxCode2 | 3 => sboxCode3
  | 4 => sboxCode4 | 5 => sboxCode5 | 6 => sboxCode6 | _ => sboxCode7

#guard (List.range 8).all fun i => sboxCode i ==
  VG.Impl.Aes.PPC64LE.compile .r5 (Circuit.gates i) sboxIns (sboxOuts i) sboxFree onesReg
    onesVar freshVar spillSlots

def sbox0 : Prog isa := .block (sboxCode 0)
def sbox1 : Prog isa := .block (sboxCode 1)
def sbox2 : Prog isa := .block (sboxCode 2)
def sbox3 : Prog isa := .block (sboxCode 3)
def sbox4 : Prog isa := .block (sboxCode 4)
def sbox5 : Prog isa := .block (sboxCode 5)
def sbox6 : Prog isa := .block (sboxCode 6)
def sbox7 : Prog isa := .block (sboxCode 7)

end VG.Impl.TripleDes.PPC64LE
