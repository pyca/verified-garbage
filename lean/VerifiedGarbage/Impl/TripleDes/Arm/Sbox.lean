module

public import VerifiedGarbage.Impl.TripleDes.Circuit
meta import VerifiedGarbage.Impl.TripleDes.Circuit
public import VerifiedGarbage.Impl.Aes.Arm.Alloc
meta import VerifiedGarbage.Impl.Aes.Arm.Alloc

@[expose] public section

namespace VG.Impl.TripleDes.Arm

open VG.Arm

def q : Nat → Reg
  | 0 => .r4 | 1 => .r5 | 2 => .r6 | 3 => .r7 | 4 => .r8 | _ => .r12

def sboxIns : List (Nat × Reg) := (List.range 6).map fun i => (i, q i)

def sboxOuts (i : Nat) : List (Nat × Reg) :=
  (List.range 4).map fun j => ((Circuit.outputs i).getD j 0, q j)

/-! The code of the S-boxes, as `compile` allocates it for their circuits. It is written
out (and `#guard` checks that it is what `compile` produces) so that the kernel, which
evaluates the code in the proofs, does not have to run the allocator. -/

/-! Short forms of the instructions, on slots of the scratch buffer at `r2`. -/
def movR (d n : Reg) : Instr := .mov d (.reg n)
def eorR (d n m : Reg) : Instr := .dp .eor d n (.reg m)
def andR (d n m : Reg) : Instr := .dp .and d n (.reg m)
def ldS (d : Reg) (k : Nat) : Instr := .ldr d .r2 (4 * k)
def stS (k : Nat) (r : Reg) : Instr := .str r .r2 (4 * k)

/-- The code of S-box 1. -/
def sboxCode0 : List Instr := [
  .mov .lr (.imm 0), .dp .sub .lr .lr (.imm 1), stS 15 .lr, eorR .lr .r4 .r4, stS 16 .r6,
  eorR .r6 .r4 .lr, stS 17 .r7, ldS .r7 15, eorR .r6 .r6 .r7, andR .r7 .r8 .r6, stS 18 .lr,
  eorR .lr .r4 .r8, stS 19 .r8, andR .r8 .r5 .lr, eorR .r8 .r7 .r8, stS 20 .lr, eorR .lr .r6 .r7,
  stS 21 .r7, andR .r7 .r5 .lr, eorR .r7 .r4 .r7, andR .r7 .r12 .r7, eorR .r8 .r8 .r7, ldS .r7 19,
  stS 22 .lr, andR .lr .r7 .r4, stS 23 .r4, ldS .r4 18, stS 24 .r6, eorR .r6 .lr .r4, stS 25 .r8,
  ldS .r8 15, eorR .r6 .r6 .r8, stS 26 .r12, andR .r12 .r5 .r6, stS 27 .r6, eorR .r6 .lr .r12,
  stS 28 .lr, eorR .lr .r7 .r4, eorR .lr .lr .r8, eorR .r8 .lr .r12, stS 29 .r12, ldS .r12 26,
  andR .r4 .r12 .r8, eorR .r6 .r6 .r4, ldS .r4 17, andR .r6 .r4 .r6, stS 30 .r8, ldS .r8 25,
  eorR .r8 .r8 .r6, andR .r7 .r5 .r7, ldS .r6 27, stS 19 .r8, eorR .r8 .r6 .r7, stS 25 .r7,
  andR .r7 .r5 .lr, stS 31 .lr, ldS .lr 24, eorR .r6 .lr .r7, andR .r6 .r12 .r6, eorR .r8 .r8 .r6,
  andR .r6 .r5 .lr, stS 32 .r5, ldS .r5 22, stS 33 .r7, eorR .r7 .r5 .r6, andR .r7 .r12 .r7,
  andR .r7 .r4 .r7, eorR .r8 .r8 .r7, ldS .r7 16, andR .r8 .r7 .r8, stS 34 .r6, ldS .r6 19,
  eorR .r6 .r6 .r8, ldS .r8 28, eorR .lr .lr .r8, ldS .r8 33, stS 28 .r6, eorR .r6 .lr .r8,
  ldS .r7 21, ldS .r4 18, eorR .r8 .r7 .r4, ldS .r7 15, eorR .r8 .r8 .r7, ldS .r7 32,
  andR .lr .r7 .lr, eorR .lr .r8 .lr, stS 24 .r8, andR .r8 .r12 .lr, eorR .r6 .r6 .r8,
  eorR .r8 .r5 .r4, ldS .r4 15, eorR .r8 .r8 .r4, ldS .r4 33, eorR .r4 .r8 .r4, stS 33 .r8,
  ldS .r8 21, andR .r5 .r7 .r8, eorR .r8 .r8 .r5, andR .r8 .r12 .r8, eorR .r5 .r4 .r8, stS 21 .r4,
  ldS .r4 17, andR .r5 .r4 .r5, eorR .r6 .r6 .r5, eorR .lr .lr .r8, ldS .r8 23, andR .r5 .r7 .r8,
  ldS .r8 24, eorR .r7 .r8 .r5, andR .r7 .r12 .r7, ldS .r8 22, eorR .r12 .r8 .r7,
  andR .r12 .r4 .r12, eorR .lr .lr .r12, ldS .r12 16, andR .lr .r12 .lr, eorR .r6 .r6 .lr,
  eorR .lr .r8 .r5, stS 19 .r6, ldS .r6 26, ldS .r8 21, andR .r12 .r6 .r8, eorR .lr .lr .r12,
  ldS .r12 27, stS 35 .r7, ldS .r7 34, eorR .r12 .r12 .r7, ldS .r7 32, stS 34 .r5, ldS .r5 33,
  andR .r5 .r7 .r5, ldS .r7 24, eorR .r7 .r7 .r5, andR .r7 .r6 .r7, eorR .r12 .r12 .r7,
  andR .r12 .r4 .r12, eorR .lr .lr .r12, ldS .r12 29, andR .r7 .r6 .r12, eorR .r8 .r8 .r7,
  ldS .r7 23, ldS .r5 34, eorR .r7 .r7 .r5, ldS .r5 35, eorR .r7 .r7 .r5, andR .r7 .r4 .r7,
  eorR .r8 .r8 .r7, ldS .r7 16, andR .r8 .r7 .r8, eorR .lr .lr .r8, ldS .r8 20, ldS .r5 18,
  eorR .r8 .r8 .r5, stS 20 .lr, ldS .lr 15, eorR .r8 .r8 .lr, ldS .r7 32, eorR .r8 .r8 .r7,
  eorR .r12 .r12 .r5, eorR .r12 .r12 .lr, andR .r12 .r6 .r12, eorR .r12 .r8 .r12, stS 29 .r8,
  ldS .r8 30, eorR .r8 .r8 .r5, eorR .r8 .r8 .lr, andR .r8 .r6 .r8, ldS .lr 31, eorR .lr .lr .r8,
  andR .lr .r4 .lr, eorR .r12 .r12 .lr, ldS .lr 22, ldS .r8 25, eorR .r8 .lr .r8, andR .r8 .r6 .r8,
  ldS .r5 34, eorR .r5 .r5 .r8, eorR .lr .lr .r7, andR .r6 .r6 .lr, ldS .lr 29, eorR .lr .lr .r6,
  andR .r4 .r4 .lr, eorR .r5 .r5 .r4, ldS .r4 16, andR .r4 .r4 .r5, eorR .r7 .r12 .r4, ldS .r4 28,
  ldS .r5 19, ldS .r6 20]

/-- The code of S-box 2. -/
def sboxCode1 : List Instr := [
  .mov .lr (.imm 0), .dp .sub .lr .lr (.imm 1), stS 15 .lr, eorR .lr .r4 .r4, stS 16 .r6,
  eorR .r6 .r4 .r4, stS 17 .r7, ldS .r7 15, eorR .r6 .r6 .r7, stS 18 .r6, eorR .r6 .r12 .lr,
  eorR .r6 .r6 .r7, stS 19 .r8, andR .r8 .r5 .r12, stS 20 .r5, eorR .r5 .r12 .r8, stS 21 .r12,
  andR .r12 .r4 .r5, eorR .r12 .r6 .r12, stS 22 .r6, eorR .r6 .r8 .lr, eorR .r6 .r6 .r7, stS 23 .r8,
  andR .r8 .r4 .r6, stS 24 .r6, eorR .r6 .r5 .r8, stS 25 .r8, ldS .r8 19, andR .r6 .r8 .r6,
  eorR .r12 .r12 .r6, stS 26 .r6, ldS .r6 20, stS 27 .r12, ldS .r12 22, andR .r8 .r6 .r12,
  eorR .r6 .r12 .r8, eorR .r5 .r5 .lr, eorR .r5 .r5 .r7, andR .r12 .r4 .r5, stS 28 .r5,
  eorR .r5 .r6 .r12, stS 29 .r12, eorR .r12 .r6 .lr, eorR .r12 .r12 .r7, stS 30 .r6,
  andR .r6 .r4 .r12, stS 31 .r12, ldS .r12 20, eorR .r6 .r12 .r6, ldS .r7 19, andR .r6 .r7 .r6,
  eorR .r5 .r5 .r6, ldS .r6 17, andR .r5 .r6 .r5, ldS .r6 27, eorR .r6 .r6 .r5, andR .r5 .r4 .r8,
  stS 27 .r8, ldS .r8 18, eorR .r5 .r8 .r5, ldS .r8 21, stS 32 .lr, eorR .lr .r8 .r12,
  andR .r8 .r4 .lr, stS 33 .r4, eorR .r4 .r12 .r8, andR .r4 .r7 .r4, eorR .r5 .r5 .r4, ldS .r4 16,
  andR .r5 .r4 .r5, eorR .r6 .r6 .r5, ldS .r5 32, eorR .lr .lr .r5, stS 34 .r6, ldS .r6 15,
  eorR .lr .lr .r6, ldS .r6 33, ldS .r5 23, andR .r5 .r6 .r5, eorR .r12 .lr .r5, stS 23 .r5,
  ldS .r5 28, eorR .r5 .r5 .r8, andR .r5 .r7 .r5, eorR .r12 .r12 .r5, ldS .r5 31, ldS .r8 26,
  eorR .r5 .r5 .r8, ldS .r8 17, andR .r5 .r8 .r5, eorR .r12 .r12 .r5, ldS .r5 30, stS 26 .lr,
  andR .lr .r6 .r5, stS 31 .r12, ldS .r12 21, eorR .lr .r12 .lr, andR .lr .r7 .lr, ldS .r4 24,
  eorR .lr .r4 .lr, ldS .r4 22, stS 28 .lr, andR .lr .r6 .r4, eorR .r5 .r5 .lr, andR .r12 .r7 .r12,
  eorR .r5 .r5 .r12, andR .r5 .r8 .r5, ldS .r12 28, eorR .r12 .r12 .r5, ldS .r5 16,
  andR .r12 .r5 .r12, stS 28 .lr, ldS .lr 31, eorR .lr .lr .r12, ldS .r12 26, stS 31 .lr,
  eorR .lr .r12 .r6, eorR .lr .lr .r7, ldS .r4 24, ldS .r12 23, eorR .r5 .r4 .r12, andR .r5 .r7 .r5,
  eorR .r5 .r6 .r5, andR .r5 .r8 .r5, eorR .lr .lr .r5, ldS .r5 20, andR .r6 .r6 .r5, ldS .r5 18,
  eorR .r5 .r5 .r6, ldS .r12 25, eorR .r4 .r4 .r12, andR .r4 .r7 .r4, eorR .r5 .r5 .r4,
  andR .r6 .r8 .r6, eorR .r5 .r5 .r6, ldS .r6 16, andR .r5 .r6 .r5, eorR .lr .lr .r5, ldS .r5 26,
  eorR .r5 .r5 .r12, ldS .r12 29, andR .r12 .r7 .r12, eorR .r5 .r5 .r12, ldS .r12 23, ldS .r4 32,
  stS 29 .lr, eorR .lr .r12 .r4, ldS .r6 15, eorR .lr .lr .r6, ldS .r6 22, ldS .r4 28,
  eorR .r6 .r6 .r4, andR .r6 .r7 .r6, eorR .lr .lr .r6, andR .r8 .r8 .lr, eorR .r5 .r5 .r8,
  ldS .r8 27, eorR .r8 .r8 .r12, ldS .r12 32, eorR .r12 .r8 .r12, ldS .lr 15, eorR .r12 .r12 .lr,
  andR .r7 .r7 .r12, eorR .r8 .r8 .r7, ldS .r7 16, andR .r7 .r7 .r8, eorR .r7 .r5 .r7, ldS .r4 34,
  ldS .r5 31, ldS .r6 29]

/-- The code of S-box 3. -/
def sboxCode2 : List Instr := [
  .mov .lr (.imm 0), .dp .sub .lr .lr (.imm 1), stS 15 .lr, eorR .lr .r4 .r4, stS 16 .r6,
  eorR .r6 .r4 .r4, stS 17 .r7, ldS .r7 15, eorR .r6 .r6 .r7, stS 18 .r6, eorR .r6 .r12 .lr,
  eorR .r6 .r6 .r7, stS 19 .r5, andR .r5 .r8 .r6, eorR .r7 .r12 .r5, stS 20 .r5, andR .r5 .r8 .r12,
  stS 21 .r8, eorR .r8 .r6 .r5, stS 22 .r6, andR .r6 .r4 .r8, stS 23 .r12, eorR .r12 .r7 .r6,
  stS 24 .r7, eorR .r7 .r8 .lr, stS 25 .lr, ldS .lr 15, eorR .r7 .r7 .lr, andR .r5 .r4 .r5,
  eorR .lr .r7 .r5, stS 26 .r7, ldS .r7 19, stS 27 .r6, andR .r6 .r7 .lr, eorR .r6 .r12 .r6,
  stS 28 .r12, andR .r12 .r7 .r8, eorR .lr .lr .r12, ldS .r12 17, andR .lr .r12 .lr,
  eorR .r6 .r6 .lr, ldS .lr 23, andR .lr .r4 .lr, stS 23 .r8, ldS .r8 18, eorR .r8 .r8 .lr,
  stS 18 .lr, ldS .lr 22, stS 29 .r4, andR .r4 .r7 .lr, eorR .r8 .r8 .r4, andR .r5 .r12 .r5,
  eorR .r8 .r8 .r5, ldS .r5 16, andR .r8 .r5 .r8, eorR .r4 .r6 .r8, ldS .r8 21, eorR .r6 .lr .r8,
  stS 30 .r4, ldS .r4 27, eorR .r4 .r6 .r4, stS 27 .r6, ldS .r6 20, ldS .r5 25, eorR .r12 .r6 .r5,
  ldS .lr 15, eorR .r12 .r12 .lr, ldS .lr 29, andR .r5 .lr .r6, eorR .r5 .r12 .r5, andR .r6 .r7 .r5,
  stS 31 .r5, eorR .r5 .r4 .r6, stS 32 .r6, ldS .r6 25, stS 33 .r12, eorR .r12 .r8 .r6, stS 34 .r4,
  ldS .r4 15, eorR .r12 .r12 .r4, andR .r4 .lr .r12, eorR .r8 .r8 .r4, stS 21 .r12, ldS .r12 22,
  stS 35 .r4, andR .r4 .lr .r12, eorR .r12 .r12 .r4, andR .r12 .r7 .r12, eorR .r8 .r8 .r12,
  ldS .r12 17, andR .r8 .r12 .r8, eorR .r5 .r5 .r8, ldS .r8 28, eorR .r8 .r8 .r6, stS 28 .r5,
  ldS .r5 15, eorR .r8 .r8 .r5, ldS .r12 34, eorR .r12 .r12 .r6, eorR .r12 .r12 .r5,
  andR .r12 .r7 .r12, eorR .r8 .r8 .r12, ldS .r12 24, stS 34 .r8, eorR .r8 .r12 .r6,
  eorR .r8 .r8 .r5, andR .r12 .lr .r8, stS 22 .r8, ldS .r8 33, eorR .lr .r8 .r12, stS 36 .r12,
  eorR .r12 .r4 .r6, eorR .r12 .r12 .r5, andR .r12 .r7 .r12, eorR .lr .lr .r12, stS 37 .r4,
  ldS .r4 17, andR .lr .r4 .lr, stS 38 .r12, ldS .r12 34, eorR .r12 .r12 .lr, ldS .lr 16,
  andR .r12 .lr .r12, ldS .lr 28, eorR .lr .lr .r12, ldS .r12 29, stS 28 .lr, andR .lr .r12 .r8,
  ldS .r12 26, eorR .r12 .r12 .lr, ldS .lr 31, eorR .r8 .lr .r6, eorR .r8 .r8 .r5, andR .r8 .r7 .r8,
  eorR .r12 .r12 .r8, ldS .r8 32, eorR .lr .lr .r8, andR .lr .r4 .lr, eorR .r12 .r12 .lr,
  ldS .lr 20, ldS .r8 35, eorR .r8 .lr .r8, ldS .r5 38, eorR .r8 .r8 .r5, ldS .r5 18,
  andR .r6 .r7 .r5, eorR .lr .lr .r6, andR .lr .r4 .lr, eorR .r8 .r8 .lr, ldS .lr 16,
  andR .r8 .lr .r8, eorR .r6 .r12 .r8, ldS .r8 33, eorR .r8 .r8 .r5, eorR .r8 .r8 .r7, ldS .r5 27,
  ldS .r12 25, eorR .r5 .r5 .r12, ldS .r12 15, eorR .r5 .r5 .r12, ldS .r12 29, andR .r12 .r12 .r5,
  ldS .r5 21, eorR .r5 .r5 .r12, andR .r5 .r7 .r5, ldS .r12 23, eorR .r12 .r12 .r5,
  andR .r12 .r4 .r12, eorR .r8 .r8 .r12, ldS .r12 24, ldS .r5 37, eorR .r12 .r12 .r5, stS 24 .r6,
  ldS .r6 22, stS 23 .r8, ldS .r8 36, eorR .r8 .r6 .r8, andR .r8 .r7 .r8, eorR .r12 .r12 .r8,
  andR .r7 .r7 .r5, eorR .r6 .r6 .r7, andR .r4 .r4 .r6, eorR .r12 .r12 .r4, andR .lr .lr .r12,
  ldS .r12 23, eorR .r7 .r12 .lr, ldS .r4 30, ldS .r5 28, ldS .r6 24]

/-- The code of S-box 4. -/
def sboxCode3 : List Instr := [
  .mov .lr (.imm 0), .dp .sub .lr .lr (.imm 1), stS 15 .lr, eorR .lr .r4 .r4, stS 16 .r6,
  eorR .r6 .r4 .r4, stS 17 .r4, ldS .r4 15, eorR .r6 .r6 .r4, stS 18 .r6, eorR .r6 .r7 .lr,
  eorR .r6 .r6 .r4, stS 19 .r8, andR .r8 .r5 .r7, eorR .r4 .r6 .r8, stS 20 .r8, andR .r8 .r12 .r4,
  stS 21 .r4, eorR .r4 .r6 .r8, stS 22 .r8, eorR .r8 .r7 .r5, stS 23 .r7, eorR .r7 .r8 .lr,
  stS 24 .r6, ldS .r6 15, eorR .r7 .r7 .r6, andR .r6 .r12 .r7, stS 25 .r7, eorR .r7 .r8 .r6,
  stS 26 .r8, ldS .r8 19, andR .r7 .r8 .r7, eorR .r4 .r4 .r7, eorR .r7 .r5 .lr, stS 27 .r12,
  ldS .r12 15, eorR .r7 .r7 .r12, eorR .r12 .r5 .r6, stS 28 .r6, andR .r6 .r8 .r12, stS 29 .r5,
  eorR .r5 .r7 .r6, stS 30 .r6, ldS .r6 16, andR .r5 .r6 .r5, eorR .r4 .r4 .r5, ldS .r5 21,
  stS 31 .r7, eorR .r7 .r5 .lr, ldS .r5 15, eorR .r7 .r7 .r5, stS 32 .r4, ldS .r4 27,
  andR .r7 .r4 .r7, ldS .r6 25, eorR .r7 .r6 .r7, andR .r7 .r8 .r7, eorR .r12 .r12 .r7, ldS .r7 20,
  eorR .r7 .r7 .lr, eorR .r7 .r7 .r5, ldS .r5 29, stS 20 .lr, ldS .lr 24, andR .r6 .r5 .lr,
  ldS .r5 18, eorR .r5 .r5 .r6, andR .lr .r4 .r5, eorR .r7 .r7 .lr, stS 18 .r5, ldS .r5 26,
  andR .r5 .r8 .r5, eorR .r7 .r7 .r5, stS 26 .r5, ldS .r5 16, andR .r7 .r5 .r7, eorR .r12 .r12 .r7,
  ldS .r7 17, andR .r5 .r7 .r12, ldS .r7 32, eorR .r7 .r7 .r5, andR .r5 .r4 .r6, stS 32 .r7,
  ldS .r7 25, eorR .r7 .r7 .r5, ldS .r4 20, stS 25 .r5, eorR .r5 .lr .r4, ldS .r4 15,
  eorR .r5 .r5 .r4, andR .r5 .r8 .r5, eorR .r5 .r7 .r5, stS 33 .r7, eorR .r7 .r6 .lr, stS 34 .r6,
  ldS .r6 23, stS 35 .lr, ldS .lr 28, eorR .lr .r6 .lr, andR .lr .r8 .lr, eorR .r7 .r7 .lr,
  ldS .r6 16, andR .r7 .r6 .r7, eorR .r5 .r5 .r7, ldS .r7 20, eorR .r12 .r12 .r7,
  eorR .r12 .r12 .r4, ldS .r4 17, andR .r12 .r4 .r12, eorR .r5 .r5 .r12, ldS .r12 21, stS 28 .r5,
  ldS .r5 35, eorR .r12 .r12 .r5, ldS .r5 24, andR .r5 .r8 .r5, eorR .r12 .r12 .r5, ldS .r5 29,
  eorR .r5 .r5 .lr, andR .r5 .r6 .r5, eorR .r12 .r12 .r5, ldS .r5 33, eorR .r5 .r5 .r7, ldS .lr 15,
  eorR .r5 .r5 .lr, ldS .lr 18, ldS .r7 25, eorR .lr .lr .r7, andR .lr .r8 .lr, eorR .r5 .r5 .lr,
  ldS .lr 31, ldS .r8 22, eorR .lr .lr .r8, ldS .r8 26, eorR .lr .lr .r8, andR .lr .r6 .lr,
  eorR .r5 .r5 .lr, andR .lr .r4 .r5, eorR .r12 .r12 .lr, ldS .lr 34, ldS .r8 27, eorR .r8 .lr .r8,
  stS 27 .r12, ldS .r12 23, eorR .r12 .r12 .lr, eorR .r12 .r12 .r7, ldS .r7 19, andR .r7 .r7 .r12,
  eorR .r8 .r8 .r7, ldS .r7 22, ldS .r12 20, eorR .r7 .r7 .r12, ldS .lr 15, eorR .r7 .r7 .lr,
  ldS .r4 30, eorR .r7 .r7 .r4, andR .r6 .r6 .r7, eorR .r8 .r8 .r6, eorR .r5 .r5 .r12,
  eorR .r5 .r5 .lr, ldS .lr 17, andR .lr .lr .r5, eorR .r7 .r8 .lr, ldS .r4 32, ldS .r5 28,
  ldS .r6 27]

/-- The code of S-box 5. -/
def sboxCode4 : List Instr := [
  .mov .lr (.imm 0), .dp .sub .lr .lr (.imm 1), stS 15 .lr, eorR .lr .r4 .r4, stS 16 .r5,
  eorR .r5 .r4 .r4, stS 17 .r6, ldS .r6 15, eorR .r5 .r5 .r6, stS 18 .r8, eorR .r8 .r7 .lr,
  eorR .r8 .r8 .r6, stS 19 .r7, andR .r7 .r8 .r12, stS 20 .r8, eorR .r8 .r5 .r7, eorR .r4 .r4 .lr,
  eorR .r4 .r4 .r6, stS 21 .r5, andR .r5 .r4 .r8, stS 22 .r8, eorR .r8 .r12 .r5, stS 23 .r5,
  eorR .r5 .r12 .lr, eorR .r5 .r5 .r6, stS 24 .r12, ldS .r12 20, stS 25 .r4, andR .r4 .r12 .r5,
  eorR .r12 .r5 .r4, stS 26 .r4, ldS .r4 18, eorR .r4 .r4 .lr, eorR .r4 .r4 .r6, andR .r6 .r4 .r12,
  eorR .r6 .r8 .r6, stS 18 .r8, eorR .r8 .r5 .r7, stS 27 .r12, andR .r12 .r4 .r8, stS 28 .r8,
  ldS .r8 19, eorR .r12 .r8 .r12, ldS .r8 17, eorR .r8 .r8 .lr, stS 17 .lr, ldS .lr 15,
  eorR .r8 .r8 .lr, andR .r12 .r8 .r12, eorR .r6 .r6 .r12, ldS .r12 25, stS 29 .r6,
  andR .r6 .r12 .r5, stS 30 .r8, ldS .r8 20, eorR .r6 .r8 .r6, stS 31 .r5, ldS .r5 24,
  eorR .lr .r5 .r8, andR .r7 .r12 .r7, eorR .r7 .lr .r7, andR .r7 .r4 .r7, eorR .r6 .r6 .r7,
  ldS .r7 27, ldS .r8 17, stS 32 .lr, eorR .lr .r7 .r8, ldS .r5 15, eorR .lr .lr .r5,
  andR .lr .r12 .lr, ldS .r7 31, eorR .r5 .r7 .r12, andR .r5 .r4 .r5, eorR .lr .lr .r5, ldS .r5 30,
  andR .lr .r5 .lr, eorR .r6 .r6 .lr, ldS .lr 16, eorR .lr .lr .r8, ldS .r7 15, eorR .lr .lr .r7,
  andR .r6 .lr .r6, stS 16 .lr, ldS .lr 29, eorR .lr .lr .r6, ldS .r6 27, stS 29 .lr,
  andR .lr .r12 .r6, ldS .r6 22, eorR .r5 .r6 .lr, eorR .r5 .r5 .r4, ldS .r6 26, stS 33 .lr,
  eorR .lr .r6 .r8, eorR .lr .lr .r7, andR .r7 .r12 .lr, ldS .r8 21, eorR .r8 .r8 .r7,
  andR .r6 .r12 .r6, stS 26 .lr, andR .lr .r4 .r6, eorR .r8 .r8 .lr, ldS .lr 30, andR .r8 .lr .r8,
  eorR .r5 .r5 .r8, ldS .r8 28, eorR .r6 .r8 .r6, andR .r6 .r4 .r6, ldS .r8 19, eorR .r6 .r8 .r6,
  ldS .r8 24, andR .r8 .r12 .r8, ldS .r12 31, eorR .r12 .r12 .r8, stS 31 .r8, andR .r8 .r4 .r12,
  eorR .r8 .r7 .r8, andR .r8 .lr .r8, eorR .r6 .r6 .r8, ldS .r8 16, andR .r6 .r8 .r6,
  eorR .r5 .r5 .r6, ldS .r6 27, stS 24 .r5, ldS .r5 25, stS 21 .r12, eorR .r12 .r6 .r5,
  eorR .r12 .r12 .r4, ldS .r8 26, ldS .r6 33, eorR .r8 .r8 .r6, ldS .r6 32, eorR .r5 .r6 .r7,
  andR .r5 .r4 .r5, eorR .r8 .r8 .r5, andR .r8 .lr .r8, eorR .r12 .r12 .r8, ldS .r8 17,
  eorR .r5 .r6 .r8, ldS .r8 15, eorR .r5 .r5 .r8, ldS .r8 25, andR .r6 .r8 .r5, stS 33 .r5,
  ldS .r5 27, eorR .r5 .r5 .r6, andR .r5 .lr .r5, stS 27 .r6, ldS .r6 22, eorR .r6 .r6 .r5,
  ldS .r5 16, andR .r6 .r5 .r6, eorR .r6 .r12 .r6, ldS .r12 20, eorR .r12 .r12 .r7, ldS .r7 18,
  andR .r7 .r4 .r7, eorR .r12 .r12 .r7, ldS .r7 28, stS 18 .r6, eorR .r6 .r7 .r8, andR .r6 .r4 .r6,
  ldS .r5 21, eorR .r5 .r5 .r6, andR .r5 .lr .r5, eorR .r12 .r12 .r5, ldS .r5 33, ldS .r6 23,
  eorR .r5 .r5 .r6, ldS .r6 19, andR .r8 .r8 .r6, ldS .r6 32, eorR .r6 .r6 .r8, andR .r6 .r4 .r6,
  eorR .r5 .r5 .r6, ldS .r6 17, eorR .r7 .r7 .r6, ldS .r8 15, eorR .r7 .r7 .r8, stS 28 .r12,
  ldS .r12 27, eorR .r7 .r7 .r12, ldS .r12 31, eorR .r12 .r12 .r6, eorR .r12 .r12 .r8,
  andR .r4 .r4 .r12, eorR .r7 .r7 .r4, andR .lr .lr .r7, eorR .r5 .r5 .lr, ldS .lr 16,
  andR .lr .lr .r5, ldS .r5 28, eorR .r7 .r5 .lr, ldS .r4 29, ldS .r5 24, ldS .r6 18]

/-- The code of S-box 6. -/
def sboxCode5 : List Instr := [
  .mov .lr (.imm 0), .dp .sub .lr .lr (.imm 1), stS 15 .lr, eorR .lr .r4 .r4, stS 16 .r12,
  eorR .r12 .r4 .r4, stS 17 .r4, ldS .r4 15, eorR .r12 .r12 .r4, stS 18 .r12, eorR .r12 .r8 .lr,
  eorR .r12 .r12 .r4, andR .r4 .r7 .r12, stS 19 .r12, eorR .r12 .r4 .r5, stS 20 .lr,
  eorR .lr .r8 .r4, stS 21 .r8, andR .r8 .r5 .r7, stS 22 .r4, eorR .r4 .lr .r8, andR .r4 .r6 .r4,
  eorR .r12 .r12 .r4, ldS .r4 20, stS 23 .lr, eorR .lr .r8 .r4, stS 24 .r8, ldS .r8 15,
  eorR .lr .lr .r8, stS 25 .r12, eorR .r12 .r7 .r4, eorR .r12 .r12 .r8, andR .r8 .r5 .r12,
  stS 26 .r12, eorR .r12 .r7 .r8, stS 27 .r8, andR .r8 .r6 .r12, eorR .lr .lr .r8, stS 28 .r12,
  ldS .r12 16, andR .lr .r12 .lr, stS 29 .r8, ldS .r8 25, eorR .r8 .r8 .lr, ldS .lr 19, stS 25 .r8,
  eorR .r8 .lr .r7, andR .r12 .r5 .r8, stS 30 .r5, ldS .r5 22, stS 31 .r8, eorR .r8 .r5 .r12,
  andR .r8 .r6 .r8, ldS .r5 21, andR .r7 .r7 .r5, eorR .r5 .lr .r7, ldS .lr 31, stS 32 .r7,
  eorR .r7 .lr .r4, ldS .r4 15, eorR .r7 .r7 .r4, eorR .r7 .r7 .r12, andR .r7 .r6 .r7,
  eorR .r7 .r5 .r7, stS 33 .r5, ldS .r5 16, andR .r7 .r5 .r7, eorR .r8 .r8 .r7, ldS .r7 17,
  andR .r8 .r7 .r8, stS 34 .r12, ldS .r12 25, eorR .r12 .r12 .r8, ldS .r8 30, stS 25 .r12,
  ldS .r12 22, andR .r4 .r8 .r12, ldS .r12 32, eorR .lr .r12 .r4, ldS .r12 21, andR .r12 .r8 .r12,
  ldS .r7 18, eorR .r7 .r7 .r12, stS 18 .r4, andR .r4 .r6 .r7, eorR .lr .lr .r4, ldS .r4 23,
  stS 21 .r7, ldS .r7 27, eorR .r4 .r4 .r7, andR .r12 .r6 .r12, eorR .r4 .r4 .r12, andR .r4 .r5 .r4,
  eorR .lr .lr .r4, andR .r4 .r6 .r8, stS 23 .r12, ldS .r12 21, eorR .r12 .r12 .r4, ldS .r4 26,
  ldS .r7 18, eorR .r4 .r4 .r7, ldS .r7 19, stS 26 .lr, andR .lr .r8 .r7, andR .r8 .r6 .lr,
  eorR .r4 .r4 .r8, andR .r4 .r5 .r4, eorR .r12 .r12 .r4, ldS .r4 17, andR .r12 .r4 .r12,
  ldS .r8 26, eorR .r8 .r8 .r12, ldS .r12 31, stS 26 .r8, ldS .r8 27, eorR .r12 .r12 .r8,
  stS 31 .lr, ldS .lr 24, eorR .r7 .r7 .lr, andR .r7 .r6 .r7, eorR .r12 .r12 .r7, ldS .r7 22,
  ldS .lr 20, eorR .r8 .r7 .lr, ldS .r4 15, eorR .r8 .r8 .r4, ldS .r7 30, ldS .r4 32,
  andR .lr .r7 .r4, eorR .lr .r8 .lr, stS 24 .r8, ldS .r8 34, andR .r8 .r6 .r8, eorR .lr .lr .r8,
  andR .lr .r5 .lr, eorR .r12 .r12 .lr, ldS .lr 23, ldS .r8 20, eorR .lr .lr .r8, ldS .r8 15,
  eorR .lr .lr .r8, ldS .r8 22, stS 15 .r12, ldS .r12 18, eorR .r8 .r8 .r12, eorR .r4 .r4 .r7,
  andR .r4 .r6 .r4, eorR .r8 .r8 .r4, andR .r8 .r5 .r8, eorR .lr .lr .r8, ldS .r8 17,
  andR .lr .r8 .lr, ldS .r4 15, eorR .r4 .r4 .lr, ldS .lr 33, eorR .r12 .lr .r7, stS 15 .r4,
  ldS .r4 29, eorR .r12 .r12 .r4, ldS .r4 28, andR .r8 .r5 .r4, eorR .r12 .r12 .r8, ldS .r8 24,
  stS 29 .r12, ldS .r12 27, eorR .r12 .r8 .r12, andR .r12 .r6 .r12, eorR .r4 .r4 .r12,
  andR .r7 .r7 .r8, eorR .r8 .r8 .r7, ldS .r7 31, eorR .lr .lr .r7, andR .r6 .r6 .lr,
  eorR .r8 .r8 .r6, andR .r5 .r5 .r8, eorR .r4 .r4 .r5, ldS .r5 17, andR .r5 .r5 .r4, ldS .r4 29,
  eorR .r7 .r4 .r5, ldS .r4 25, ldS .r5 26, ldS .r6 15]

/-- The code of S-box 7. -/
def sboxCode6 : List Instr := [
  .mov .lr (.imm 0), .dp .sub .lr .lr (.imm 1), stS 15 .lr, eorR .lr .r4 .r4, stS 16 .r5,
  eorR .r5 .r4 .r4, stS 17 .r8, ldS .r8 15, eorR .r5 .r5 .r8, stS 18 .r7, eorR .r7 .r12 .r4,
  stS 19 .r5, andR .r5 .r4 .r12, stS 20 .r4, andR .r4 .r6 .r5, stS 21 .r12, eorR .r12 .r7 .r4,
  stS 22 .r4, eorR .r4 .r5 .lr, eorR .r4 .r4 .r8, stS 23 .r7, andR .r7 .r6 .r4, stS 24 .r5,
  ldS .r5 19, stS 25 .r4, eorR .r4 .r5 .r7, stS 26 .r7, ldS .r7 18, andR .r5 .r7 .r4,
  eorR .r12 .r12 .r5, ldS .r5 21, stS 27 .r4, eorR .r4 .r5 .lr, eorR .r4 .r4 .r8, ldS .r5 20,
  andR .r8 .r5 .r4, stS 28 .r4, andR .r4 .r6 .r8, stS 29 .r8, ldS .r8 19, stS 30 .lr,
  eorR .lr .r8 .r4, ldS .r8 25, stS 31 .r4, andR .r4 .r7 .r8, eorR .lr .lr .r4, stS 32 .r4,
  ldS .r4 17, andR .lr .r4 .lr, eorR .r12 .r12 .lr, ldS .lr 26, andR .r8 .r7 .lr, ldS .lr 27,
  eorR .lr .lr .r8, andR .r8 .r6 .r5, ldS .r5 24, eorR .r8 .r5 .r8, andR .r8 .r4 .r8,
  eorR .lr .lr .r8, ldS .r8 16, andR .lr .r8 .lr, eorR .r12 .r12 .lr, eorR .lr .r5 .r6, stS 27 .r12,
  ldS .r12 23, ldS .r8 30, eorR .r4 .r12 .r8, ldS .r12 15, eorR .r4 .r4 .r12, ldS .r12 31,
  eorR .r8 .r4 .r12, andR .r8 .r7 .r8, eorR .lr .lr .r8, ldS .r8 21, stS 33 .r4, andR .r4 .r6 .r8,
  stS 34 .r6, ldS .r6 19, stS 35 .lr, eorR .lr .r6 .r4, eorR .r5 .r8 .r5, eorR .r6 .r5 .r12,
  andR .r6 .r7 .r6, eorR .lr .lr .r6, ldS .r12 17, andR .lr .r12 .lr, stS 24 .r4, ldS .r4 35,
  eorR .r4 .r4 .lr, ldS .lr 28, ldS .r8 29, stS 35 .r4, eorR .r4 .lr .r8, ldS .r8 20, ldS .lr 30,
  eorR .r8 .r8 .lr, ldS .lr 15, eorR .r8 .r8 .lr, ldS .lr 34, andR .r8 .lr .r8, eorR .r8 .r4 .r8,
  eorR .r8 .r8 .r6, ldS .r6 33, stS 20 .r4, andR .r4 .lr .r6, andR .r6 .r7 .r5, eorR .r4 .r4 .r6,
  andR .r4 .r12 .r4, eorR .r8 .r8 .r4, ldS .r4 16, andR .r8 .r4 .r8, ldS .r6 35, eorR .r6 .r6 .r8,
  ldS .r8 30, eorR .r5 .r5 .r8, ldS .r8 15, eorR .r5 .r5 .r8, ldS .r8 28, andR .r8 .lr .r8,
  stS 28 .r6, eorR .r6 .r5 .r8, stS 15 .r5, ldS .r5 21, stS 30 .r8, andR .r8 .r7 .r5,
  eorR .r6 .r6 .r8, stS 35 .r8, ldS .r8 33, ldS .r5 26, eorR .r8 .r8 .r5, ldS .r5 25, ldS .r4 24,
  eorR .r5 .r5 .r4, andR .r5 .r7 .r5, eorR .r8 .r8 .r5, andR .r8 .r12 .r8, eorR .r6 .r6 .r8,
  ldS .r8 23, andR .r8 .lr .r8, andR .r8 .r7 .r8, ldS .r5 19, eorR .r5 .r5 .r8, ldS .r8 31,
  andR .r8 .r12 .r8, eorR .r5 .r5 .r8, ldS .r8 16, andR .r5 .r8 .r5, eorR .r6 .r6 .r5, ldS .r5 29,
  eorR .r5 .r5 .r4, stS 29 .r6, ldS .r6 32, eorR .r5 .r5 .r6, ldS .r6 21, ldS .r8 30,
  eorR .r8 .r6 .r8, ldS .r4 20, andR .lr .lr .r4, eorR .r4 .r4 .lr, andR .r4 .r7 .r4,
  eorR .r8 .r8 .r4, andR .r8 .r12 .r8, eorR .r5 .r5 .r8, ldS .r8 15, ldS .r4 22, eorR .r8 .r8 .r4,
  eorR .r6 .r6 .lr, andR .r7 .r7 .r6, eorR .r8 .r8 .r7, ldS .r7 24, ldS .r6 35, eorR .r7 .r7 .r6,
  andR .r12 .r12 .r7, eorR .r8 .r8 .r12, ldS .r12 16, andR .r12 .r12 .r8, eorR .r7 .r5 .r12,
  ldS .r4 27, ldS .r5 28, ldS .r6 29]

/-- The code of S-box 8. -/
def sboxCode7 : List Instr := [
  .mov .lr (.imm 0), .dp .sub .lr .lr (.imm 1), stS 15 .lr, eorR .lr .r4 .r4, stS 16 .r6,
  eorR .r6 .r4 .r4, stS 17 .r8, ldS .r8 15, eorR .r6 .r6 .r8, stS 18 .r6, eorR .r6 .r4 .lr,
  eorR .r6 .r6 .r8, stS 19 .r4, eorR .r4 .r12 .r6, eorR .r7 .r7 .lr, eorR .r7 .r7 .r8, stS 20 .r6,
  eorR .r6 .r4 .r7, eorR .r5 .r5 .lr, eorR .r5 .r5 .r8, eorR .r6 .r6 .r5, stS 21 .r4, ldS .r4 19,
  stS 22 .r6, andR .r6 .r7 .r4, ldS .r4 20, andR .r8 .r4 .r12, stS 23 .r12, andR .r12 .r7 .r8,
  stS 24 .r7, eorR .r7 .r4 .r12, andR .r7 .r5 .r7, eorR .r7 .r6 .r7, stS 25 .r12, ldS .r12 17,
  eorR .r12 .r12 .lr, stS 17 .r8, ldS .r8 15, eorR .r12 .r12 .r8, andR .r7 .r12 .r7, stS 26 .r12,
  ldS .r12 22, eorR .r12 .r12 .r7, ldS .r7 23, stS 22 .r12, eorR .r12 .r7 .lr, eorR .r12 .r12 .r8,
  andR .r8 .r4 .r12, stS 27 .lr, ldS .lr 18, stS 28 .r12, eorR .r12 .lr .r8, stS 29 .r8,
  eorR .r8 .r12 .r6, andR .r8 .r5 .r8, eorR .r4 .r4 .r8, ldS .r8 17, stS 20 .r12, eorR .r12 .r7 .r8,
  stS 30 .r6, ldS .r6 24, andR .r7 .r6 .r12, eorR .lr .lr .r7, ldS .r6 28, stS 18 .r12,
  andR .r12 .r5 .r6, eorR .lr .lr .r12, stS 31 .r12, ldS .r12 26, andR .lr .r12 .lr,
  eorR .r4 .r4 .lr, ldS .lr 16, ldS .r12 27, eorR .lr .lr .r12, stS 16 .r5, ldS .r5 15,
  eorR .lr .lr .r5, andR .r4 .lr .r4, stS 32 .lr, ldS .lr 22, eorR .r4 .lr .r4, eorR .lr .r8 .r12,
  eorR .lr .lr .r5, stS 22 .r4, eorR .r4 .lr .r7, stS 33 .r7, ldS .r7 18, eorR .r7 .r7 .r12,
  eorR .r7 .r7 .r5, ldS .r8 24, stS 18 .lr, andR .lr .r8 .r7, eorR .r6 .r6 .lr, stS 28 .r7,
  ldS .r7 16, andR .r6 .r7 .r6, eorR .r4 .r4 .r6, ldS .r6 25, stS 34 .lr, eorR .lr .r6 .r12,
  eorR .lr .lr .r5, andR .r8 .r7 .r6, eorR .r8 .lr .r8, stS 35 .lr, ldS .lr 26, andR .r8 .lr .r8,
  eorR .r4 .r4 .r8, ldS .r8 23, ldS .r6 29, stS 36 .r4, eorR .r4 .r8 .r6, ldS .r8 30,
  eorR .r8 .r4 .r8, ldS .r6 21, andR .r6 .r7 .r6, eorR .lr .r8 .r6, eorR .r8 .r8 .r12,
  eorR .r8 .r8 .r5, eorR .r4 .r4 .r12, eorR .r4 .r4 .r5, andR .r4 .r7 .r4, eorR .r8 .r8 .r4,
  ldS .r4 26, andR .r8 .r4 .r8, eorR .lr .lr .r8, ldS .r8 32, andR .lr .r8 .lr, ldS .r5 36,
  eorR .r5 .r5 .lr, ldS .lr 29, stS 36 .r5, ldS .r5 25, eorR .r12 .lr .r5, stS 21 .r6, ldS .r6 24,
  ldS .lr 18, andR .r8 .r6 .lr, ldS .r6 23, eorR .r6 .r6 .r8, andR .r8 .r7 .r6, eorR .r12 .r12 .r8,
  ldS .r8 34, eorR .r8 .lr .r8, andR .r8 .r4 .r8, eorR .r12 .r12 .r8, ldS .r8 31, eorR .lr .lr .r8,
  stS 18 .r6, ldS .r6 17, eorR .r5 .r6 .r5, eorR .r5 .r5 .r8, andR .r5 .r4 .r5, eorR .lr .lr .r5,
  ldS .r5 32, andR .lr .r5 .lr, eorR .r12 .r12 .lr, ldS .lr 35, andR .lr .r7 .lr, ldS .r8 18,
  eorR .r8 .r8 .lr, ldS .lr 24, stS 18 .r12, ldS .r12 29, andR .lr .lr .r12, eorR .r6 .r6 .lr,
  ldS .lr 19, ldS .r12 33, eorR .lr .lr .r12, andR .lr .r7 .lr, eorR .lr .r6 .lr, andR .lr .r4 .lr,
  eorR .r8 .r8 .lr, ldS .lr 20, ldS .r12 21, eorR .lr .lr .r12, ldS .r12 27, eorR .r6 .r6 .r12,
  ldS .r12 15, eorR .r6 .r6 .r12, ldS .r12 28, andR .r7 .r7 .r12, eorR .r6 .r6 .r7,
  andR .r4 .r4 .r6, eorR .lr .lr .r4, andR .r5 .r5 .lr, eorR .r7 .r8 .r5, ldS .r4 22, ldS .r5 36,
  ldS .r6 18]

/-- Six input planes and one temporary; slots below 16 hold saved registers and control state. -/
def sboxCode : Nat → List Instr
  | 0 => sboxCode0 | 1 => sboxCode1 | 2 => sboxCode2 | 3 => sboxCode3
  | 4 => sboxCode4 | 5 => sboxCode5 | 6 => sboxCode6 | _ => sboxCode7

#guard (List.range 8).all fun i => sboxCode i ==
  VG.Impl.Aes.Arm.compile .r2 (Circuit.gates i) sboxIns (sboxOuts i)
    [.lr] 15 10000 10001 (List.range' 16 96)

def sbox0 : Prog isa := .block (sboxCode 0)
def sbox1 : Prog isa := .block (sboxCode 1)
def sbox2 : Prog isa := .block (sboxCode 2)
def sbox3 : Prog isa := .block (sboxCode 3)
def sbox4 : Prog isa := .block (sboxCode 4)
def sbox5 : Prog isa := .block (sboxCode 5)
def sbox6 : Prog isa := .block (sboxCode 6)
def sbox7 : Prog isa := .block (sboxCode 7)

end VG.Impl.TripleDes.Arm
