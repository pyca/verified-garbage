module

public import VerifiedGarbage.Impl.TripleDes.Circuit
meta import VerifiedGarbage.Impl.TripleDes.Circuit
public import VerifiedGarbage.Impl.Aes.AArch64.Alloc
meta import VerifiedGarbage.Impl.Aes.AArch64.Alloc

@[expose] public section

namespace VG.Impl.TripleDes.AArch64

open VG.AArch64

def q : Nat → Reg
  | 0 => .x3 | 1 => .x4 | 2 => .x5 | 3 => .x6 | 4 => .x7 | _ => .x8

def sboxIns : List (Nat × Reg) := (List.range 6).map fun i => (i, q i)

def sboxOuts (i : Nat) : List (Nat × Reg) :=
  (List.range 4).map fun j => ((Circuit.outputs i).getD j 0, q j)

/-! The code of the S-boxes, as `compile` allocates it for their circuits. It is written
out (and `#guard` checks that it is what `compile` produces) so that the kernel, which
evaluates the code in the proofs, does not have to run the allocator. -/

/-! Short forms of the instructions, on slots of the scratch buffer at `x2`. -/
def movR (d n : Reg) : Instr := .addImm .x d n 0
def eorR (d n m : Reg) : Instr := .logic .eor .x d n m
def andR (d n m : Reg) : Instr := .logic .and .x d n m
def ldS (d : Reg) (k : Nat) : Instr := .ldr .x d .x2 (8 * k)
def stS (k : Nat) (r : Reg) : Instr := .str .x r .x2 (8 * k)

/-- The code of S-box 1. -/
def sboxCode0 : List Instr := [
  .movz .x .x9 0 0, .subImm .x .x9 .x9 1, eorR .x10 .x3 .x3, eorR .x11 .x3 .x10, eorR .x11 .x11 .x9,
  andR .x12 .x7 .x11, eorR .x13 .x3 .x7, andR .x14 .x4 .x13, eorR .x14 .x12 .x14,
  eorR .x15 .x11 .x12, andR .x16 .x4 .x15, eorR .x16 .x3 .x16, andR .x16 .x8 .x16,
  eorR .x14 .x14 .x16, andR .x16 .x7 .x3, eorR .x17 .x16 .x10, eorR .x17 .x17 .x9, stS 4 .x13,
  andR .x13 .x4 .x17, stS 5 .x3, eorR .x3 .x16 .x13, stS 6 .x12, eorR .x12 .x7 .x10,
  eorR .x12 .x12 .x9, stS 7 .x10, eorR .x10 .x12 .x13, stS 8 .x13, andR .x13 .x8 .x10,
  eorR .x3 .x3 .x13, andR .x3 .x6 .x3, eorR .x14 .x14 .x3, andR .x7 .x4 .x7, eorR .x3 .x17 .x7,
  andR .x13 .x4 .x12, stS 9 .x7, eorR .x7 .x11 .x13, andR .x7 .x8 .x7, eorR .x3 .x3 .x7,
  andR .x7 .x4 .x11, stS 10 .x12, eorR .x12 .x15 .x7, andR .x12 .x8 .x12, andR .x12 .x6 .x12,
  eorR .x3 .x3 .x12, andR .x3 .x5 .x3, eorR .x3 .x14 .x3, eorR .x11 .x11 .x16, eorR .x16 .x11 .x13,
  ldS .x14 6, ldS .x12 7, stS 11 .x3, eorR .x3 .x14 .x12, eorR .x3 .x3 .x9, andR .x11 .x4 .x11,
  eorR .x11 .x3 .x11, stS 12 .x10, andR .x10 .x8 .x11, eorR .x16 .x16 .x10, eorR .x10 .x15 .x12,
  eorR .x10 .x10 .x9, eorR .x13 .x10 .x13, andR .x12 .x4 .x14, eorR .x14 .x14 .x12,
  andR .x14 .x8 .x14, eorR .x12 .x13 .x14, andR .x12 .x6 .x12, eorR .x16 .x16 .x12,
  eorR .x11 .x11 .x14, ldS .x14 5, andR .x12 .x4 .x14, eorR .x14 .x3 .x12, andR .x14 .x8 .x14,
  stS 6 .x3, eorR .x3 .x15 .x14, andR .x3 .x6 .x3, eorR .x11 .x11 .x3, andR .x11 .x5 .x11,
  eorR .x16 .x16 .x11, eorR .x11 .x15 .x12, andR .x3 .x8 .x13, eorR .x11 .x11 .x3,
  eorR .x17 .x17 .x7, andR .x10 .x4 .x10, ldS .x7 6, eorR .x7 .x7 .x10, andR .x7 .x8 .x7,
  eorR .x17 .x17 .x7, andR .x17 .x6 .x17, eorR .x11 .x11 .x17, ldS .x17 8, andR .x7 .x8 .x17,
  eorR .x13 .x13 .x7, ldS .x7 5, eorR .x7 .x7 .x12, eorR .x7 .x7 .x14, andR .x7 .x6 .x7,
  eorR .x13 .x13 .x7, andR .x13 .x5 .x13, eorR .x11 .x11 .x13, ldS .x13 4, ldS .x7 7,
  eorR .x13 .x13 .x7, eorR .x13 .x13 .x9, eorR .x13 .x13 .x4, eorR .x17 .x17 .x7,
  eorR .x17 .x17 .x9, andR .x17 .x8 .x17, eorR .x17 .x13 .x17, ldS .x14 12, eorR .x14 .x14 .x7,
  eorR .x14 .x14 .x9, andR .x14 .x8 .x14, ldS .x7 10, eorR .x7 .x7 .x14, andR .x7 .x6 .x7,
  eorR .x17 .x17 .x7, ldS .x7 9, eorR .x7 .x15 .x7, andR .x7 .x8 .x7, eorR .x12 .x12 .x7,
  eorR .x15 .x15 .x4, andR .x8 .x8 .x15, eorR .x13 .x13 .x8, andR .x6 .x6 .x13, eorR .x12 .x12 .x6,
  andR .x5 .x5 .x12, eorR .x6 .x17 .x5, ldS .x3 11, movR .x4 .x16, movR .x5 .x11]

/-- The code of S-box 2. -/
def sboxCode1 : List Instr := [
  .movz .x .x9 0 0, .subImm .x .x9 .x9 1, eorR .x10 .x3 .x3, eorR .x11 .x3 .x3, eorR .x11 .x11 .x9,
  eorR .x12 .x8 .x10, eorR .x12 .x12 .x9, andR .x13 .x4 .x8, eorR .x14 .x8 .x13, andR .x15 .x3 .x14,
  eorR .x15 .x12 .x15, eorR .x16 .x13 .x10, eorR .x16 .x16 .x9, andR .x17 .x3 .x16, stS 4 .x16,
  eorR .x16 .x14 .x17, andR .x16 .x7 .x16, eorR .x15 .x15 .x16, stS 5 .x17, andR .x17 .x4 .x12,
  stS 6 .x16, eorR .x16 .x12 .x17, eorR .x14 .x14 .x10, eorR .x14 .x14 .x9, stS 7 .x12,
  andR .x12 .x3 .x14, stS 8 .x14, eorR .x14 .x16 .x12, stS 9 .x12, eorR .x12 .x16 .x10,
  eorR .x12 .x12 .x9, stS 10 .x16, andR .x16 .x3 .x12, eorR .x16 .x4 .x16, andR .x16 .x7 .x16,
  eorR .x14 .x14 .x16, andR .x14 .x6 .x14, eorR .x15 .x15 .x14, andR .x14 .x3 .x17,
  eorR .x14 .x11 .x14, eorR .x16 .x8 .x4, stS 11 .x17, andR .x17 .x3 .x16, stS 12 .x11,
  eorR .x11 .x4 .x17, andR .x11 .x7 .x11, eorR .x14 .x14 .x11, andR .x14 .x5 .x14,
  eorR .x15 .x15 .x14, eorR .x16 .x16 .x10, eorR .x16 .x16 .x9, andR .x13 .x3 .x13,
  eorR .x14 .x16 .x13, ldS .x11 8, eorR .x11 .x11 .x17, andR .x11 .x7 .x11, eorR .x14 .x14 .x11,
  ldS .x11 6, eorR .x12 .x12 .x11, andR .x12 .x6 .x12, eorR .x14 .x14 .x12, ldS .x12 10,
  andR .x11 .x3 .x12, eorR .x11 .x8 .x11, andR .x11 .x7 .x11, ldS .x17 4, eorR .x11 .x17 .x11,
  stS 6 .x15, ldS .x15 7, stS 8 .x10, andR .x10 .x3 .x15, eorR .x12 .x12 .x10, andR .x8 .x7 .x8,
  eorR .x12 .x12 .x8, andR .x12 .x6 .x12, eorR .x11 .x11 .x12, andR .x11 .x5 .x11,
  eorR .x14 .x14 .x11, eorR .x11 .x16 .x3, eorR .x11 .x11 .x7, eorR .x12 .x17 .x13,
  andR .x12 .x7 .x12, eorR .x12 .x3 .x12, andR .x12 .x6 .x12, eorR .x11 .x11 .x12, andR .x3 .x3 .x4,
  ldS .x4 12, eorR .x4 .x4 .x3, ldS .x12 5, eorR .x17 .x17 .x12, andR .x17 .x7 .x17,
  eorR .x4 .x4 .x17, andR .x3 .x6 .x3, eorR .x4 .x4 .x3, andR .x4 .x5 .x4, eorR .x11 .x11 .x4,
  eorR .x16 .x16 .x12, ldS .x12 9, andR .x12 .x7 .x12, eorR .x16 .x16 .x12, ldS .x12 8,
  eorR .x4 .x13 .x12, eorR .x4 .x4 .x9, eorR .x15 .x15 .x10, andR .x15 .x7 .x15, eorR .x4 .x4 .x15,
  andR .x6 .x6 .x4, eorR .x16 .x16 .x6, ldS .x6 11, eorR .x6 .x6 .x13, eorR .x12 .x6 .x12,
  eorR .x12 .x12 .x9, andR .x7 .x7 .x12, eorR .x6 .x6 .x7, andR .x5 .x5 .x6, eorR .x6 .x16 .x5,
  ldS .x3 6, movR .x4 .x14, movR .x5 .x11]

/-- The code of S-box 3. -/
def sboxCode2 : List Instr := [
  .movz .x .x9 0 0, .subImm .x .x9 .x9 1, eorR .x10 .x3 .x3, eorR .x11 .x3 .x3, eorR .x11 .x11 .x9,
  eorR .x12 .x8 .x10, eorR .x12 .x12 .x9, andR .x13 .x7 .x12, eorR .x14 .x8 .x13, andR .x15 .x7 .x8,
  eorR .x16 .x12 .x15, andR .x17 .x3 .x16, stS 4 .x13, eorR .x13 .x14 .x17, stS 5 .x14,
  eorR .x14 .x16 .x10, eorR .x14 .x14 .x9, andR .x15 .x3 .x15, stS 6 .x10, eorR .x10 .x14 .x15,
  stS 7 .x14, andR .x14 .x4 .x10, eorR .x14 .x13 .x14, stS 8 .x13, andR .x13 .x4 .x16,
  eorR .x10 .x10 .x13, andR .x10 .x6 .x10, eorR .x14 .x14 .x10, andR .x8 .x3 .x8,
  eorR .x11 .x11 .x8, andR .x10 .x4 .x12, eorR .x11 .x11 .x10, andR .x15 .x6 .x15,
  eorR .x11 .x11 .x15, andR .x11 .x5 .x11, eorR .x14 .x14 .x11, eorR .x11 .x12 .x7,
  eorR .x17 .x11 .x17, ldS .x15 4, ldS .x10 6, eorR .x13 .x15 .x10, eorR .x13 .x13 .x9, stS 9 .x14,
  andR .x14 .x3 .x15, eorR .x14 .x13 .x14, stS 10 .x16, andR .x16 .x4 .x14, stS 11 .x11,
  eorR .x11 .x17 .x16, stS 12 .x8, eorR .x8 .x7 .x10, eorR .x8 .x8 .x9, andR .x15 .x3 .x8,
  eorR .x7 .x7 .x15, stS 13 .x8, andR .x8 .x3 .x12, eorR .x12 .x12 .x8, andR .x12 .x4 .x12,
  eorR .x7 .x7 .x12, andR .x7 .x6 .x7, eorR .x11 .x11 .x7, ldS .x7 8, eorR .x7 .x7 .x10,
  eorR .x7 .x7 .x9, eorR .x17 .x17 .x10, eorR .x17 .x17 .x9, andR .x17 .x4 .x17, eorR .x7 .x7 .x17,
  ldS .x17 5, eorR .x12 .x17 .x10, eorR .x12 .x12 .x9, andR .x17 .x3 .x12, stS 8 .x12,
  eorR .x12 .x13 .x17, stS 14 .x17, eorR .x17 .x8 .x10, eorR .x17 .x17 .x9, andR .x17 .x4 .x17,
  eorR .x12 .x12 .x17, andR .x12 .x6 .x12, eorR .x7 .x7 .x12, andR .x7 .x5 .x7, eorR .x11 .x11 .x7,
  andR .x7 .x3 .x13, ldS .x12 7, eorR .x12 .x12 .x7, eorR .x7 .x14 .x10, eorR .x7 .x7 .x9,
  andR .x7 .x4 .x7, eorR .x12 .x12 .x7, eorR .x14 .x14 .x16, andR .x14 .x6 .x14,
  eorR .x12 .x12 .x14, ldS .x14 4, eorR .x15 .x14 .x15, eorR .x15 .x15 .x17, ldS .x17 12,
  andR .x16 .x4 .x17, eorR .x14 .x14 .x16, andR .x14 .x6 .x14, eorR .x15 .x15 .x14,
  andR .x15 .x5 .x15, eorR .x12 .x12 .x15, eorR .x13 .x13 .x17, eorR .x13 .x13 .x4, ldS .x17 11,
  eorR .x17 .x17 .x10, eorR .x17 .x17 .x9, andR .x3 .x3 .x17, ldS .x17 13, eorR .x17 .x17 .x3,
  andR .x17 .x4 .x17, ldS .x3 10, eorR .x3 .x3 .x17, andR .x3 .x6 .x3, eorR .x13 .x13 .x3,
  ldS .x3 5, eorR .x3 .x3 .x8, ldS .x17 8, ldS .x10 14, eorR .x10 .x17 .x10, andR .x10 .x4 .x10,
  eorR .x3 .x3 .x10, andR .x4 .x4 .x8, eorR .x17 .x17 .x4, andR .x6 .x6 .x17, eorR .x3 .x3 .x6,
  andR .x5 .x5 .x3, eorR .x6 .x13 .x5, ldS .x3 9, movR .x4 .x11, movR .x5 .x12]

/-- The code of S-box 4. -/
def sboxCode3 : List Instr := [
  .movz .x .x9 0 0, .subImm .x .x9 .x9 1, eorR .x10 .x3 .x3, eorR .x11 .x3 .x3, eorR .x11 .x11 .x9,
  eorR .x12 .x6 .x10, eorR .x12 .x12 .x9, andR .x13 .x4 .x6, eorR .x14 .x12 .x13,
  andR .x15 .x8 .x14, eorR .x16 .x12 .x15, eorR .x17 .x6 .x4, stS 4 .x15, eorR .x15 .x17 .x10,
  eorR .x15 .x15 .x9, stS 5 .x6, andR .x6 .x8 .x15, stS 6 .x3, eorR .x3 .x17 .x6, andR .x3 .x7 .x3,
  eorR .x16 .x16 .x3, eorR .x3 .x4 .x10, eorR .x3 .x3 .x9, stS 7 .x17, eorR .x17 .x4 .x6, stS 8 .x6,
  andR .x6 .x7 .x17, stS 9 .x11, eorR .x11 .x3 .x6, andR .x11 .x5 .x11, eorR .x16 .x16 .x11,
  eorR .x11 .x14 .x10, eorR .x11 .x11 .x9, andR .x11 .x8 .x11, eorR .x11 .x15 .x11,
  andR .x11 .x7 .x11, eorR .x17 .x17 .x11, eorR .x13 .x13 .x10, eorR .x13 .x13 .x9,
  andR .x11 .x4 .x12, stS 10 .x6, ldS .x6 9, eorR .x6 .x6 .x11, stS 9 .x3, andR .x3 .x8 .x6,
  eorR .x13 .x13 .x3, stS 11 .x6, ldS .x6 7, andR .x6 .x7 .x6, eorR .x13 .x13 .x6,
  andR .x13 .x5 .x13, eorR .x17 .x17 .x13, ldS .x13 6, stS 7 .x6, andR .x6 .x13 .x17,
  eorR .x16 .x16 .x6, andR .x6 .x8 .x11, eorR .x15 .x15 .x6, stS 12 .x16, eorR .x16 .x3 .x10,
  eorR .x16 .x16 .x9, andR .x16 .x7 .x16, eorR .x16 .x15 .x16, stS 13 .x8, eorR .x8 .x11 .x3,
  stS 14 .x11, ldS .x11 5, stS 15 .x6, ldS .x6 8, eorR .x6 .x11 .x6, andR .x6 .x7 .x6,
  eorR .x8 .x8 .x6, andR .x8 .x5 .x8, eorR .x16 .x16 .x8, eorR .x17 .x17 .x10, eorR .x17 .x17 .x9,
  andR .x17 .x13 .x17, eorR .x16 .x16 .x17, eorR .x14 .x14 .x3, andR .x12 .x7 .x12,
  eorR .x14 .x14 .x12, eorR .x4 .x4 .x6, andR .x4 .x5 .x4, eorR .x14 .x14 .x4, eorR .x15 .x15 .x10,
  eorR .x15 .x15 .x9, ldS .x4 11, ldS .x6 15, eorR .x4 .x4 .x6, andR .x4 .x7 .x4,
  eorR .x15 .x15 .x4, ldS .x4 9, ldS .x12 4, eorR .x4 .x4 .x12, ldS .x3 7, eorR .x4 .x4 .x3,
  andR .x4 .x5 .x4, eorR .x15 .x15 .x4, andR .x4 .x13 .x15, eorR .x14 .x14 .x4, ldS .x4 14,
  ldS .x3 13, eorR .x3 .x4 .x3, eorR .x11 .x11 .x4, eorR .x11 .x11 .x6, andR .x7 .x7 .x11,
  eorR .x3 .x3 .x7, eorR .x12 .x12 .x10, eorR .x12 .x12 .x9, ldS .x7 10, eorR .x12 .x12 .x7,
  andR .x5 .x5 .x12, eorR .x3 .x3 .x5, eorR .x15 .x15 .x10, eorR .x15 .x15 .x9, andR .x13 .x13 .x15,
  eorR .x6 .x3 .x13, ldS .x3 12, movR .x4 .x16, movR .x5 .x14]

/-- The code of S-box 5. -/
def sboxCode4 : List Instr := [
  .movz .x .x9 0 0, .subImm .x .x9 .x9 1, eorR .x10 .x3 .x3, eorR .x11 .x3 .x3, eorR .x11 .x11 .x9,
  eorR .x12 .x6 .x10, eorR .x12 .x12 .x9, andR .x13 .x12 .x8, eorR .x14 .x11 .x13,
  eorR .x3 .x3 .x10, eorR .x3 .x3 .x9, andR .x15 .x3 .x14, eorR .x16 .x8 .x15, eorR .x17 .x8 .x10,
  eorR .x17 .x17 .x9, stS 4 .x15, andR .x15 .x12 .x17, stS 5 .x11, eorR .x11 .x17 .x15,
  eorR .x7 .x7 .x10, eorR .x7 .x7 .x9, stS 6 .x15, andR .x15 .x7 .x11, eorR .x15 .x16 .x15,
  stS 7 .x16, eorR .x16 .x17 .x13, stS 8 .x14, andR .x14 .x7 .x16, eorR .x14 .x6 .x14,
  eorR .x5 .x5 .x10, eorR .x5 .x5 .x9, andR .x14 .x5 .x14, eorR .x15 .x15 .x14, andR .x14 .x3 .x17,
  eorR .x14 .x12 .x14, stS 9 .x6, eorR .x6 .x8 .x12, andR .x13 .x3 .x13, eorR .x13 .x6 .x13,
  andR .x13 .x7 .x13, eorR .x14 .x14 .x13, eorR .x13 .x11 .x10, eorR .x13 .x13 .x9,
  andR .x13 .x3 .x13, stS 10 .x12, eorR .x12 .x17 .x3, andR .x12 .x7 .x12, eorR .x13 .x13 .x12,
  andR .x13 .x5 .x13, eorR .x14 .x14 .x13, eorR .x4 .x4 .x10, eorR .x4 .x4 .x9, andR .x14 .x4 .x14,
  eorR .x15 .x15 .x14, andR .x14 .x3 .x11, ldS .x13 8, eorR .x12 .x13 .x14, eorR .x12 .x12 .x7,
  stS 11 .x15, ldS .x15 6, eorR .x13 .x15 .x10, eorR .x13 .x13 .x9, stS 12 .x10, andR .x10 .x3 .x13,
  stS 13 .x6, ldS .x6 5, eorR .x6 .x6 .x10, andR .x15 .x3 .x15, stS 6 .x13, andR .x13 .x7 .x15,
  eorR .x6 .x6 .x13, andR .x6 .x5 .x6, eorR .x12 .x12 .x6, eorR .x15 .x16 .x15, andR .x15 .x7 .x15,
  ldS .x6 9, eorR .x15 .x6 .x15, andR .x8 .x3 .x8, eorR .x17 .x17 .x8, andR .x13 .x7 .x17,
  eorR .x13 .x10 .x13, andR .x13 .x5 .x13, eorR .x15 .x15 .x13, andR .x15 .x4 .x15,
  eorR .x12 .x12 .x15, eorR .x15 .x11 .x3, eorR .x15 .x15 .x7, ldS .x13 6, eorR .x13 .x13 .x14,
  ldS .x14 13, stS 6 .x12, eorR .x12 .x14 .x10, andR .x12 .x7 .x12, eorR .x13 .x13 .x12,
  andR .x13 .x5 .x13, eorR .x15 .x15 .x13, ldS .x13 12, eorR .x12 .x14 .x13, eorR .x12 .x12 .x9,
  stS 5 .x8, andR .x8 .x3 .x12, eorR .x11 .x11 .x8, andR .x11 .x5 .x11, stS 14 .x8, ldS .x8 8,
  eorR .x8 .x8 .x11, andR .x8 .x4 .x8, eorR .x15 .x15 .x8, ldS .x8 10, eorR .x8 .x8 .x10,
  ldS .x10 7, andR .x10 .x7 .x10, eorR .x8 .x8 .x10, eorR .x10 .x16 .x3, andR .x10 .x7 .x10,
  eorR .x17 .x17 .x10, andR .x17 .x5 .x17, eorR .x8 .x8 .x17, ldS .x17 4, eorR .x12 .x12 .x17,
  andR .x3 .x3 .x6, eorR .x14 .x14 .x3, andR .x14 .x7 .x14, eorR .x12 .x12 .x14,
  eorR .x16 .x16 .x13, eorR .x16 .x16 .x9, ldS .x14 14, eorR .x16 .x16 .x14, ldS .x14 5,
  eorR .x14 .x14 .x13, eorR .x14 .x14 .x9, andR .x7 .x7 .x14, eorR .x16 .x16 .x7, andR .x5 .x5 .x16,
  eorR .x12 .x12 .x5, andR .x4 .x4 .x12, eorR .x6 .x8 .x4, ldS .x3 11, ldS .x4 6, movR .x5 .x15]

/-- The code of S-box 6. -/
def sboxCode5 : List Instr := [
  .movz .x .x9 0 0, .subImm .x .x9 .x9 1, eorR .x10 .x3 .x3, eorR .x11 .x3 .x3, eorR .x11 .x11 .x9,
  eorR .x12 .x7 .x10, eorR .x12 .x12 .x9, andR .x13 .x6 .x12, eorR .x14 .x13 .x4,
  eorR .x15 .x7 .x13, andR .x16 .x4 .x6, eorR .x17 .x15 .x16, andR .x17 .x5 .x17,
  eorR .x14 .x14 .x17, eorR .x17 .x16 .x10, eorR .x17 .x17 .x9, stS 4 .x16, eorR .x16 .x6 .x10,
  eorR .x16 .x16 .x9, stS 5 .x15, andR .x15 .x4 .x16, stS 6 .x16, eorR .x16 .x6 .x15, stS 7 .x15,
  andR .x15 .x5 .x16, eorR .x17 .x17 .x15, andR .x17 .x8 .x17, eorR .x14 .x14 .x17,
  eorR .x17 .x12 .x6, stS 8 .x16, andR .x16 .x4 .x17, stS 9 .x15, eorR .x15 .x13 .x16,
  andR .x15 .x5 .x15, andR .x6 .x6 .x7, stS 10 .x11, eorR .x11 .x12 .x6, stS 11 .x12,
  eorR .x12 .x17 .x10, eorR .x12 .x12 .x9, eorR .x12 .x12 .x16, andR .x12 .x5 .x12,
  eorR .x12 .x11 .x12, andR .x12 .x8 .x12, eorR .x15 .x15 .x12, andR .x15 .x3 .x15,
  eorR .x14 .x14 .x15, andR .x15 .x4 .x13, eorR .x12 .x6 .x15, andR .x7 .x4 .x7, stS 12 .x14,
  ldS .x14 10, eorR .x14 .x14 .x7, stS 10 .x11, andR .x11 .x5 .x14, eorR .x12 .x12 .x11, ldS .x11 5,
  stS 13 .x16, ldS .x16 7, eorR .x11 .x11 .x16, andR .x7 .x5 .x7, eorR .x11 .x11 .x7,
  andR .x11 .x8 .x11, eorR .x12 .x12 .x11, andR .x11 .x5 .x4, eorR .x14 .x14 .x11, ldS .x11 6,
  eorR .x11 .x11 .x15, stS 6 .x15, ldS .x15 11, stS 5 .x7, andR .x7 .x4 .x15, stS 14 .x6,
  andR .x6 .x5 .x7, eorR .x11 .x11 .x6, andR .x11 .x8 .x11, eorR .x14 .x14 .x11, andR .x14 .x3 .x14,
  eorR .x12 .x12 .x14, eorR .x17 .x17 .x16, ldS .x14 4, eorR .x15 .x15 .x14, andR .x15 .x5 .x15,
  eorR .x17 .x17 .x15, eorR .x15 .x13 .x10, eorR .x15 .x15 .x9, ldS .x14 14, andR .x11 .x4 .x14,
  eorR .x11 .x15 .x11, ldS .x6 13, andR .x6 .x5 .x6, eorR .x11 .x11 .x6, andR .x11 .x8 .x11,
  eorR .x17 .x17 .x11, ldS .x11 5, eorR .x11 .x11 .x10, eorR .x11 .x11 .x9, ldS .x10 6,
  eorR .x13 .x13 .x10, eorR .x14 .x14 .x4, andR .x14 .x5 .x14, eorR .x13 .x13 .x14,
  andR .x13 .x8 .x13, eorR .x11 .x11 .x13, andR .x11 .x3 .x11, eorR .x17 .x17 .x11, ldS .x11 10,
  eorR .x13 .x11 .x4, ldS .x14 9, eorR .x13 .x13 .x14, ldS .x14 8, andR .x10 .x8 .x14,
  eorR .x13 .x13 .x10, eorR .x16 .x15 .x16, andR .x16 .x5 .x16, eorR .x14 .x14 .x16,
  andR .x4 .x4 .x15, eorR .x15 .x15 .x4, eorR .x11 .x11 .x7, andR .x5 .x5 .x11, eorR .x15 .x15 .x5,
  andR .x8 .x8 .x15, eorR .x14 .x14 .x8, andR .x3 .x3 .x14, eorR .x6 .x13 .x3, ldS .x3 12,
  movR .x4 .x12, movR .x5 .x17]

/-- The code of S-box 7. -/
def sboxCode6 : List Instr := [
  .movz .x .x9 0 0, .subImm .x .x9 .x9 1, eorR .x10 .x3 .x3, eorR .x11 .x3 .x3, eorR .x11 .x11 .x9,
  eorR .x12 .x8 .x3, andR .x13 .x3 .x8, andR .x14 .x5 .x13, eorR .x15 .x12 .x14,
  eorR .x16 .x13 .x10, eorR .x16 .x16 .x9, andR .x17 .x5 .x16, stS 4 .x14, eorR .x14 .x11 .x17,
  stS 5 .x12, andR .x12 .x6 .x14, eorR .x15 .x15 .x12, eorR .x12 .x8 .x10, eorR .x12 .x12 .x9,
  stS 6 .x8, andR .x8 .x3 .x12, stS 7 .x12, andR .x12 .x5 .x8, stS 8 .x8, eorR .x8 .x11 .x12,
  stS 9 .x11, andR .x11 .x6 .x16, eorR .x8 .x8 .x11, andR .x8 .x7 .x8, eorR .x15 .x15 .x8,
  andR .x8 .x6 .x17, eorR .x14 .x14 .x8, andR .x8 .x5 .x3, eorR .x8 .x13 .x8, andR .x8 .x7 .x8,
  eorR .x14 .x14 .x8, andR .x14 .x4 .x14, eorR .x15 .x15 .x14, eorR .x14 .x13 .x5, ldS .x8 5,
  stS 10 .x15, eorR .x15 .x8 .x10, eorR .x15 .x15 .x9, stS 11 .x11, eorR .x11 .x15 .x12,
  andR .x11 .x6 .x11, eorR .x14 .x14 .x11, ldS .x11 6, andR .x8 .x5 .x11, stS 12 .x16, ldS .x16 9,
  stS 13 .x17, eorR .x17 .x16 .x8, eorR .x13 .x11 .x13, eorR .x16 .x13 .x12, andR .x16 .x6 .x16,
  eorR .x17 .x17 .x16, andR .x17 .x7 .x17, eorR .x14 .x14 .x17, ldS .x17 7, stS 14 .x12, ldS .x12 8,
  stS 15 .x8, eorR .x8 .x17 .x12, eorR .x3 .x3 .x10, eorR .x3 .x3 .x9, andR .x3 .x5 .x3,
  eorR .x3 .x8 .x3, eorR .x3 .x3 .x16, andR .x16 .x5 .x15, stS 16 .x8, andR .x8 .x6 .x13,
  eorR .x16 .x16 .x8, andR .x16 .x7 .x16, eorR .x3 .x3 .x16, andR .x3 .x4 .x3, eorR .x14 .x14 .x3,
  eorR .x13 .x13 .x10, eorR .x13 .x13 .x9, andR .x17 .x5 .x17, eorR .x10 .x13 .x17,
  andR .x3 .x6 .x11, eorR .x10 .x10 .x3, ldS .x16 13, eorR .x15 .x15 .x16, ldS .x16 12, ldS .x8 15,
  eorR .x16 .x16 .x8, andR .x16 .x6 .x16, eorR .x15 .x15 .x16, andR .x15 .x7 .x15,
  eorR .x10 .x10 .x15, ldS .x15 5, andR .x15 .x5 .x15, andR .x15 .x6 .x15, ldS .x16 9,
  eorR .x16 .x16 .x15, ldS .x15 14, andR .x15 .x7 .x15, eorR .x16 .x16 .x15, andR .x16 .x4 .x16,
  eorR .x10 .x10 .x16, eorR .x12 .x12 .x8, ldS .x16 11, eorR .x12 .x12 .x16, eorR .x17 .x11 .x17,
  ldS .x16 16, andR .x5 .x5 .x16, eorR .x16 .x16 .x5, andR .x16 .x6 .x16, eorR .x17 .x17 .x16,
  andR .x17 .x7 .x17, eorR .x12 .x12 .x17, ldS .x17 4, eorR .x13 .x13 .x17, eorR .x11 .x11 .x5,
  andR .x6 .x6 .x11, eorR .x13 .x13 .x6, eorR .x8 .x8 .x3, andR .x7 .x7 .x8, eorR .x13 .x13 .x7,
  andR .x4 .x4 .x13, eorR .x6 .x12 .x4, ldS .x3 10, movR .x4 .x14, movR .x5 .x10]

/-- The code of S-box 8. -/
def sboxCode7 : List Instr := [
  .movz .x .x9 0 0, .subImm .x .x9 .x9 1, eorR .x10 .x3 .x3, eorR .x11 .x3 .x3, eorR .x11 .x11 .x9,
  eorR .x12 .x3 .x10, eorR .x12 .x12 .x9, eorR .x13 .x8 .x12, eorR .x6 .x6 .x10, eorR .x6 .x6 .x9,
  eorR .x14 .x13 .x6, eorR .x4 .x4 .x10, eorR .x4 .x4 .x9, eorR .x14 .x14 .x4, andR .x15 .x6 .x3,
  andR .x16 .x12 .x8, andR .x17 .x6 .x16, stS 4 .x3, eorR .x3 .x12 .x17, andR .x3 .x4 .x3,
  eorR .x3 .x15 .x3, eorR .x7 .x7 .x10, eorR .x7 .x7 .x9, andR .x3 .x7 .x3, eorR .x14 .x14 .x3,
  eorR .x3 .x8 .x10, eorR .x3 .x3 .x9, stS 5 .x13, andR .x13 .x12 .x3, stS 6 .x17,
  eorR .x17 .x11 .x13, stS 7 .x13, eorR .x13 .x17 .x15, andR .x13 .x4 .x13, eorR .x12 .x12 .x13,
  eorR .x13 .x8 .x16, stS 8 .x17, andR .x17 .x6 .x13, eorR .x11 .x11 .x17, stS 9 .x15,
  andR .x15 .x4 .x3, eorR .x11 .x11 .x15, andR .x11 .x7 .x11, eorR .x12 .x12 .x11,
  eorR .x5 .x5 .x10, eorR .x5 .x5 .x9, andR .x12 .x5 .x12, eorR .x14 .x14 .x12, eorR .x12 .x16 .x10,
  eorR .x12 .x12 .x9, eorR .x11 .x12 .x17, eorR .x13 .x13 .x10, eorR .x13 .x13 .x9, stS 10 .x14,
  andR .x14 .x6 .x13, eorR .x3 .x3 .x14, andR .x3 .x4 .x3, eorR .x11 .x11 .x3, ldS .x3 6,
  stS 11 .x13, eorR .x13 .x3 .x10, eorR .x13 .x13 .x9, stS 12 .x17, andR .x17 .x4 .x3,
  eorR .x17 .x13 .x17, andR .x17 .x7 .x17, eorR .x11 .x11 .x17, ldS .x17 7, stS 13 .x13,
  eorR .x13 .x8 .x17, stS 14 .x16, ldS .x16 9, eorR .x16 .x13 .x16, stS 9 .x15, ldS .x15 5,
  andR .x15 .x4 .x15, stS 5 .x14, eorR .x14 .x16 .x15, eorR .x16 .x16 .x10, eorR .x16 .x16 .x9,
  eorR .x13 .x13 .x10, eorR .x13 .x13 .x9, andR .x13 .x4 .x13, eorR .x16 .x16 .x13,
  andR .x16 .x7 .x16, eorR .x14 .x14 .x16, andR .x14 .x5 .x14, eorR .x11 .x11 .x14,
  eorR .x14 .x17 .x3, andR .x16 .x6 .x12, eorR .x8 .x8 .x16, andR .x16 .x4 .x8, eorR .x14 .x14 .x16,
  ldS .x16 5, eorR .x16 .x12 .x16, andR .x16 .x7 .x16, eorR .x14 .x14 .x16, ldS .x16 9,
  eorR .x12 .x12 .x16, ldS .x13 14, eorR .x3 .x13 .x3, eorR .x3 .x3 .x16, andR .x3 .x7 .x3,
  eorR .x12 .x12 .x3, andR .x12 .x5 .x12, eorR .x14 .x14 .x12, ldS .x12 13, andR .x12 .x4 .x12,
  eorR .x8 .x8 .x12, andR .x6 .x6 .x17, eorR .x13 .x13 .x6, ldS .x6 4, ldS .x17 12,
  eorR .x6 .x6 .x17, andR .x6 .x4 .x6, eorR .x6 .x13 .x6, andR .x6 .x7 .x6, eorR .x8 .x8 .x6,
  ldS .x6 8, eorR .x6 .x6 .x15, eorR .x13 .x13 .x10, eorR .x13 .x13 .x9, ldS .x10 11,
  andR .x4 .x4 .x10, eorR .x13 .x13 .x4, andR .x7 .x7 .x13, eorR .x6 .x6 .x7, andR .x5 .x5 .x6,
  eorR .x6 .x8 .x5, ldS .x3 10, movR .x4 .x11, movR .x5 .x14]

/-- Six input planes and eight temporary registers; scratch slots 0–3 are reserved. -/
def sboxCode : Nat → List Instr
  | 0 => sboxCode0 | 1 => sboxCode1 | 2 => sboxCode2 | 3 => sboxCode3
  | 4 => sboxCode4 | 5 => sboxCode5 | 6 => sboxCode6 | _ => sboxCode7

#guard (List.range 8).all fun i => sboxCode i ==
  VG.Impl.Aes.AArch64.compile .x2 (Circuit.gates i) sboxIns (sboxOuts i)
    [.x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] .x9 (List.range' 4 48)

def sbox0 : Prog isa := .block (sboxCode 0)
def sbox1 : Prog isa := .block (sboxCode 1)
def sbox2 : Prog isa := .block (sboxCode 2)
def sbox3 : Prog isa := .block (sboxCode 3)
def sbox4 : Prog isa := .block (sboxCode 4)
def sbox5 : Prog isa := .block (sboxCode 5)
def sbox6 : Prog isa := .block (sboxCode 6)
def sbox7 : Prog isa := .block (sboxCode 7)

end VG.Impl.TripleDes.AArch64
