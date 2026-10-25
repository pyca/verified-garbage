module

public import VerifiedGarbage.Impl.TripleDes.Circuit
public import VerifiedGarbage.TCB.RISCV64.Isa
public import VerifiedGarbage.Impl.TripleDes.RISCV64.Common
meta import VerifiedGarbage.Impl.TripleDes.Circuit
import VerifiedGarbage.Impl.Aes.RISCV64.Alloc
meta import VerifiedGarbage.Impl.Aes.RISCV64.Alloc
public meta import VerifiedGarbage.TCB.RISCV64.Isa
public meta import VerifiedGarbage.Impl.TripleDes.RISCV64.Common

/-!
# DES S-box circuits on RISC-V

The circuit of S-box `i` (`Circuit.gates i`) on its six input bits, one in
the low bit of each of `t0`–`t5` (`q 0`–`q 5`), leaving its four output bits
in `q 0`–`q 3`, with the temporaries in `t6`, `a7`, `s0` and `s5`–`s11`,
spilling to slots 15–30 of the frame at `s4` (slots 0–14 hold the modes'
state and the saved registers): the code that `compile` allocates for it.
It is written out (and `#guard` checks that it is what `compile` produces)
so that the kernel, which evaluates the code in the proofs, does not have to
run the allocator.
-/

@[expose] public section

namespace VG.Impl.TripleDes.RISCV64

open VG.RISCV64

def q : Nat → Reg
  | 0 => .t0 | 1 => .t1 | 2 => .t2 | 3 => .t3 | 4 => .t4 | _ => .t5

/-- The frame's base, a multiple of 16. -/
def sb : Reg := .s4

def sboxIns : List (Nat × Reg) := (List.range 6).map fun i => (i, q i)

def sboxOuts (i : Nat) : List (Nat × Reg) :=
  (List.range 4).map fun j => ((Circuit.outputs i).getD j 0, q j)

/-- The registers the S-boxes may use for their temporaries. -/
def sboxFree : List Reg := [.t6, .a7, .s0, .s5, .s6, .s7, .s8, .s9, .s10, .s11]

/-- The slots the S-boxes may spill to. -/
def spillSlots : List Nat := List.range' 15 16

/-! Short forms of the instructions, on slots of the frame at `sb`. -/
def xorR (d n m : Reg) : Instr := .logic .xor d n m
def andR (d n m : Reg) : Instr := .logic .and d n m
def notR (d : Reg) : Instr := .logicImm .xor d d (-1)
def ldS (d : Reg) (k : Nat) : Instr := .load .d d sb (8 * k)
def stS (k : Nat) (r : Reg) : Instr := .store .d r sb (8 * k)

/-- The code of S-box 1. -/
def sboxCode0 : List Instr := [
  xorR .t6 .t0 .t0, xorR .a7 .t0 .t6, notR .a7, andR .s0 .t4 .a7, xorR .s5 .t0 .t4,
  andR .s6 .t1 .s5, xorR .s6 .s0 .s6, xorR .s7 .a7 .s0, andR .s8 .t1 .s7, xorR .s8 .t0 .s8,
  andR .s8 .t5 .s8, xorR .s6 .s6 .s8, andR .s8 .t4 .t0, xorR .s9 .s8 .t6, notR .s9,
  andR .s10 .t1 .s9, xorR .s11 .s8 .s10, stS 15 .s5, xorR .s5 .t4 .t6, notR .s5, stS 16 .t0,
  xorR .t0 .s5 .s10, stS 17 .s10, andR .s10 .t5 .t0, xorR .s11 .s11 .s10, andR .s11 .t3 .s11,
  xorR .s6 .s6 .s11, andR .t4 .t1 .t4, xorR .s11 .s9 .t4, andR .s10 .t1 .s5, stS 18 .t4,
  xorR .t4 .a7 .s10, andR .t4 .t5 .t4, xorR .s11 .s11 .t4, andR .t4 .t1 .a7, stS 19 .s5,
  xorR .s5 .s7 .t4, andR .s5 .t5 .s5, andR .s5 .t3 .s5, xorR .s11 .s11 .s5, andR .s11 .t2 .s11,
  xorR .s6 .s6 .s11, xorR .a7 .a7 .s8, xorR .s8 .a7 .s10, xorR .s11 .s0 .t6, notR .s11,
  andR .a7 .t1 .a7, xorR .a7 .s11 .a7, andR .s5 .t5 .a7, xorR .s8 .s8 .s5, xorR .s5 .s7 .t6,
  notR .s5, xorR .s10 .s5 .s10, stS 20 .s6, andR .s6 .t1 .s0, xorR .s0 .s0 .s6, andR .s0 .t5 .s0,
  xorR .s6 .s10 .s0, andR .s6 .t3 .s6, xorR .s8 .s8 .s6, xorR .a7 .a7 .s0, ldS .s0 16,
  andR .s6 .t1 .s0, stS 21 .t0, xorR .t0 .s11 .s6, andR .t0 .t5 .t0, stS 22 .t6,
  xorR .t6 .s7 .t0, andR .t6 .t3 .t6, xorR .a7 .a7 .t6, andR .a7 .t2 .a7, xorR .s8 .s8 .a7,
  xorR .a7 .s7 .s6, andR .t6 .t5 .s10, xorR .a7 .a7 .t6, xorR .s9 .s9 .t4, andR .s5 .t1 .s5,
  xorR .s11 .s11 .s5, andR .s11 .t5 .s11, xorR .s9 .s9 .s11, andR .s9 .t3 .s9, xorR .a7 .a7 .s9,
  ldS .s9 17, andR .s11 .t5 .s9, xorR .s10 .s10 .s11, xorR .s0 .s0 .s6, xorR .s0 .s0 .t0,
  andR .s0 .t3 .s0, xorR .s10 .s10 .s0, andR .s10 .t2 .s10, xorR .a7 .a7 .s10, ldS .s10 15,
  ldS .s0 22, xorR .s10 .s10 .s0, notR .s10, xorR .s10 .s10 .t1, xorR .s9 .s9 .s0, notR .s9,
  andR .s9 .t5 .s9, xorR .s9 .s10 .s9, ldS .t0 21, xorR .t0 .t0 .s0, notR .t0, andR .t0 .t5 .t0,
  ldS .s0 19, xorR .s0 .s0 .t0, andR .s0 .t3 .s0, xorR .s9 .s9 .s0, ldS .s0 18, xorR .s0 .s7 .s0,
  andR .s0 .t5 .s0, xorR .s6 .s6 .s0, xorR .s7 .s7 .t1, andR .t5 .t5 .s7, xorR .s10 .s10 .t5,
  andR .t3 .t3 .s10, xorR .s6 .s6 .t3, andR .t2 .t2 .s6, xorR .t3 .s9 .t2, ldS .t0 20,
  movR .t1 .s8, movR .t2 .a7]

/-- The code of S-box 2. -/
def sboxCode1 : List Instr := [
  xorR .t6 .t0 .t0, xorR .a7 .t0 .t0, notR .a7, xorR .s0 .t5 .t6, notR .s0, andR .s5 .t1 .t5,
  xorR .s6 .t5 .s5, andR .s7 .t0 .s6, xorR .s7 .s0 .s7, xorR .s8 .s5 .t6, notR .s8,
  andR .s9 .t0 .s8, xorR .s10 .s6 .s9, andR .s10 .t4 .s10, xorR .s7 .s7 .s10, andR .s11 .t1 .s0,
  stS 15 .s9, xorR .s9 .s0 .s11, xorR .s6 .s6 .t6, notR .s6, stS 16 .s0, andR .s0 .t0 .s6,
  stS 17 .s8, xorR .s8 .s9 .s0, stS 18 .s0, xorR .s0 .s9 .t6, notR .s0, stS 19 .s9,
  andR .s9 .t0 .s0, xorR .s9 .t1 .s9, andR .s9 .t4 .s9, xorR .s8 .s8 .s9, andR .s8 .t3 .s8,
  xorR .s7 .s7 .s8, andR .s8 .t0 .s11, xorR .s8 .a7 .s8, xorR .s9 .t5 .t1, stS 20 .s11,
  andR .s11 .t0 .s9, stS 21 .a7, xorR .a7 .t1 .s11, andR .a7 .t4 .a7, xorR .s8 .s8 .a7,
  andR .s8 .t2 .s8, xorR .s7 .s7 .s8, xorR .s9 .s9 .t6, notR .s9, andR .s5 .t0 .s5,
  xorR .s8 .s9 .s5, xorR .s6 .s6 .s11, andR .s6 .t4 .s6, xorR .s8 .s8 .s6, xorR .s0 .s0 .s10,
  andR .s0 .t3 .s0, xorR .s8 .s8 .s0, ldS .s0 19, andR .s10 .t0 .s0, xorR .s10 .t5 .s10,
  andR .s10 .t4 .s10, ldS .s6 17, xorR .s10 .s6 .s10, ldS .s11 16, andR .a7 .t0 .s11,
  xorR .s0 .s0 .a7, andR .t5 .t4 .t5, xorR .s0 .s0 .t5, andR .s0 .t3 .s0, xorR .s10 .s10 .s0,
  andR .s10 .t2 .s10, xorR .s8 .s8 .s10, xorR .s10 .s9 .t0, xorR .s10 .s10 .t4, xorR .s0 .s6 .s5,
  andR .s0 .t4 .s0, xorR .s0 .t0 .s0, andR .s0 .t3 .s0, xorR .s10 .s10 .s0, andR .t0 .t0 .t1,
  ldS .t1 21, xorR .t1 .t1 .t0, ldS .s0 15, xorR .s6 .s6 .s0, andR .s6 .t4 .s6, xorR .t1 .t1 .s6,
  andR .t0 .t3 .t0, xorR .t1 .t1 .t0, andR .t1 .t2 .t1, xorR .s10 .s10 .t1, xorR .s9 .s9 .s0,
  ldS .s0 18, andR .s0 .t4 .s0, xorR .s9 .s9 .s0, xorR .s0 .s5 .t6, notR .s0, xorR .s11 .s11 .a7,
  andR .s11 .t4 .s11, xorR .s0 .s0 .s11, andR .t3 .t3 .s0, xorR .s9 .s9 .t3, ldS .t3 20,
  xorR .t3 .t3 .s5, xorR .t6 .t3 .t6, notR .t6, andR .t4 .t4 .t6, xorR .t3 .t3 .t4,
  andR .t2 .t2 .t3, xorR .t3 .s9 .t2, movR .t0 .s7, movR .t1 .s8, movR .t2 .s10]

/-- The code of S-box 3. -/
def sboxCode2 : List Instr := [
  xorR .t6 .t0 .t0, xorR .a7 .t0 .t0, notR .a7, xorR .s0 .t5 .t6, notR .s0, andR .s5 .t4 .s0,
  xorR .s6 .t5 .s5, andR .s7 .t4 .t5, xorR .s8 .s0 .s7, andR .s9 .t0 .s8, xorR .s10 .s6 .s9,
  xorR .s11 .s8 .t6, notR .s11, andR .s7 .t0 .s7, stS 15 .s6, xorR .s6 .s11 .s7, stS 16 .s11,
  andR .s11 .t1 .s6, xorR .s11 .s10 .s11, stS 17 .s10, andR .s10 .t1 .s8, xorR .s6 .s6 .s10,
  andR .s6 .t3 .s6, xorR .s11 .s11 .s6, andR .t5 .t0 .t5, xorR .a7 .a7 .t5, andR .s6 .t1 .s0,
  xorR .a7 .a7 .s6, andR .s7 .t3 .s7, xorR .a7 .a7 .s7, andR .a7 .t2 .a7, xorR .s11 .s11 .a7,
  xorR .a7 .s0 .t4, xorR .s9 .a7 .s9, xorR .s7 .s5 .t6, notR .s7, andR .s6 .t0 .s5,
  xorR .s6 .s7 .s6, andR .s10 .t1 .s6, stS 18 .s11, xorR .s11 .s9 .s10, stS 19 .s8,
  xorR .s8 .t4 .t6, notR .s8, stS 20 .a7, andR .a7 .t0 .s8, xorR .t4 .t4 .a7, stS 21 .s8,
  andR .s8 .t0 .s0, xorR .s0 .s0 .s8, andR .s0 .t1 .s0, xorR .t4 .t4 .s0, andR .t4 .t3 .t4,
  xorR .s11 .s11 .t4, ldS .t4 17, xorR .t4 .t4 .t6, notR .t4, xorR .s9 .s9 .t6, notR .s9,
  andR .s9 .t1 .s9, xorR .t4 .t4 .s9, ldS .s9 15, xorR .s0 .s9 .t6, notR .s0, andR .s9 .t0 .s0,
  stS 17 .s0, xorR .s0 .s7 .s9, stS 22 .s9, xorR .s9 .s8 .t6, notR .s9, andR .s9 .t1 .s9,
  xorR .s0 .s0 .s9, andR .s0 .t3 .s0, xorR .t4 .t4 .s0, andR .t4 .t2 .t4, xorR .s11 .s11 .t4,
  andR .t4 .t0 .s7, ldS .s0 16, xorR .s0 .s0 .t4, xorR .t4 .s6 .t6, notR .t4, andR .t4 .t1 .t4,
  xorR .s0 .s0 .t4, xorR .s6 .s6 .s10, andR .s6 .t3 .s6, xorR .s0 .s0 .s6, xorR .a7 .s5 .a7,
  xorR .a7 .a7 .s9, andR .s9 .t1 .t5, xorR .s5 .s5 .s9, andR .s5 .t3 .s5, xorR .a7 .a7 .s5,
  andR .a7 .t2 .a7, xorR .s0 .s0 .a7, xorR .s7 .s7 .t5, xorR .s7 .s7 .t1, ldS .t5 20,
  xorR .t5 .t5 .t6, notR .t5, andR .t0 .t0 .t5, ldS .t5 21, xorR .t5 .t5 .t0, andR .t5 .t1 .t5,
  ldS .t0 19, xorR .t0 .t0 .t5, andR .t0 .t3 .t0, xorR .s7 .s7 .t0, ldS .t0 15, xorR .t0 .t0 .s8,
  ldS .t5 17, ldS .t6 22, xorR .t6 .t5 .t6, andR .t6 .t1 .t6, xorR .t0 .t0 .t6, andR .t1 .t1 .s8,
  xorR .t5 .t5 .t1, andR .t3 .t3 .t5, xorR .t0 .t0 .t3, andR .t2 .t2 .t0, xorR .t3 .s7 .t2,
  ldS .t0 18, movR .t1 .s11, movR .t2 .s0]

/-- The code of S-box 4. -/
def sboxCode3 : List Instr := [
  xorR .t6 .t0 .t0, xorR .a7 .t0 .t0, notR .a7, xorR .s0 .t3 .t6, notR .s0, andR .s5 .t1 .t3,
  xorR .s6 .s0 .s5, andR .s7 .t5 .s6, xorR .s8 .s0 .s7, xorR .s9 .t3 .t1, xorR .s10 .s9 .t6,
  notR .s10, andR .s11 .t5 .s10, stS 15 .s7, xorR .s7 .s9 .s11, andR .s7 .t4 .s7,
  xorR .s8 .s8 .s7, xorR .s7 .t1 .t6, notR .s7, stS 16 .t3, xorR .t3 .t1 .s11, stS 17 .s11,
  andR .s11 .t4 .t3, stS 18 .t0, xorR .t0 .s7 .s11, andR .t0 .t2 .t0, xorR .s8 .s8 .t0,
  xorR .t0 .s6 .t6, notR .t0, andR .t0 .t5 .t0, xorR .t0 .s10 .t0, andR .t0 .t4 .t0,
  xorR .t3 .t3 .t0, xorR .s5 .s5 .t6, notR .s5, andR .t0 .t1 .s0, xorR .a7 .a7 .t0, stS 19 .s11,
  andR .s11 .t5 .a7, xorR .s5 .s5 .s11, andR .s9 .t4 .s9, xorR .s5 .s5 .s9, andR .s5 .t2 .s5,
  xorR .t3 .t3 .s5, ldS .s5 18, stS 20 .s9, andR .s9 .s5 .t3, xorR .s8 .s8 .s9, andR .s9 .t5 .t0,
  xorR .s10 .s10 .s9, stS 21 .s8, xorR .s8 .s11 .t6, notR .s8, andR .s8 .t4 .s8,
  xorR .s8 .s10 .s8, stS 22 .t5, xorR .t5 .t0 .s11, stS 23 .t0, ldS .t0 16, stS 24 .s7,
  ldS .s7 17, xorR .s7 .t0 .s7, andR .s7 .t4 .s7, xorR .t5 .t5 .s7, andR .t5 .t2 .t5,
  xorR .s8 .s8 .t5, xorR .t3 .t3 .t6, notR .t3, andR .t3 .s5 .t3, xorR .s8 .s8 .t3,
  xorR .s6 .s6 .s11, andR .s0 .t4 .s0, xorR .s6 .s6 .s0, xorR .t1 .t1 .s7, andR .t1 .t2 .t1,
  xorR .s6 .s6 .t1, xorR .s10 .s10 .t6, notR .s10, xorR .a7 .a7 .s9, andR .a7 .t4 .a7,
  xorR .s10 .s10 .a7, ldS .a7 24, ldS .t1 15, xorR .a7 .a7 .t1, ldS .s7 20, xorR .a7 .a7 .s7,
  andR .a7 .t2 .a7, xorR .s10 .s10 .a7, andR .a7 .s5 .s10, xorR .s6 .s6 .a7, ldS .a7 23,
  ldS .s7 22, xorR .s7 .a7 .s7, xorR .t0 .t0 .a7, xorR .t0 .t0 .s9, andR .t4 .t4 .t0,
  xorR .s7 .s7 .t4, xorR .t1 .t1 .t6, notR .t1, ldS .t4 19, xorR .t1 .t1 .t4, andR .t2 .t2 .t1,
  xorR .s7 .s7 .t2, xorR .s10 .s10 .t6, notR .s10, andR .s5 .s5 .s10, xorR .t3 .s7 .s5,
  ldS .t0 21, movR .t1 .s8, movR .t2 .s6]

/-- The code of S-box 5. -/
def sboxCode4 : List Instr := [
  xorR .t6 .t0 .t0, xorR .a7 .t0 .t0, notR .a7, xorR .s0 .t3 .t6, notR .s0, andR .s5 .s0 .t5,
  xorR .s6 .a7 .s5, xorR .t0 .t0 .t6, notR .t0, andR .s7 .t0 .s6, xorR .s8 .t5 .s7,
  xorR .s9 .t5 .t6, notR .s9, andR .s10 .s0 .s9, xorR .s11 .s9 .s10, xorR .t4 .t4 .t6, notR .t4,
  stS 15 .s7, andR .s7 .t4 .s11, xorR .s7 .s8 .s7, stS 16 .s8, xorR .s8 .s9 .s5, stS 17 .a7,
  andR .a7 .t4 .s8, xorR .a7 .t3 .a7, xorR .t2 .t2 .t6, notR .t2, andR .a7 .t2 .a7,
  xorR .s7 .s7 .a7, andR .a7 .t0 .s9, xorR .a7 .s0 .a7, stS 18 .t3, xorR .t3 .t5 .s0,
  andR .s5 .t0 .s5, xorR .s5 .t3 .s5, andR .s5 .t4 .s5, xorR .a7 .a7 .s5, xorR .s5 .s11 .t6,
  notR .s5, andR .s5 .t0 .s5, stS 19 .s0, xorR .s0 .s9 .t0, andR .s0 .t4 .s0, xorR .s5 .s5 .s0,
  andR .s5 .t2 .s5, xorR .a7 .a7 .s5, xorR .t1 .t1 .t6, notR .t1, andR .a7 .t1 .a7,
  xorR .s7 .s7 .a7, andR .a7 .t0 .s11, xorR .s5 .s6 .a7, xorR .s5 .s5 .t4, xorR .s0 .s10 .t6,
  notR .s0, stS 20 .s7, andR .s7 .t0 .s0, stS 21 .s6, ldS .s6 17, xorR .s6 .s6 .s7,
  andR .s10 .t0 .s10, stS 17 .t6, andR .t6 .t4 .s10, xorR .s6 .s6 .t6, andR .s6 .t2 .s6,
  xorR .s5 .s5 .s6, xorR .s10 .s8 .s10, andR .s10 .t4 .s10, ldS .s6 18, xorR .s10 .s6 .s10,
  andR .t5 .t0 .t5, xorR .s9 .s9 .t5, andR .t6 .t4 .s9, xorR .t6 .s7 .t6, andR .t6 .t2 .t6,
  xorR .s10 .s10 .t6, andR .s10 .t1 .s10, xorR .s5 .s5 .s10, xorR .s10 .s11 .t0,
  xorR .s10 .s10 .t4, xorR .s0 .s0 .a7, xorR .a7 .t3 .s7, andR .a7 .t4 .a7, xorR .s0 .s0 .a7,
  andR .s0 .t2 .s0, xorR .s10 .s10 .s0, ldS .s0 17, xorR .a7 .t3 .s0, notR .a7, andR .t6 .t0 .a7,
  xorR .s11 .s11 .t6, andR .s11 .t2 .s11, stS 22 .s5, ldS .s5 21, xorR .s5 .s5 .s11,
  andR .s5 .t1 .s5, xorR .s10 .s10 .s5, ldS .s5 19, xorR .s5 .s5 .s7, ldS .s7 16,
  andR .s7 .t4 .s7, xorR .s5 .s5 .s7, xorR .s7 .s8 .t0, andR .s7 .t4 .s7, xorR .s9 .s9 .s7,
  andR .s9 .t2 .s9, xorR .s5 .s5 .s9, ldS .s9 15, xorR .a7 .a7 .s9, andR .t0 .t0 .s6,
  xorR .t3 .t3 .t0, andR .t3 .t4 .t3, xorR .a7 .a7 .t3, xorR .s8 .s8 .s0, notR .s8,
  xorR .s8 .s8 .t6, xorR .t5 .t5 .s0, notR .t5, andR .t4 .t4 .t5, xorR .s8 .s8 .t4,
  andR .t2 .t2 .s8, xorR .a7 .a7 .t2, andR .t1 .t1 .a7, xorR .t3 .s5 .t1, ldS .t0 20, ldS .t1 22,
  movR .t2 .s10]

/-- The code of S-box 6. -/
def sboxCode5 : List Instr := [
  xorR .t6 .t0 .t0, xorR .a7 .t0 .t0, notR .a7, xorR .s0 .t4 .t6, notR .s0, andR .s5 .t3 .s0,
  xorR .s6 .s5 .t1, xorR .s7 .t4 .s5, andR .s8 .t1 .t3, xorR .s9 .s7 .s8, andR .s9 .t2 .s9,
  xorR .s6 .s6 .s9, xorR .s9 .s8 .t6, notR .s9, xorR .s10 .t3 .t6, notR .s10, andR .s11 .t1 .s10,
  stS 15 .s8, xorR .s8 .t3 .s11, stS 16 .s10, andR .s10 .t2 .s8, xorR .s9 .s9 .s10,
  andR .s9 .t5 .s9, xorR .s6 .s6 .s9, xorR .s9 .s0 .t3, stS 17 .s8, andR .s8 .t1 .s9,
  stS 18 .s10, xorR .s10 .s5 .s8, andR .s10 .t2 .s10, andR .t3 .t3 .t4, stS 19 .s11,
  xorR .s11 .s0 .t3, stS 20 .s0, xorR .s0 .s9 .t6, notR .s0, xorR .s0 .s0 .s8, andR .s0 .t2 .s0,
  xorR .s0 .s11 .s0, andR .s0 .t5 .s0, xorR .s10 .s10 .s0, andR .s10 .t0 .s10, xorR .s6 .s6 .s10,
  andR .s10 .t1 .s5, xorR .s0 .t3 .s10, andR .t4 .t1 .t4, xorR .a7 .a7 .t4, stS 21 .s6,
  andR .s6 .t2 .a7, xorR .s0 .s0 .s6, ldS .s6 19, xorR .s7 .s7 .s6, andR .t4 .t2 .t4,
  xorR .s7 .s7 .t4, andR .s7 .t5 .s7, xorR .s0 .s0 .s7, andR .s7 .t2 .t1, xorR .a7 .a7 .s7,
  ldS .s7 16, xorR .s7 .s7 .s10, stS 16 .s11, ldS .s11 20, stS 22 .s10, andR .s10 .t1 .s11,
  stS 23 .t4, andR .t4 .t2 .s10, xorR .s7 .s7 .t4, andR .s7 .t5 .s7, xorR .a7 .a7 .s7,
  andR .a7 .t0 .a7, xorR .s0 .s0 .a7, xorR .s9 .s9 .s6, ldS .a7 15, xorR .s11 .s11 .a7,
  andR .s11 .t2 .s11, xorR .s9 .s9 .s11, xorR .s11 .s5 .t6, notR .s11, andR .a7 .t1 .t3,
  xorR .a7 .s11 .a7, andR .s8 .t2 .s8, xorR .a7 .a7 .s8, andR .a7 .t5 .a7, xorR .s9 .s9 .a7,
  ldS .a7 23, xorR .a7 .a7 .t6, notR .a7, ldS .t6 22, xorR .s5 .s5 .t6, xorR .t3 .t3 .t1,
  andR .t3 .t2 .t3, xorR .s5 .s5 .t3, andR .s5 .t5 .s5, xorR .a7 .a7 .s5, andR .a7 .t0 .a7,
  xorR .s9 .s9 .a7, ldS .a7 16, xorR .s5 .a7 .t1, ldS .t3 18, xorR .s5 .s5 .t3, ldS .t3 17,
  andR .t6 .t5 .t3, xorR .s5 .s5 .t6, xorR .s6 .s11 .s6, andR .s6 .t2 .s6, xorR .t3 .t3 .s6,
  andR .t1 .t1 .s11, xorR .s11 .s11 .t1, xorR .a7 .a7 .s10, andR .t2 .t2 .a7, xorR .s11 .s11 .t2,
  andR .t5 .t5 .s11, xorR .t3 .t3 .t5, andR .t0 .t0 .t3, xorR .t3 .s5 .t0, ldS .t0 21,
  movR .t1 .s0, movR .t2 .s9]

/-- The code of S-box 7. -/
def sboxCode6 : List Instr := [
  xorR .t6 .t0 .t0, xorR .a7 .t0 .t0, notR .a7, xorR .s0 .t5 .t0, andR .s5 .t0 .t5,
  andR .s6 .t2 .s5, xorR .s7 .s0 .s6, xorR .s8 .s5 .t6, notR .s8, andR .s9 .t2 .s8,
  xorR .s10 .a7 .s9, andR .s11 .t3 .s10, xorR .s7 .s7 .s11, xorR .s11 .t5 .t6, notR .s11,
  stS 15 .s6, andR .s6 .t0 .s11, stS 16 .s11, andR .s11 .t2 .s6, stS 17 .s6, xorR .s6 .a7 .s11,
  stS 18 .a7, andR .a7 .t3 .s8, xorR .s6 .s6 .a7, andR .s6 .t4 .s6, xorR .s7 .s7 .s6,
  andR .s6 .t3 .s9, xorR .s10 .s10 .s6, andR .s6 .t2 .t0, xorR .s6 .s5 .s6, andR .s6 .t4 .s6,
  xorR .s10 .s10 .s6, andR .s10 .t1 .s10, xorR .s7 .s7 .s10, xorR .s10 .s5 .t2, xorR .s6 .s0 .t6,
  notR .s6, stS 19 .s7, xorR .s7 .s6 .s11, andR .s7 .t3 .s7, xorR .s10 .s10 .s7,
  andR .s7 .t2 .t5, stS 20 .a7, ldS .a7 18, stS 21 .s0, xorR .s0 .a7 .s7, xorR .s5 .t5 .s5,
  xorR .a7 .s5 .s11, andR .a7 .t3 .a7, xorR .s0 .s0 .a7, andR .s0 .t4 .s0, xorR .s10 .s10 .s0,
  ldS .s0 16, stS 22 .s11, ldS .s11 17, stS 23 .s7, xorR .s7 .s0 .s11, xorR .t0 .t0 .t6,
  notR .t0, andR .t0 .t2 .t0, xorR .t0 .s7 .t0, xorR .t0 .t0 .a7, andR .a7 .t2 .s6, stS 24 .s7,
  andR .s7 .t3 .s5, xorR .a7 .a7 .s7, andR .a7 .t4 .a7, xorR .t0 .t0 .a7, andR .t0 .t1 .t0,
  xorR .s10 .s10 .t0, xorR .s5 .s5 .t6, notR .s5, andR .s0 .t2 .s0, xorR .t6 .s5 .s0,
  andR .t0 .t3 .t5, xorR .t6 .t6 .t0, xorR .s6 .s6 .s9, ldS .s9 23, xorR .s8 .s8 .s9,
  andR .s8 .t3 .s8, xorR .s6 .s6 .s8, andR .s6 .t4 .s6, xorR .t6 .t6 .s6, ldS .s6 21,
  andR .s6 .t2 .s6, andR .s6 .t3 .s6, ldS .s8 18, xorR .s8 .s8 .s6, ldS .s6 22, andR .s6 .t4 .s6,
  xorR .s8 .s8 .s6, andR .s8 .t1 .s8, xorR .t6 .t6 .s8, xorR .s11 .s11 .s9, ldS .s8 20,
  xorR .s11 .s11 .s8, xorR .s0 .t5 .s0, ldS .s8 24, andR .t2 .t2 .s8, xorR .s8 .s8 .t2,
  andR .s8 .t3 .s8, xorR .s0 .s0 .s8, andR .s0 .t4 .s0, xorR .s11 .s11 .s0, ldS .s0 15,
  xorR .s5 .s5 .s0, xorR .t5 .t5 .t2, andR .t3 .t3 .t5, xorR .s5 .s5 .t3, xorR .s9 .s9 .t0,
  andR .t4 .t4 .s9, xorR .s5 .s5 .t4, andR .t1 .t1 .s5, xorR .t3 .s11 .t1, ldS .t0 19,
  movR .t1 .s10, movR .t2 .t6]

/-- The code of S-box 8. -/
def sboxCode7 : List Instr := [
  xorR .t6 .t0 .t0, xorR .a7 .t0 .t0, notR .a7, xorR .s0 .t0 .t6, notR .s0, xorR .s5 .t5 .s0,
  xorR .t3 .t3 .t6, notR .t3, xorR .s6 .s5 .t3, xorR .t1 .t1 .t6, notR .t1, xorR .s6 .s6 .t1,
  andR .s7 .t3 .t0, andR .s8 .s0 .t5, andR .s9 .t3 .s8, xorR .s10 .s0 .s9, andR .s10 .t1 .s10,
  xorR .s10 .s7 .s10, xorR .t4 .t4 .t6, notR .t4, andR .s10 .t4 .s10, xorR .s6 .s6 .s10,
  xorR .s10 .t5 .t6, notR .s10, andR .s11 .s0 .s10, stS 15 .t0, xorR .t0 .a7 .s11, stS 16 .s5,
  xorR .s5 .t0 .s7, andR .s5 .t1 .s5, xorR .s0 .s0 .s5, xorR .s5 .t5 .s8, stS 17 .t0,
  andR .t0 .t3 .s5, xorR .a7 .a7 .t0, stS 18 .s7, andR .s7 .t1 .s10, xorR .a7 .a7 .s7,
  andR .a7 .t4 .a7, xorR .s0 .s0 .a7, xorR .t2 .t2 .t6, notR .t2, andR .s0 .t2 .s0,
  xorR .s6 .s6 .s0, xorR .s0 .s8 .t6, notR .s0, xorR .a7 .s0 .t0, xorR .s5 .s5 .t6, notR .s5,
  stS 19 .s6, andR .s6 .t3 .s5, xorR .s10 .s10 .s6, andR .s10 .t1 .s10, xorR .a7 .a7 .s10,
  xorR .s10 .s9 .t6, notR .s10, stS 20 .s5, andR .s5 .t1 .s9, xorR .s5 .s10 .s5,
  andR .s5 .t4 .s5, xorR .a7 .a7 .s5, xorR .s5 .t5 .s11, stS 21 .t0, ldS .t0 18,
  xorR .t0 .s5 .t0, stS 18 .s10, ldS .s10 16, andR .s10 .t1 .s10, stS 16 .s8, xorR .s8 .t0 .s10,
  xorR .t0 .t0 .t6, notR .t0, xorR .s5 .s5 .t6, notR .s5, andR .s5 .t1 .s5, xorR .t0 .t0 .s5,
  andR .t0 .t4 .t0, xorR .s8 .s8 .t0, andR .s8 .t2 .s8, xorR .a7 .a7 .s8, xorR .s8 .s11 .s9,
  andR .t0 .t3 .s0, xorR .t5 .t5 .t0, andR .t0 .t1 .t5, xorR .s8 .s8 .t0, xorR .s6 .s0 .s6,
  andR .s6 .t4 .s6, xorR .s8 .s8 .s6, xorR .s0 .s0 .s7, ldS .s6 16, xorR .s9 .s6 .s9,
  xorR .s9 .s9 .s7, andR .s9 .t4 .s9, xorR .s0 .s0 .s9, andR .s0 .t2 .s0, xorR .s8 .s8 .s0,
  ldS .s0 18, andR .s0 .t1 .s0, xorR .t5 .t5 .s0, andR .t3 .t3 .s11, xorR .s6 .s6 .t3,
  ldS .t3 15, ldS .s11 21, xorR .t3 .t3 .s11, andR .t3 .t1 .t3, xorR .t3 .s6 .t3,
  andR .t3 .t4 .t3, xorR .t5 .t5 .t3, ldS .t3 17, xorR .t3 .t3 .s10, xorR .s6 .s6 .t6, notR .s6,
  ldS .t6 20, andR .t1 .t1 .t6, xorR .s6 .s6 .t1, andR .t4 .t4 .s6, xorR .t3 .t3 .t4,
  andR .t2 .t2 .t3, xorR .t3 .t5 .t2, ldS .t0 19, movR .t1 .a7, movR .t2 .s8]

/-- The S-boxes' code. -/
def sboxCode : Nat → List Instr
  | 0 => sboxCode0 | 1 => sboxCode1 | 2 => sboxCode2 | 3 => sboxCode3
  | 4 => sboxCode4 | 5 => sboxCode5 | 6 => sboxCode6 | _ => sboxCode7

#guard (List.range 8).all fun i => sboxCode i ==
  VG.Impl.Aes.RISCV64.compile sb (Circuit.gates i) sboxIns (sboxOuts i) sboxFree spillSlots

def sbox0 : Prog isa := .block (sboxCode 0)
def sbox1 : Prog isa := .block (sboxCode 1)
def sbox2 : Prog isa := .block (sboxCode 2)
def sbox3 : Prog isa := .block (sboxCode 3)
def sbox4 : Prog isa := .block (sboxCode 4)
def sbox5 : Prog isa := .block (sboxCode 5)
def sbox6 : Prog isa := .block (sboxCode 6)
def sbox7 : Prog isa := .block (sboxCode 7)

end VG.Impl.TripleDes.RISCV64
