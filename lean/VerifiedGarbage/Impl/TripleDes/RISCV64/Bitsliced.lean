module

public import VerifiedGarbage.Impl.TripleDes.BitsliceLayout
public import VerifiedGarbage.Impl.Words.RISCV64.Word64
public import VerifiedGarbage.Impl.Words.RISCV64.Loops
public import VerifiedGarbage.Spec.TripleDes
meta import VerifiedGarbage.Impl.TripleDes.BitsliceLayout
import VerifiedGarbage.Impl.TripleDes.RISCV64.BitsliceAlloc
meta import VerifiedGarbage.Impl.TripleDes.RISCV64.BitsliceAlloc

/-!
# Bitsliced Triple DES ECB on RISC-V

`vg_triple_des_ecb_{en,de}crypt(schedule = a0, data = a1, n = a2)`.

Constant-time Triple DES on 64 blocks at a time, bitsliced in 64-bit words
(Biham's bitslicing; the S-box circuits are Rusakov's, `BitsliceCircuit`),
as x86-64's scalar code does (`Impl/TripleDes/X86_64/Bitsliced.lean`).
Everything lives in a frame of `frameBytes` on the stack, at `s0`: the 64
state words (`stOff`), a copy of the schedules (`schedOff`), the
transposition's masks (`maskOff`) and the callee-saved registers and `ra`
(`savedOff`), which the code uses.

* Up to 64 blocks are copied into the state words a byte at a time (the
  model faults on misaligned accesses, and the contracts state no alignment
  for the data) and transposed in place, so that word `j` holds bit `j` of
  every block (`BitsliceLayout`); IP only renames words. The words of the
  other lanes hold whatever they held: their results are not stored.
* A round loads its key into `a5` and steps the key pointer `a3`. S-box
  `j`'s input `i` is key bit `inBit j i` as a mask (shifted to the top and
  arithmetically back), XORed with the state word of `E`. Each S-box's
  circuit then runs in registers (`BitsliceAlloc`), and its four outputs are
  XORed into the state words of `L` that P sends them to. Rounds alternate
  between reading the words of `R` (`.ba`) and of `L` (`.ab`), so no word
  moves; a pass of sixteen rounds, eight times both (counted in `a4`), ends
  by exchanging the halves, as DES's swap and the next pass's IP do.
* The three passes are unrolled, each with its schedule component and key
  direction.
* The state is transposed back and the blocks copied out; the data pointer
  `a1` and the blocks left `a2` advance.

The schedule is copied once, as the round keys are read a doubleword at a
time. The frame is zeroed, but for the saved registers, before they come
back. Every address and branch depends only on the pointers, `n` and the
loop counters, which stay in registers (memory is secret to the analysis of
constant time).
-/

@[expose] public section

namespace VG.Impl.TripleDes.RISCV64.Bitslice

open VG.RISCV64 VG.Impl.TripleDes.Bitslice
open VG.Impl.Words.RISCV64 (li64 copyLoop fillLoop)
open VG.Spec.TripleDes (Direction)

/-! ## Registers and the frame -/

/-- The frame's base. -/
def base : Reg := .s0
/-- The round key's pointer, the pairs of rounds left, the round key and a
temporary for the state words. -/
def keyPtr : Reg := .a3
def pairs : Reg := .a4
def key : Reg := .a5
def tmp : Reg := .a6

/-- State word `j`. -/
def stOff (j : Nat) : Nat := 8 * j
/-- The schedules' copy. -/
def schedOff : Nat := 512
/-- The transposition's six masks. -/
def maskOff : Nat := 896
/-- The saved registers. -/
def savedOff : Nat := 944
/-- The frame's bytes. -/
def frameBytes : Nat := 1056

/-- The registers the code saves, and their offsets from `savedOff`; the
frame's base last. -/
def saved : List (Reg × Nat) :=
  [(.s1, 0), (.s2, 8), (.s3, 16), (.s4, 24), (.s5, 32), (.s6, 40), (.s7, 48), (.s8, 56), (.s9, 64),
   (.s10, 72), (.s11, 80), (.ra, 88), (.s0, 96)]

/-! ## S-boxes -/

def inRegs : List Reg := [.t0, .t1, .t2, .t3, .t4, .t5]
def freeRegs : List Reg :=
  [.t6, .a0, .a7, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11, .ra]
def inReg (i : Nat) : Reg := inRegs.getD i .t0

/-! The code of the S-boxes, as `compile` allocates it for their circuits. It is written
out (and `#guard` checks that it is what `compile` produces) so that the kernel, which
evaluates the code in the proofs, does not have to run the allocator. -/

/-- The code of S-box 1. -/
def sboxCode0 : List Instr := [
  .logic .or .t6 .t5 .t1, .logic .xor .t6 .t6 .t1, .logic .xor .a0 .t2 .t6, .logic .or .a7 .t3 .t0,
  .logic .xor .s1 .t5 .t3, .logic .and .s2 .a7 .s1, .logic .xor .s3 .t2 .s2,
  .logic .or .s4 .s3 .a0, .logic .xor .s4 .s4 .a0, .logic .xor .s5 .t1 .t0,
  .logic .xor .s6 .t3 .s5, .logicImm .xor .s6 .s6 (-1), .logic .and .s6 .s6 .a0,
  .logic .or .s2 .t0 .s2, .logic .xor .s6 .s6 .s2, .logic .or .s2 .s6 .s4, .logic .xor .s2 .s2 .s4,
  .logic .or .t0 .t5 .t0, .logic .or .s7 .s6 .t0, .logicImm .xor .s3 .s3 (-1),
  .logic .and .s3 .s3 .t1, .logic .xor .s8 .s7 .s3, .logic .or .t2 .t2 .t0,
  .logic .xor .t2 .t2 .t0, .logic .xor .t2 .s3 .t2, .logicImm .xor .s1 .s1 (-1),
  .logic .and .s1 .s1 .s5, .logic .or .t2 .t2 .s1, .logic .or .t3 .t3 .t6, .logic .xor .t3 .t3 .t6,
  .logic .xor .t6 .a0 .s7, .logic .or .t6 .t6 .t3, .logic .xor .t6 .t6 .t3,
  .logicImm .xor .t3 .t6 (-1), .logic .and .s6 .a7 .s6, .logic .xor .t3 .t3 .s6,
  .logic .or .s8 .s8 .t4, .logic .xor .s8 .s8 .t4, .logic .xor .s8 .s8 .t3,
  .logic .xor .t6 .s5 .t6, .logic .or .s3 .s3 .t6, .logic .xor .s3 .a7 .s3,
  .logic .xor .t5 .t5 .s3, .logic .xor .t3 .t3 .t5, .logic .or .s4 .s4 .t4,
  .logic .xor .s4 .s4 .t3, .logic .xor .a7 .a7 .s7, .logic .or .a7 .t2 .a7,
  .logic .xor .a7 .t5 .a7, .logic .or .s5 .s5 .t3, .logic .xor .s5 .a7 .s5, .logic .or .t3 .s2 .t4,
  .logic .xor .t3 .t3 .s5, .logic .or .t1 .t1 .a0, .logic .or .t1 .t1 .a7, .logic .xor .t1 .t1 .a7,
  .logic .and .s2 .s2 .t5, .logic .xor .t1 .t1 .s2, .logic .or .t1 .t1 .t4,
  .logic .xor .t1 .t1 .t2]

/-- The code of S-box 2. -/
def sboxCode1 : List Instr := [
  .logic .xor .t6 .t4 .t1, .logic .or .a0 .t5 .t0, .logic .xor .a0 .a0 .t0,
  .logicImm .xor .a0 .a0 (-1), .logic .and .a0 .a0 .t1, .logic .or .a7 .t4 .a0,
  .logic .or .s1 .t6 .t0, .logic .xor .s1 .s1 .t0, .logic .and .s2 .t5 .t6,
  .logic .xor .t1 .t1 .s2, .logic .or .s2 .t1 .s1, .logic .xor .s2 .s2 .s1,
  .logic .and .s3 .t3 .t0, .logic .xor .a0 .a0 .s1, .logic .and .a0 .a7 .a0,
  .logic .or .s1 .a0 .s3, .logic .xor .s1 .s1 .s3, .logic .and .s4 .t3 .a0,
  .logicImm .xor .t5 .t5 (-1), .logic .xor .t5 .s4 .t5, .logic .xor .t0 .t0 .t6,
  .logic .or .s5 .t0 .s3, .logic .xor .s5 .s5 .s3, .logic .xor .s6 .t5 .s5,
  .logicImm .xor .s1 .s1 (-1), .logic .and .s1 .s1 .t2, .logic .xor .s1 .s1 .s6,
  .logic .or .t4 .t4 .s5, .logic .xor .t4 .t4 .s5, .logic .xor .t1 .t1 .t4, .logic .or .t5 .t5 .t1,
  .logic .xor .t5 .t5 .t1, .logic .xor .t3 .t3 .t0, .logic .xor .t5 .t5 .t3,
  .logic .or .s5 .a7 .t2, .logic .xor .s5 .s5 .t2, .logic .xor .s5 .s5 .t5,
  .logic .xor .s4 .s4 .t4, .logic .or .t3 .t3 .s4, .logic .xor .a7 .a7 .s6, .logic .or .s3 .s3 .a7,
  .logic .xor .s4 .t3 .s3, .logic .xor .a0 .a0 .s6, .logic .xor .t5 .t5 .a0,
  .logic .and .s3 .s3 .t5, .logic .and .t6 .t6 .t3, .logic .xor .s3 .s3 .t6,
  .logic .or .t6 .s3 .t2, .logic .xor .t6 .t6 .s4, .logic .or .s3 .s3 .t1, .logic .xor .s3 .s3 .t1,
  .logic .or .t0 .t0 .a7, .logic .xor .s3 .s3 .t0, .logic .or .s2 .s2 .t2, .logic .xor .s2 .s2 .s3]

/-- The code of S-box 3. -/
def sboxCode2 : List Instr := [
  .logic .or .t6 .t5 .t4, .logic .xor .t6 .t6 .t4, .logic .xor .a0 .t3 .t0, .logic .or .a7 .t6 .a0,
  .logic .xor .s1 .t2 .t0, .logic .or .s2 .s1 .t5, .logic .xor .s2 .s2 .t5,
  .logic .xor .s3 .a7 .s2, .logic .xor .s4 .t4 .a0, .logic .or .s5 .s4 .t0,
  .logic .xor .s5 .s5 .t0, .logic .xor .a7 .a7 .s5, .logic .or .s5 .s3 .a7,
  .logic .xor .s5 .s5 .a7, .logic .and .s6 .t0 .s3, .logic .or .s6 .t2 .s6,
  .logic .and .s6 .t5 .s6, .logic .xor .s6 .s4 .s6, .logic .or .s7 .s3 .t1,
  .logic .xor .s7 .s7 .t1, .logic .xor .s7 .s7 .s6, .logic .and .a0 .a0 .s1,
  .logic .xor .s1 .t5 .t2, .logic .xor .s8 .a7 .s1, .logic .or .s8 .t3 .s8, .logic .or .s8 .s8 .a0,
  .logic .xor .s8 .s8 .a0, .logic .or .s2 .s2 .s1, .logic .or .s1 .s6 .s2, .logic .xor .s1 .s1 .s2,
  .logic .and .t0 .t2 .t0, .logic .or .a0 .t0 .t4, .logic .xor .a0 .a0 .t4,
  .logic .xor .s1 .s1 .a0, .logic .and .a7 .a7 .s1, .logic .or .t0 .s4 .t0, .logic .or .t0 .t0 .a7,
  .logic .xor .t0 .t0 .a7, .logic .xor .t5 .t5 .t0, .logic .and .s8 .s8 .t1,
  .logic .xor .s8 .s8 .t5, .logicImm .xor .s3 .s3 (-1), .logic .or .t4 .t4 .s3,
  .logic .or .t3 .t3 .t4, .logic .xor .s4 .s4 .t3, .logic .xor .s2 .s2 .s4,
  .logicImm .xor .s5 .s5 (-1), .logic .and .s5 .s5 .t1, .logic .xor .s5 .s5 .s2,
  .logic .and .t2 .t2 .s3, .logic .xor .s6 .s6 .t2, .logic .or .s4 .s4 .s6,
  .logic .xor .t6 .t6 .t5, .logic .xor .s4 .s4 .t6, .logic .or .s1 .s1 .t1,
  .logic .xor .s1 .s1 .s4]

/-- The code of S-box 4. -/
def sboxCode3 : List Instr := [
  .logic .xor .t5 .t5 .t3, .logic .xor .t3 .t3 .t1, .logic .or .t6 .t4 .t2,
  .logic .xor .t6 .t1 .t6, .logicImm .xor .t6 .t6 (-1), .logic .and .t6 .t6 .t3,
  .logic .or .a0 .t3 .t4, .logic .xor .a0 .a0 .t4, .logic .xor .a7 .t2 .a0, .logic .or .s1 .t5 .a7,
  .logic .or .s1 .s1 .t6, .logic .xor .s1 .s1 .t6, .logic .xor .s2 .t4 .s1,
  .logic .and .a7 .a7 .s2, .logic .or .t3 .t3 .a7, .logic .xor .t3 .t3 .a7,
  .logic .xor .t5 .t5 .s2, .logicImm .xor .t3 .t3 (-1), .logic .and .t3 .t3 .t5,
  .logic .xor .t6 .t6 .t3, .logic .xor .t4 .t4 .t2, .logic .or .t1 .t1 .a0,
  .logic .xor .t5 .t5 .t1, .logic .or .t1 .t5 .t4, .logic .xor .t1 .t1 .t4,
  .logic .xor .s1 .s1 .t1, .logic .or .t1 .t0 .t6, .logic .xor .t1 .t1 .t6,
  .logic .xor .t1 .t1 .s1, .logicImm .xor .s1 .s1 (-1), .logic .or .a0 .t6 .t0,
  .logic .xor .a0 .a0 .t0, .logic .xor .a0 .a0 .s1, .logic .xor .t6 .t6 .s1,
  .logic .or .t6 .t6 .t4, .logic .xor .t6 .t6 .t4, .logic .or .a7 .a7 .t6, .logic .xor .t5 .t5 .a7,
  .logic .or .a7 .s2 .t0, .logic .xor .a7 .a7 .t5, .logic .and .t0 .t0 .s2,
  .logic .xor .t0 .t0 .t5]

/-- The code of S-box 5. -/
def sboxCode4 : List Instr := [
  .logic .or .t6 .t5 .t3, .logic .or .a0 .t6 .t0, .logic .xor .a0 .a0 .t0, .logic .xor .a7 .t5 .a0,
  .logic .xor .s1 .t3 .a7, .logic .or .s2 .t2 .s1, .logic .or .a0 .a0 .t2, .logic .xor .a0 .a0 .t2,
  .logic .xor .t3 .t3 .a0, .logic .and .a0 .t1 .t3, .logic .or .s1 .t5 .s1,
  .logic .xor .a0 .a0 .s1, .logic .xor .a0 .t2 .a0, .logic .xor .t0 .t0 .a0,
  .logic .or .s3 .a7 .t0, .logic .and .s4 .t1 .s3, .logic .xor .s5 .a7 .s4,
  .logic .and .s6 .t2 .s1, .logic .xor .s5 .s5 .s6, .logic .or .s3 .s3 .t5,
  .logic .xor .s3 .s3 .t5, .logic .xor .s6 .t3 .s3, .logic .xor .t1 .t1 .s2,
  .logicImm .xor .s6 .s6 (-1), .logic .and .s6 .s6 .t1, .logicImm .xor .s6 .s6 (-1),
  .logic .or .s6 .s6 .t4, .logic .xor .s6 .s6 .t4, .logic .xor .s6 .s6 .a0, .logic .or .a0 .t3 .s4,
  .logic .xor .a0 .a0 .s4, .logic .xor .s3 .s3 .t1, .logic .or .s3 .s5 .s3, .logic .or .s3 .s3 .a0,
  .logic .xor .s3 .s3 .a0, .logic .or .a0 .s2 .s3, .logic .xor .a0 .a0 .s3,
  .logic .and .t0 .t0 .s3, .logic .xor .t1 .t1 .t0, .logic .and .s1 .t3 .s1,
  .logic .or .s1 .t1 .s1, .logic .xor .s4 .s4 .s1, .logic .and .s4 .s4 .t4,
  .logic .xor .s4 .s4 .s5, .logic .xor .t5 .t5 .t6, .logic .xor .s3 .s3 .t5,
  .logic .and .t2 .t2 .t1, .logic .xor .s3 .s3 .t2, .logic .or .a0 .a0 .t4,
  .logic .xor .a0 .a0 .s3, .logic .xor .t3 .s2 .t3, .logic .or .t3 .t3 .s3,
  .logic .xor .t3 .t3 .s3, .logic .xor .a7 .a7 .t1, .logic .xor .t3 .t3 .a7,
  .logic .and .s2 .s2 .t4, .logic .xor .s2 .s2 .t3]

/-- The code of S-box 6. -/
def sboxCode5 : List Instr := [
  .logic .xor .t6 .t4 .t1, .logic .or .a0 .t4 .t0, .logic .and .a0 .t5 .a0,
  .logic .xor .t6 .t6 .a0, .logic .xor .a7 .t0 .t6, .logic .or .s1 .t1 .a7,
  .logic .xor .s1 .s1 .a7, .logic .and .a7 .t5 .a7, .logic .xor .s2 .t4 .a7,
  .logic .xor .s3 .t5 .t3, .logic .or .s4 .s2 .s3, .logic .xor .s5 .t6 .s4,
  .logic .and .s6 .t3 .s5, .logic .or .s7 .s6 .t0, .logic .xor .s7 .s7 .t0, .logic .or .s2 .s1 .s2,
  .logic .xor .s8 .s7 .s2, .logic .and .s9 .s8 .t2, .logic .xor .s9 .s9 .s5,
  .logic .xor .s4 .t4 .s4, .logic .or .s10 .t0 .s4, .logic .xor .s10 .s10 .s4,
  .logic .xor .t3 .t3 .s10, .logic .or .s10 .t1 .s6, .logic .xor .s10 .s10 .s6,
  .logic .or .s10 .t3 .s10, .logic .or .t4 .t4 .s3, .logic .xor .s8 .s8 .t4,
  .logic .or .a0 .a0 .s10, .logic .xor .s8 .s8 .a0, .logic .or .s5 .t5 .s5,
  .logic .and .s2 .s2 .s5, .logic .xor .s2 .t3 .s2, .logicImm .xor .s7 .s7 (-1),
  .logic .and .s7 .s7 .s2, .logic .or .s1 .s1 .t2, .logic .xor .s1 .s1 .s7,
  .logic .xor .t6 .t6 .s2, .logic .or .t1 .t1 .t6, .logic .xor .t1 .t1 .t6,
  .logicImm .xor .t4 .t4 (-1), .logic .xor .s4 .s4 .t4, .logic .xor .t1 .t1 .s4,
  .logic .or .t1 .t1 .t2, .logic .xor .t1 .t1 .t2, .logic .xor .t1 .t1 .s8,
  .logic .xor .t0 .t0 .a7, .logic .xor .t5 .t5 .t3, .logic .and .t0 .t0 .t5,
  .logic .xor .s6 .s6 .s4, .logic .xor .t0 .t0 .s6, .logic .or .s10 .s10 .t2,
  .logic .xor .s10 .s10 .t2, .logic .xor .s10 .s10 .t0]

/-- The code of S-box 7. -/
def sboxCode6 : List Instr := [
  .logic .xor .t6 .t2 .t1, .logic .xor .a0 .t3 .t6, .logic .and .a7 .t0 .a0,
  .logic .and .s1 .t2 .t6, .logic .xor .s2 .t4 .s1, .logic .and .s3 .a7 .s2,
  .logic .and .s4 .t0 .s1, .logic .xor .s5 .t3 .s4, .logic .or .s6 .s2 .s5,
  .logic .xor .t6 .t0 .t6, .logic .xor .s7 .s6 .t6, .logic .or .s8 .t5 .s3,
  .logic .xor .s8 .s8 .s3, .logic .xor .s8 .s8 .s7, .logicImm .xor .a0 .a0 (-1),
  .logic .and .a0 .a0 .t1, .logic .or .s7 .s2 .a0, .logic .xor .s5 .a7 .s5,
  .logic .xor .s7 .s7 .s5, .logic .xor .a7 .a7 .t6, .logic .or .t2 .t2 .a7,
  .logic .xor .t2 .t2 .a7, .logic .or .t6 .s2 .t2, .logic .xor .t6 .t6 .t2,
  .logic .xor .t1 .t1 .s5, .logic .xor .t6 .t6 .t1, .logic .or .a7 .a7 .s4,
  .logic .xor .a7 .a7 .s4, .logic .or .t2 .t2 .a7, .logic .xor .s6 .t4 .s6,
  .logic .and .s6 .t6 .s6, .logic .xor .s6 .t2 .s6, .logic .and .s4 .s6 .t5,
  .logic .xor .s4 .s4 .t6, .logic .or .s2 .s2 .t3, .logic .xor .s2 .s2 .t3, .logic .or .a7 .a7 .s2,
  .logic .or .s1 .s1 .t6, .logic .and .a7 .a7 .s1, .logic .xor .s6 .s6 .a7,
  .logic .xor .a0 .a0 .t2, .logic .and .t0 .t0 .a0, .logic .or .s3 .s3 .t0,
  .logic .xor .a7 .a7 .s3, .logic .or .t0 .a7 .t5, .logic .xor .t0 .t0 .t5,
  .logic .xor .t0 .t0 .s7, .logic .and .t4 .t4 .s3, .logicImm .xor .s7 .s7 (-1),
  .logic .xor .t4 .t4 .s7, .logic .xor .a7 .a7 .t4, .logic .or .s6 .s6 .t5,
  .logic .xor .s6 .s6 .a7]

/-- The code of S-box 8. -/
def sboxCode7 : List Instr := [
  .logic .or .t6 .t3 .t4, .logic .xor .t6 .t6 .t4, .logic .or .a0 .t1 .t3, .logic .xor .a0 .a0 .t3,
  .logic .xor .a0 .t2 .a0, .logic .and .a7 .t5 .a0, .logic .or .s1 .a7 .t6,
  .logic .xor .s1 .s1 .t6, .logic .or .s2 .t4 .a0, .logic .xor .s2 .s2 .a0, .logic .or .s3 .t5 .s2,
  .logic .or .s4 .t4 .t3, .logic .xor .s4 .s4 .t3, .logic .xor .s4 .t1 .s4,
  .logic .and .s5 .s3 .s4, .logic .or .a7 .a7 .s5, .logicImm .xor .a0 .a0 (-1),
  .logic .xor .s5 .s5 .a0, .logic .or .t3 .t3 .s3, .logic .xor .t3 .t3 .s3,
  .logic .xor .s5 .s5 .t3, .logic .xor .t6 .t6 .s5, .logic .or .t3 .s1 .t0,
  .logic .xor .t3 .t3 .t6, .logic .xor .t6 .t5 .t6, .logic .and .s3 .t1 .t6,
  .logic .xor .s5 .t4 .s5, .logic .xor .s3 .s3 .s5, .logic .xor .s2 .s2 .s3,
  .logic .xor .s3 .a7 .s3, .logic .or .t4 .t4 .s3, .logic .xor .t1 .t1 .t6,
  .logic .xor .t4 .t4 .t1, .logic .and .a7 .a7 .t0, .logic .xor .a7 .a7 .t4,
  .logic .xor .s4 .s4 .s2, .logic .or .s5 .t2 .s5, .logic .xor .s5 .s4 .s5,
  .logic .xor .t5 .t5 .s5, .logic .and .t5 .t5 .t0, .logic .xor .t5 .t5 .s2,
  .logic .or .s4 .s4 .t2, .logic .xor .s4 .s4 .t2, .logic .and .t4 .t4 .s4,
  .logic .xor .s1 .s1 .s5, .logic .xor .t4 .t4 .s1, .logic .or .t4 .t4 .t0,
  .logic .xor .t4 .t4 .s2]

/-- Each S-box's code and the registers of its outputs. -/
def sboxCompiled : Nat → List Instr × List Reg
  | 0 => (sboxCode0, [.t1, .s8, .t3, .s4])
  | 1 => (sboxCode1, [.s2, .t6, .s1, .s5])
  | 2 => (sboxCode2, [.s7, .s1, .s8, .s5])
  | 3 => (sboxCode3, [.t0, .a7, .a0, .t1])
  | 4 => (sboxCode4, [.s4, .s6, .s2, .a0])
  | 5 => (sboxCode5, [.s9, .s1, .t1, .s10])
  | 6 => (sboxCode6, [.s8, .s4, .s6, .t0])
  | _ => (sboxCode7, [.t5, .a7, .t3, .t4])

#guard (List.range 8).all fun j =>
  let c := compile (box j) inRegs (outputs j) freeRegs
  c.2.2 && (c.1, c.2.1) == sboxCompiled j

def sboxCode (j : Nat) : List Instr := (sboxCompiled j).1

/-- The registers of each S-box's outputs. -/
def outRegsTable : List (List Reg) := (List.range 8).map fun j => (sboxCompiled j).2

/-- The register of S-box `j`'s output `i`. -/
def outReg (j i : Nat) : Reg := (outRegsTable.getD j []).getD i .t0

/-- S-box `j`'s input `i`: key bit `inBit j i` as a mask, ⊕ the word of `E`. -/
def inputStep (ρ : Role) (j i : Nat) : List Instr :=
  [.shift .sll .d (inReg i) key (63 - inBit j i), .shift .sra .d (inReg i) (inReg i) 63,
   .load .d tmp base (stOff (readWord ρ (eBit (inBit j i)))), .logic .xor (inReg i) (inReg i) tmp]

def inputCode (ρ : Role) (j : Nat) : List Instr := (List.range 6).flatMap (inputStep ρ j)

/-- XOR S-box `j`'s outputs into their words. -/
def outputCode (ρ : Role) (j : Nat) : List Instr :=
  (List.range 4).flatMap fun i =>
    [.load .d tmp base (stOff (writeWord ρ (outBit j i))), .logic .xor tmp tmp (outReg j i),
     .store .d tmp base (stOff (writeWord ρ (outBit j i)))]

def sboxStep (ρ : Role) (j : Nat) : List Instr := inputCode ρ j ++ sboxCode j ++ outputCode ρ j

/-! ## Rounds and passes -/

/-- Load the round key and step the key pointer. -/
def keyLoad (d : Direction) : List Instr :=
  [.load .d key keyPtr 0, .addi keyPtr keyPtr (if d = .encrypt then 8 else -8)]

def round (d : Direction) (ρ : Role) : List Instr := keyLoad d ++ (List.range 8).flatMap (sboxStep ρ)

/-- Two rounds, and the count of pairs left. -/
def roundPair (d : Direction) : List Instr :=
  round d .ba ++ round d .ab ++ ([.addi pairs pairs (-1)] : List Instr)

/-- Exchange the halves. -/
def swapHalves : List Instr :=
  (List.range 32).flatMap fun q =>
    [.load .d .t0 base (stOff (lWord q)), .load .d .t1 base (stOff (rWord q)),
     .store .d .t1 base (stOff (lWord q)), .store .d .t0 base (stOff (rWord q))]

/-- A DES pass with schedule component `c`, in direction `d`. -/
def pass (c : Nat) (d : Direction) : Prog isa :=
  .seq (.block [.addi keyPtr base (schedOff + 128 * c + if d = .encrypt then 0 else 120), .li pairs 8])
    (.seq (.loop (.block (roundPair d)) (.nonzero pairs)) (.block swapHalves))

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

/-- The masks to their words, through `t0` and `t1`. -/
def storeMasks : List Instr :=
  (List.range 6).flatMap fun k =>
    li64 .t0 .t1 (swapMask (maskShifts.getD k 1)) ++ ([.store .d .t0 base (maskOff + 8 * k)] : List Instr)

/-- Exchange the bits `p + s` of `a` and `p` of `b` (`p &&& s = 0`), masked by `m`. -/
def swapBits (a b t m : Reg) (s : Nat) : List Instr :=
  [.shift .srl .d t a s, .logic .xor t t b, .logic .and t t m, .logic .xor b b t,
   .shift .sll .d t t s, .logic .xor a a t]

def groupRegs : List Reg := [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .a7]
def groupReg (k : Nat) : Reg := groupRegs.getD k .t0

/-- Three stages on eight words, the state words `word k`: the stage of
shift `unit * d` pairs the words `k` and `k + d`, for `d` = 4, 2, 1, with
the masks in `s1`, `s2` and `s3`. -/
def group (word : Nat → Nat) (unit : Nat) : List Instr :=
  (List.range 8).map (fun k => .load .d (groupReg k) base (stOff (word k))) ++
  ([(4, Reg.s1), (2, .s2), (1, .s3)].flatMap fun (d, m) =>
    ((List.range 8).filter (fun k => k &&& d = 0)).flatMap fun k =>
      swapBits (groupReg k) (groupReg (k + d)) .s4 m (unit * d)) ++
  (List.range 8).map (fun k => .store .d (groupReg k) base (stOff (word k)))

/-- The masks of words `3 h`–`3 h + 2` into `s1`–`s3`, from `a0`. -/
def masks (h : Nat) : List Instr :=
  [.load .d .s1 .a0 (24 * h), .load .d .s2 .a0 (24 * h + 8), .load .d .s3 .a0 (24 * h + 16)]

/-- Transpose the 64 state words in place, with `a0` at the masks: stages
32, 16, 8 on the words `i + 8 k` of each `i`, then 4, 2, 1 on the words
`8 g + k` of each `g`. -/
def transposeBody : List Instr :=
  masks 0 ++ (List.range 8).flatMap (fun i => group (fun k => i + 8 * k) 8) ++
  masks 1 ++ (List.range 8).flatMap (fun g => group (fun k => 8 * g + k) 1)

/-- `a0` at the masks, and the transposition. -/
def transpose : List Instr := .addi .a0 base maskOff :: transposeBody

/-! ## Batches -/

/-- The batch's bytes, `8 min(n, 64)`, into `s5`. -/
def batchBytes : Prog isa :=
  .seq (.block [.shift .srl .d .t0 .a2 6])
    (.ite (.zero .t0) (.block [.shift .sll .d .s5 .a2 3]) (.block [.li .s5 512]))

/-- Copy `s5` bytes from `src` to `dst`. -/
def copyBytes (src dst : Reg) : Prog isa :=
  .seq (.block [.addi .t2 src 0, .addi .t3 dst 0, .addi .t4 .s5 0]) (copyLoop .t1 .t2 .t3 .t4)

/-- One batch: the next `min(n, 64)` blocks into the state words, through
the three passes, and back; then the next blocks. -/
def batch (d : Direction) : Prog isa :=
  .seq batchBytes (.seq (copyBytes .a1 base)
    (.seq (.block transpose) (.seq (passes d) (.seq (.block transpose) (.seq batchBytes
      (.seq (copyBytes base .a1) (.block [.add .a1 .a1 .s5, .shift .srl .d .t0 .s5 3, .sub .a2 .a2 .t0])))))))

/-! ## The function -/

/-- The registers saved, the frame's base, the schedules copied and the masks stored. -/
def setup : Prog isa :=
  .seq (.block ([.addSp .t0 0] ++ saved.map (fun (r, o) => .store .d r .t0 (savedOff + o)) ++
      [.addi base .t0 0, .addi .t3 base schedOff, .addi .t2 .a0 0, .li .t4 384]))
    (.seq (copyLoop .t1 .t2 .t3 .t4) (.block storeMasks))

/-- The frame zeroed but for the saved registers, and the registers back. -/
def finish : Prog isa :=
  .seq (.block [.li .t1 0, .addi .t0 base 0, .li .t4 (savedOff / 8 : Nat)]) (.seq (fillLoop .t1 .t0 .t4)
    (.block (saved.map fun (r, o) => .load .d r base (savedOff + o))))

def ecb (d : Direction) : Prog isa :=
  .ite (.zero .a2) (.block [])
    (.frame (.alloc frameBytes) (.seq setup (.seq (.loop (batch d) (.nonzero .a2)) finish))
      (.free frameBytes))

def encrypt : Prog isa := ecb .encrypt
def decrypt : Prog isa := ecb .decrypt

end VG.Impl.TripleDes.RISCV64.Bitslice
