import VerifiedGarbage.Impl.TripleDes.Circuit
import VerifiedGarbage.Impl.Aes.X86.Alloc

/-! Scalar DES Boolean circuits on IA-32. EBP is the scratch base;
ESI/EDI retain the Feistel halves. Inputs and outputs occupy fixed slots
16–21, with spills in slots 22–111. No address depends on a secret. -/
namespace VG.Impl.TripleDes.X86
open VG.X86

def sboxIns : List (Nat × Nat) := (List.range 6).map fun j => (j, 16 + j)
def sboxOuts (i : Nat) : List (Nat × Nat) :=
  (List.range 4).map fun j => ((Circuit.outputs i).getD j 0, 16 + j)

/-! The code of the S-boxes, as `compile` allocates it for their circuits. It is written
out (and `#guard` checks that it is what `compile` produces) so that the kernel, which
evaluates the code in the proofs, does not have to run the allocator. -/

/-! Short forms of the instructions, on slots of the scratch buffer at `ebp`. -/
def movR (d s : Reg) : Instr := .mov d (.reg s)
def movS (d : Reg) (k : Nat) : Instr := .mov d (.mem (VG.Impl.Aes.X86.slotAt .ebp k))
def xorR (d s : Reg) : Instr := .alu .xor d (.reg s)
def xorS (d : Reg) (k : Nat) : Instr := .alu .xor d (.mem (VG.Impl.Aes.X86.slotAt .ebp k))
def andR (d s : Reg) : Instr := .alu .and d (.reg s)
def andS (d : Reg) (k : Nat) : Instr := .alu .and d (.mem (VG.Impl.Aes.X86.slotAt .ebp k))
def notR (d : Reg) : Instr := .alu .xor d (.imm (BitVec.allOnes 32))
def st (k : Nat) (r : Reg) : Instr := .store (VG.Impl.Aes.X86.slotAt .ebp k) r

/-- The code of S-box 1. -/
def sboxCode0 : List Instr := [
  movS .eax 16, xorS .eax 16, movS .ebx 16, xorR .ebx .eax, notR .ebx, movS .ecx 20, andR .ecx .ebx,
  movS .edx 16, xorS .edx 20, st 22 .eax, movS .eax 17, andR .eax .edx, xorR .eax .ecx, st 23 .edx,
  movR .edx .ebx, xorR .edx .ecx, st 24 .ecx, movS .ecx 17, andR .ecx .edx, xorS .ecx 16,
  andS .ecx 21, xorR .eax .ecx, movS .ecx 20, andS .ecx 16, st 25 .edx, movR .edx .ecx,
  xorS .edx 22, notR .edx, st 26 .ebx, movS .ebx 17, andR .ebx .edx, st 27 .edx, movR .edx .ecx,
  xorR .edx .ebx, st 28 .ecx, movS .ecx 20, xorS .ecx 22, notR .ecx, st 29 .eax, movR .eax .ecx,
  xorR .eax .ebx, st 30 .ebx, movS .ebx 21, andR .ebx .eax, xorR .edx .ebx, andS .edx 19,
  xorS .edx 29, movS .ebx 17, andS .ebx 20, st 29 .eax, movS .eax 27, xorR .eax .ebx, st 31 .ebx,
  movS .ebx 17, andR .ebx .ecx, st 32 .ecx, movS .ecx 26, xorR .ecx .ebx, andS .ecx 21,
  xorR .eax .ecx, movS .ecx 17, andS .ecx 26, st 33 .ebx, movS .ebx 25, xorR .ebx .ecx,
  andS .ebx 21, andS .ebx 19, xorR .eax .ebx, andS .eax 18, xorR .edx .eax, movS .eax 26,
  xorS .eax 28, movR .ebx .eax, xorS .ebx 33, st 28 .edx, movS .edx 24, xorS .edx 22, notR .edx,
  andS .eax 17, xorR .eax .edx, st 26 .ecx, movS .ecx 21, andR .ecx .eax, xorR .ebx .ecx,
  movS .ecx 25, xorS .ecx 22, notR .ecx, st 34 .edx, movR .edx .ecx, xorS .edx 33, st 33 .ecx,
  movS .ecx 17, andS .ecx 24, xorS .ecx 24, andS .ecx 21, st 24 .eax, movR .eax .edx,
  xorR .eax .ecx, andS .eax 19, xorR .ebx .eax, xorS .ecx 24, movS .eax 17, andS .eax 16,
  st 24 .edx, movS .edx 34, xorR .edx .eax, andS .edx 21, st 35 .eax, movS .eax 25, xorR .eax .edx,
  andS .eax 19, xorR .ecx .eax, andS .ecx 18, xorR .ebx .ecx, movS .ecx 25, xorS .ecx 35,
  movS .eax 21, andS .eax 24, xorR .ecx .eax, movS .eax 27, xorS .eax 26, st 26 .ebx, movS .ebx 17,
  andS .ebx 33, xorS .ebx 34, andS .ebx 21, xorR .eax .ebx, andS .eax 19, xorR .ecx .eax,
  movS .eax 21, andS .eax 30, xorS .eax 24, movS .ebx 16, xorS .ebx 35, xorR .ebx .edx,
  andS .ebx 19, xorR .eax .ebx, andS .eax 18, xorR .ecx .eax, movS .eax 23, xorS .eax 22, notR .eax,
  xorS .eax 17, movS .ebx 30, xorS .ebx 22, notR .ebx, andS .ebx 21, xorR .ebx .eax, movS .edx 29,
  xorS .edx 22, notR .edx, andS .edx 21, xorS .edx 32, andS .edx 19, xorR .ebx .edx, movS .edx 25,
  xorS .edx 31, andS .edx 21, xorS .edx 35, st 35 .ecx, movS .ecx 25, xorS .ecx 17, andS .ecx 21,
  xorR .eax .ecx, andS .eax 19, xorR .edx .eax, andS .edx 18, xorR .ebx .edx, st 19 .ebx,
  movS .eax 28, st 16 .eax, movS .eax 26, st 17 .eax, movS .eax 35, st 18 .eax]

/-- The code of S-box 2. -/
def sboxCode1 : List Instr := [
  movS .eax 16, xorS .eax 16, movS .ebx 16, xorS .ebx 16, notR .ebx, movS .ecx 21, xorR .ecx .eax,
  notR .ecx, movS .edx 17, andS .edx 21, st 22 .ebx, movS .ebx 21, xorR .ebx .edx, st 23 .edx,
  movS .edx 16, andR .edx .ebx, xorR .edx .ecx, st 24 .ecx, movS .ecx 23, xorR .ecx .eax, notR .ecx,
  st 25 .eax, movS .eax 16, andR .eax .ecx, st 26 .ecx, movR .ecx .ebx, xorR .ecx .eax,
  andS .ecx 20, xorR .edx .ecx, st 27 .eax, movS .eax 17, andS .eax 24, st 28 .ecx, movS .ecx 24,
  xorR .ecx .eax, xorS .ebx 25, notR .ebx, st 29 .eax, movS .eax 16, andR .eax .ebx, st 30 .ebx,
  movR .ebx .ecx, xorR .ebx .eax, st 31 .eax, movR .eax .ecx, xorS .eax 25, notR .eax, st 32 .ecx,
  movS .ecx 16, andR .ecx .eax, xorS .ecx 17, andS .ecx 20, xorR .ebx .ecx, andS .ebx 19,
  xorR .edx .ebx, movS .ebx 16, andS .ebx 29, xorS .ebx 22, movS .ecx 21, xorS .ecx 17, st 33 .eax,
  movS .eax 16, andR .eax .ecx, st 34 .ecx, movS .ecx 17, xorR .ecx .eax, andS .ecx 20,
  xorR .ebx .ecx, andS .ebx 18, xorR .edx .ebx, movS .ebx 34, xorS .ebx 25, notR .ebx, movS .ecx 16,
  andS .ecx 23, st 23 .edx, movR .edx .ebx, xorR .edx .ecx, xorS .eax 30, andS .eax 20,
  xorR .edx .eax, movS .eax 33, xorS .eax 28, andS .eax 19, xorR .edx .eax, movS .eax 16,
  andS .eax 32, xorS .eax 21, andS .eax 20, xorS .eax 26, st 28 .ecx, movS .ecx 16, andS .ecx 24,
  st 33 .ebx, movS .ebx 32, xorR .ebx .ecx, st 32 .ecx, movS .ecx 20, andS .ecx 21, xorR .ebx .ecx,
  andS .ebx 19, xorR .eax .ebx, andS .eax 18, xorR .edx .eax, movS .eax 33, xorS .eax 16,
  xorS .eax 20, movS .ebx 26, xorS .ebx 28, andS .ebx 20, xorS .ebx 16, andS .ebx 19,
  xorR .eax .ebx, movS .ebx 16, andS .ebx 17, movS .ecx 22, xorR .ecx .ebx, st 22 .edx,
  movS .edx 26, xorS .edx 27, andS .edx 20, xorR .ecx .edx, andS .ebx 19, xorR .ecx .ebx,
  andS .ecx 18, xorR .eax .ecx, movS .ecx 33, xorS .ecx 27, movS .ebx 20, andS .ebx 31,
  xorR .ecx .ebx, movS .ebx 28, xorS .ebx 25, notR .ebx, movS .edx 24, xorS .edx 32, andS .edx 20,
  xorR .ebx .edx, andS .ebx 19, xorR .ecx .ebx, movS .ebx 29, xorS .ebx 28, movR .edx .ebx,
  xorS .edx 25, notR .edx, andS .edx 20, xorR .ebx .edx, andS .ebx 18, xorR .ecx .ebx, st 18 .eax,
  st 19 .ecx, movS .eax 23, st 16 .eax, movS .eax 22, st 17 .eax]

/-- The code of S-box 3. -/
def sboxCode2 : List Instr := [
  movS .eax 16, xorS .eax 16, movS .ebx 16, xorS .ebx 16, notR .ebx, movS .ecx 21, xorR .ecx .eax,
  notR .ecx, movS .edx 20, andR .edx .ecx, st 22 .ebx, movS .ebx 21, xorR .ebx .edx, st 23 .edx,
  movS .edx 20, andS .edx 21, st 24 .eax, movR .eax .ecx, xorR .eax .edx, st 25 .ecx, movS .ecx 16,
  andR .ecx .eax, st 26 .edx, movR .edx .ebx, xorR .edx .ecx, st 27 .ebx, movR .ebx .eax,
  xorS .ebx 24, notR .ebx, st 28 .ecx, movS .ecx 16, andS .ecx 26, st 26 .eax, movR .eax .ebx,
  xorR .eax .ecx, st 29 .ebx, movS .ebx 17, andR .ebx .eax, xorR .ebx .edx, st 30 .edx,
  movS .edx 17, andS .edx 26, xorR .eax .edx, andS .eax 19, xorR .ebx .eax, movS .eax 16,
  andS .eax 21, movS .edx 22, xorR .edx .eax, st 22 .eax, movS .eax 17, andS .eax 25,
  xorR .edx .eax, andS .ecx 19, xorR .edx .ecx, andS .edx 18, xorR .ebx .edx, movS .edx 25,
  xorS .edx 20, movR .ecx .edx, xorS .ecx 28, movS .eax 23, xorS .eax 24, notR .eax, st 28 .ebx,
  movS .ebx 16, andS .ebx 23, xorR .ebx .eax, st 31 .edx, movS .edx 17, andR .edx .ebx, st 32 .ebx,
  movR .ebx .ecx, xorR .ebx .edx, st 33 .edx, movS .edx 20, xorS .edx 24, notR .edx, st 34 .eax,
  movS .eax 16, andR .eax .edx, st 35 .edx, movS .edx 20, xorR .edx .eax, st 36 .eax, movS .eax 16,
  andS .eax 25, st 37 .ecx, movS .ecx 25, xorR .ecx .eax, andS .ecx 17, xorR .edx .ecx,
  andS .edx 19, xorR .ebx .edx, movS .edx 30, xorS .edx 24, notR .edx, movS .ecx 37, xorS .ecx 24,
  notR .ecx, andS .ecx 17, xorR .edx .ecx, movS .ecx 27, xorS .ecx 24, notR .ecx, st 37 .ebx,
  movS .ebx 16, andR .ebx .ecx, st 30 .ecx, movS .ecx 34, xorR .ecx .ebx, st 25 .ebx,
  movR .ebx .eax, xorS .ebx 24, notR .ebx, andS .ebx 17, xorR .ecx .ebx, andS .ecx 19,
  xorR .edx .ecx, andS .edx 18, xorS .edx 37, movS .ecx 16, andS .ecx 34, xorS .ecx 29, st 29 .edx,
  movS .edx 32, xorS .edx 24, notR .edx, andS .edx 17, xorR .ecx .edx, movS .edx 32, xorS .edx 33,
  andS .edx 19, xorR .ecx .edx, movS .edx 23, xorS .edx 36, xorR .edx .ebx, movS .ebx 17,
  andS .ebx 22, xorS .ebx 23, andS .ebx 19, xorR .edx .ebx, andS .edx 18, xorR .ecx .edx,
  movS .edx 34, xorS .edx 22, xorS .edx 17, movS .ebx 31, xorS .ebx 24, notR .ebx, andS .ebx 16,
  xorS .ebx 35, andS .ebx 17, xorS .ebx 26, andS .ebx 19, xorR .edx .ebx, movS .ebx 27,
  xorR .ebx .eax, st 27 .ecx, movS .ecx 30, xorS .ecx 25, andS .ecx 17, xorR .ebx .ecx,
  andS .eax 17, xorS .eax 30, andS .eax 19, xorR .ebx .eax, andS .ebx 18, xorR .edx .ebx,
  st 19 .edx, movS .eax 28, st 16 .eax, movS .eax 29, st 17 .eax, movS .eax 27, st 18 .eax]

/-- The code of S-box 4. -/
def sboxCode3 : List Instr := [
  movS .eax 16, xorS .eax 16, movS .ebx 16, xorS .ebx 16, notR .ebx, movS .ecx 19, xorR .ecx .eax,
  notR .ecx, movS .edx 17, andS .edx 19, st 22 .ebx, movR .ebx .ecx, xorR .ebx .edx, st 23 .edx,
  movS .edx 21, andR .edx .ebx, st 24 .ebx, movR .ebx .ecx, xorR .ebx .edx, st 25 .edx,
  movS .edx 19, xorS .edx 17, st 26 .ecx, movR .ecx .edx, xorR .ecx .eax, notR .ecx, st 27 .eax,
  movS .eax 21, andR .eax .ecx, st 28 .ecx, movR .ecx .edx, xorR .ecx .eax, andS .ecx 20,
  xorR .ebx .ecx, movS .ecx 17, xorS .ecx 27, notR .ecx, st 29 .edx, movS .edx 17, xorR .edx .eax,
  st 30 .eax, movS .eax 20, andR .eax .edx, st 31 .edx, movR .edx .ecx, xorR .edx .eax,
  andS .edx 18, xorR .ebx .edx, movS .edx 24, xorS .edx 27, notR .edx, andS .edx 21, xorS .edx 28,
  andS .edx 20, xorS .edx 31, st 31 .eax, movS .eax 23, xorS .eax 27, notR .eax, st 23 .ecx,
  movS .ecx 17, andS .ecx 26, st 32 .ebx, movS .ebx 22, xorR .ebx .ecx, st 22 .ecx, movS .ecx 21,
  andR .ecx .ebx, xorR .eax .ecx, st 33 .ebx, movS .ebx 20, andS .ebx 29, xorR .eax .ebx,
  andS .eax 18, xorR .edx .eax, movS .eax 16, andR .eax .edx, xorS .eax 32, st 32 .eax,
  movS .eax 21, andS .eax 22, st 29 .ebx, movS .ebx 28, xorR .ebx .eax, st 28 .eax, movR .eax .ecx,
  xorS .eax 27, notR .eax, andS .eax 20, xorR .eax .ebx, st 34 .ebx, movS .ebx 22, xorR .ebx .ecx,
  st 35 .ecx, movS .ecx 19, xorS .ecx 30, andS .ecx 20, xorR .ebx .ecx, andS .ebx 18,
  xorR .eax .ebx, xorS .edx 27, notR .edx, andS .edx 16, xorR .eax .edx, movS .edx 24, xorS .edx 35,
  movS .ebx 20, andS .ebx 26, xorR .edx .ebx, xorS .ecx 17, andS .ecx 18, xorR .edx .ecx,
  movS .ecx 34, xorS .ecx 27, notR .ecx, movS .ebx 33, xorS .ebx 28, andS .ebx 20, xorR .ecx .ebx,
  movS .ebx 23, xorS .ebx 25, xorS .ebx 29, andS .ebx 18, xorR .ecx .ebx, movS .ebx 16,
  andR .ebx .ecx, xorR .edx .ebx, movS .ebx 22, xorS .ebx 21, st 29 .edx, movS .edx 19,
  xorS .edx 22, xorS .edx 28, andS .edx 20, xorR .ebx .edx, movS .edx 25, xorS .edx 27, notR .edx,
  xorS .edx 31, andS .edx 18, xorR .ebx .edx, xorS .ecx 27, notR .ecx, andS .ecx 16, xorR .ebx .ecx,
  st 17 .eax, st 19 .ebx, movS .eax 32, st 16 .eax, movS .eax 29, st 18 .eax]

/-- The code of S-box 5. -/
def sboxCode4 : List Instr := [
  movS .eax 16, xorS .eax 16, movS .ebx 16, xorS .ebx 16, notR .ebx, movS .ecx 19, xorR .ecx .eax,
  notR .ecx, movR .edx .ecx, andS .edx 21, st 22 .ecx, movR .ecx .ebx, xorR .ecx .edx, st 23 .ebx,
  movS .ebx 16, xorR .ebx .eax, notR .ebx, st 24 .edx, movR .edx .ebx, andR .edx .ecx, st 25 .ecx,
  movS .ecx 21, xorR .ecx .edx, st 26 .edx, movS .edx 21, xorR .edx .eax, notR .edx, st 27 .ebx,
  movS .ebx 22, andR .ebx .edx, st 28 .ecx, movR .ecx .edx, xorR .ecx .ebx, st 29 .ebx,
  movS .ebx 20, xorR .ebx .eax, notR .ebx, st 30 .eax, movR .eax .ebx, andR .eax .ecx, xorS .eax 28,
  st 31 .ecx, movR .ecx .edx, xorS .ecx 24, st 32 .edx, movR .edx .ebx, andR .edx .ecx,
  xorS .edx 19, st 33 .ecx, movS .ecx 18, xorS .ecx 30, notR .ecx, andR .edx .ecx, xorR .eax .edx,
  movS .edx 27, andS .edx 32, xorS .edx 22, st 34 .eax, movS .eax 21, xorS .eax 22, st 35 .ecx,
  movS .ecx 27, andS .ecx 24, xorR .ecx .eax, andR .ecx .ebx, xorR .edx .ecx, movS .ecx 31,
  xorS .ecx 30, notR .ecx, andS .ecx 27, st 24 .eax, movS .eax 32, xorS .eax 27, andR .eax .ebx,
  xorR .ecx .eax, andS .ecx 35, xorR .edx .ecx, movS .ecx 17, xorS .ecx 30, notR .ecx,
  andR .edx .ecx, xorS .edx 34, movS .eax 27, andS .eax 31, st 34 .edx, movS .edx 25,
  xorR .edx .eax, xorR .edx .ebx, st 36 .eax, movS .eax 29, xorS .eax 30, notR .eax, st 37 .ecx,
  movS .ecx 27, andR .ecx .eax, st 38 .eax, movS .eax 23, xorR .eax .ecx, st 23 .ecx, movS .ecx 27,
  andS .ecx 29, st 29 .edx, movR .edx .ebx, andR .edx .ecx, xorR .eax .edx, andS .eax 35,
  xorS .eax 29, xorS .ecx 33, andR .ecx .ebx, xorS .ecx 19, movS .edx 27, andS .edx 21, st 29 .eax,
  movS .eax 32, xorR .eax .edx, st 32 .edx, movR .edx .ebx, andR .edx .eax, xorS .edx 23,
  andS .edx 35, xorR .ecx .edx, andS .ecx 37, xorS .ecx 29, movS .edx 31, xorS .edx 27,
  xorR .edx .ebx, st 29 .ecx, movS .ecx 38, xorS .ecx 36, st 36 .eax, movS .eax 24, xorS .eax 23,
  andR .eax .ebx, xorR .ecx .eax, andS .ecx 35, xorR .edx .ecx, movS .ecx 24, xorS .ecx 30,
  notR .ecx, movS .eax 27, andR .eax .ecx, st 38 .ecx, movS .ecx 31, xorR .ecx .eax, andS .ecx 35,
  xorS .ecx 25, andS .ecx 37, xorR .edx .ecx, movS .ecx 22, xorS .ecx 23, st 23 .edx,
  movR .edx .ebx, andS .edx 28, xorR .ecx .edx, movS .edx 33, xorS .edx 27, andR .edx .ebx,
  xorS .edx 36, andS .edx 35, xorR .ecx .edx, movS .edx 38, xorS .edx 26, st 26 .ecx, movS .ecx 27,
  andS .ecx 19, xorS .ecx 24, andR .ecx .ebx, xorR .edx .ecx, movS .ecx 33, xorS .ecx 30, notR .ecx,
  xorR .ecx .eax, movS .eax 32, xorS .eax 30, notR .eax, andR .ebx .eax, xorR .ecx .ebx,
  andS .ecx 35, xorR .edx .ecx, andS .edx 37, xorS .edx 26, st 19 .edx, movS .eax 34, st 16 .eax,
  movS .eax 29, st 17 .eax, movS .eax 23, st 18 .eax]

/-- The code of S-box 6. -/
def sboxCode5 : List Instr := [
  movS .eax 16, xorS .eax 16, movS .ebx 16, xorS .ebx 16, notR .ebx, movS .ecx 20, xorR .ecx .eax,
  notR .ecx, movS .edx 19, andR .edx .ecx, st 22 .ebx, movR .ebx .edx, xorS .ebx 17, st 23 .ecx,
  movS .ecx 20, xorR .ecx .edx, st 24 .edx, movS .edx 17, andS .edx 19, st 25 .eax, movR .eax .ecx,
  xorR .eax .edx, andS .eax 18, xorR .ebx .eax, movR .eax .edx, xorS .eax 25, notR .eax, st 26 .edx,
  movS .edx 19, xorS .edx 25, notR .edx, st 27 .ecx, movS .ecx 17, andR .ecx .edx, st 28 .edx,
  movS .edx 19, xorR .edx .ecx, st 29 .ecx, movS .ecx 18, andR .ecx .edx, xorR .eax .ecx,
  andS .eax 21, xorR .ebx .eax, movS .eax 23, xorS .eax 19, st 30 .edx, movS .edx 17,
  andR .edx .eax, st 31 .ecx, movS .ecx 24, xorR .ecx .edx, andS .ecx 18, st 32 .ebx, movS .ebx 19,
  andS .ebx 20, st 33 .ecx, movS .ecx 23, xorR .ecx .ebx, st 34 .ebx, movR .ebx .eax, xorS .ebx 25,
  notR .ebx, xorR .ebx .edx, andS .ebx 18, xorR .ebx .ecx, andS .ebx 21, xorS .ebx 33, andS .ebx 16,
  xorS .ebx 32, st 32 .ebx, movS .ebx 17, andS .ebx 24, st 33 .ecx, movS .ecx 34, xorR .ecx .ebx,
  st 35 .edx, movS .edx 17, andS .edx 20, st 36 .eax, movS .eax 22, xorR .eax .edx, st 22 .ebx,
  movS .ebx 18, andR .ebx .eax, xorR .ecx .ebx, movS .ebx 27, xorS .ebx 29, andS .edx 18,
  xorR .ebx .edx, andS .ebx 21, xorR .ecx .ebx, movS .ebx 18, andS .ebx 17, xorR .eax .ebx,
  movS .ebx 28, xorS .ebx 22, st 28 .edx, movS .edx 17, andS .edx 23, st 27 .ecx, movS .ecx 18,
  andR .ecx .edx, xorR .ebx .ecx, andS .ebx 21, xorR .eax .ebx, andS .eax 16, xorS .eax 27,
  movS .ebx 36, xorS .ebx 29, movS .ecx 23, xorS .ecx 26, andS .ecx 18, xorR .ebx .ecx,
  movS .ecx 24, xorS .ecx 25, notR .ecx, st 26 .eax, movS .eax 17, andS .eax 34, xorR .eax .ecx,
  st 23 .edx, movS .edx 18, andS .edx 35, xorR .eax .edx, andS .eax 21, xorR .ebx .eax,
  movS .eax 28, xorS .eax 25, notR .eax, movS .edx 24, xorS .edx 22, st 22 .ecx, movS .ecx 34,
  xorS .ecx 17, andS .ecx 18, xorR .edx .ecx, andS .edx 21, xorR .eax .edx, andS .eax 16,
  xorR .ebx .eax, movS .eax 33, xorS .eax 17, xorS .eax 31, movS .edx 21, andS .edx 30,
  xorR .eax .edx, movS .edx 22, xorS .edx 29, andS .edx 18, xorS .edx 30, movS .ecx 17,
  andS .ecx 22, xorS .ecx 22, st 22 .ebx, movS .ebx 33, xorS .ebx 23, andS .ebx 18, xorR .ecx .ebx,
  andS .ecx 21, xorR .edx .ecx, andS .edx 16, xorR .eax .edx, st 19 .eax, movS .eax 32, st 16 .eax,
  movS .eax 26, st 17 .eax, movS .eax 22, st 18 .eax]

/-- The code of S-box 7. -/
def sboxCode6 : List Instr := [
  movS .eax 16, xorS .eax 16, movS .ebx 16, xorS .ebx 16, notR .ebx, movS .ecx 21, xorS .ecx 16,
  movS .edx 16, andS .edx 21, st 22 .ebx, movS .ebx 18, andR .ebx .edx, st 23 .edx, movR .edx .ecx,
  xorR .edx .ebx, st 24 .ebx, movS .ebx 23, xorR .ebx .eax, notR .ebx, st 25 .ecx, movS .ecx 18,
  andR .ecx .ebx, st 26 .ebx, movS .ebx 22, xorR .ebx .ecx, st 27 .ecx, movS .ecx 19,
  andR .ecx .ebx, xorR .edx .ecx, movS .ecx 21, xorR .ecx .eax, notR .ecx, st 28 .eax, movS .eax 16,
  andR .eax .ecx, st 29 .ecx, movS .ecx 18, andR .ecx .eax, st 30 .eax, movS .eax 22,
  xorR .eax .ecx, st 31 .ecx, movS .ecx 19, andS .ecx 26, xorR .eax .ecx, andS .eax 20,
  xorR .edx .eax, movS .eax 19, andS .eax 27, xorR .ebx .eax, movS .eax 18, andS .eax 16,
  xorS .eax 23, andS .eax 20, xorR .ebx .eax, andS .ebx 17, xorR .edx .ebx, movS .ebx 23,
  xorS .ebx 18, movS .eax 25, xorS .eax 28, notR .eax, st 32 .edx, movR .edx .eax, xorS .edx 31,
  andS .edx 19, xorR .ebx .edx, movS .edx 18, andS .edx 21, st 33 .ecx, movS .ecx 22,
  xorR .ecx .edx, st 34 .edx, movS .edx 21, xorS .edx 23, st 23 .eax, movR .eax .edx, xorS .eax 31,
  andS .eax 19, xorR .ecx .eax, andS .ecx 20, xorR .ebx .ecx, movS .ecx 29, xorS .ecx 30,
  st 35 .ebx, movS .ebx 16, xorS .ebx 28, notR .ebx, andS .ebx 18, xorR .ebx .ecx, xorR .ebx .eax,
  movS .eax 18, andS .eax 23, st 36 .ecx, movS .ecx 19, andR .ecx .edx, xorR .eax .ecx,
  andS .eax 20, xorR .ebx .eax, andS .ebx 17, xorS .ebx 35, xorS .edx 28, notR .edx, movS .eax 18,
  andS .eax 29, movR .ecx .edx, xorR .ecx .eax, st 29 .ebx, movS .ebx 19, andS .ebx 21,
  xorR .ecx .ebx, st 28 .ebx, movS .ebx 23, xorS .ebx 27, st 27 .edx, movS .edx 26, xorS .edx 34,
  andS .edx 19, xorR .ebx .edx, andS .ebx 20, xorR .ecx .ebx, movS .ebx 18, andS .ebx 25,
  andS .ebx 19, xorS .ebx 22, movS .edx 20, andS .edx 31, xorR .ebx .edx, andS .ebx 17,
  xorR .ecx .ebx, movS .ebx 30, xorS .ebx 34, xorS .ebx 33, xorS .eax 21, movS .edx 18,
  andS .edx 36, st 33 .ecx, movS .ecx 36, xorR .ecx .edx, andS .ecx 19, xorR .eax .ecx,
  andS .eax 20, xorR .ebx .eax, movS .eax 27, xorS .eax 24, xorS .edx 21, andS .edx 19,
  xorR .eax .edx, movS .edx 34, xorS .edx 28, andS .edx 20, xorR .eax .edx, andS .eax 17,
  xorR .ebx .eax, st 19 .ebx, movS .eax 32, st 16 .eax, movS .eax 29, st 17 .eax, movS .eax 33,
  st 18 .eax]

/-- The code of S-box 8. -/
def sboxCode7 : List Instr := [
  movS .eax 16, xorS .eax 16, movS .ebx 16, xorS .ebx 16, notR .ebx, movS .ecx 16, xorR .ecx .eax,
  notR .ecx, movS .edx 21, xorR .edx .ecx, st 22 .ebx, movS .ebx 19, xorR .ebx .eax, notR .ebx,
  st 23 .ecx, movR .ecx .edx, xorR .ecx .ebx, st 24 .edx, movS .edx 17, xorR .edx .eax, notR .edx,
  xorR .ecx .edx, st 25 .ecx, movR .ecx .ebx, andS .ecx 16, st 26 .eax, movS .eax 23, andS .eax 21,
  st 27 .ecx, movR .ecx .ebx, andR .ecx .eax, st 28 .ebx, movS .ebx 23, xorR .ebx .ecx,
  andR .ebx .edx, xorS .ebx 27, st 29 .ecx, movS .ecx 20, xorS .ecx 26, notR .ecx, andR .ebx .ecx,
  xorS .ebx 25, st 25 .ebx, movS .ebx 21, xorS .ebx 26, notR .ebx, st 30 .ecx, movS .ecx 23,
  andR .ecx .ebx, st 31 .ebx, movS .ebx 22, xorR .ebx .ecx, st 32 .ecx, movR .ecx .ebx,
  xorS .ecx 27, andR .ecx .edx, xorS .ecx 23, st 23 .ebx, movS .ebx 21, xorR .ebx .eax, st 33 .eax,
  movS .eax 28, andR .eax .ebx, st 34 .ebx, movS .ebx 22, xorR .ebx .eax, st 22 .eax,
  movR .eax .edx, andS .eax 31, xorR .ebx .eax, andS .ebx 30, xorR .ecx .ebx, movS .ebx 18,
  xorS .ebx 26, notR .ebx, andR .ecx .ebx, xorS .ecx 25, st 25 .ecx, movS .ecx 33, xorS .ecx 26,
  notR .ecx, st 35 .eax, movR .eax .ecx, xorS .eax 22, st 36 .ecx, movS .ecx 34, xorS .ecx 26,
  notR .ecx, st 34 .ebx, movS .ebx 28, andR .ebx .ecx, st 37 .ecx, movS .ecx 31, xorR .ecx .ebx,
  andR .ecx .edx, xorR .eax .ecx, movS .ecx 29, xorS .ecx 26, notR .ecx, st 31 .ebx, movR .ebx .edx,
  andS .ebx 29, xorR .ebx .ecx, andS .ebx 30, xorR .eax .ebx, movS .ebx 21, xorS .ebx 32,
  st 38 .ecx, movR .ecx .ebx, xorS .ecx 27, st 27 .eax, movR .eax .edx, andS .eax 24, st 24 .edx,
  movR .edx .ecx, xorR .edx .eax, xorS .ecx 26, notR .ecx, xorS .ebx 26, notR .ebx, andS .ebx 24,
  xorR .ecx .ebx, andS .ecx 30, xorR .edx .ecx, andS .edx 34, xorS .edx 27, movS .ecx 32,
  xorS .ecx 29, movS .ebx 28, andS .ebx 36, xorS .ebx 21, st 27 .edx, movS .edx 24, andR .edx .ebx,
  xorR .ecx .edx, movS .edx 36, xorS .edx 31, andS .edx 30, xorR .ecx .edx, movS .edx 36,
  xorS .edx 35, st 36 .eax, movS .eax 33, xorS .eax 29, xorS .eax 35, andS .eax 30, xorR .edx .eax,
  andS .edx 34, xorR .ecx .edx, movS .edx 24, andS .edx 38, xorR .ebx .edx, movS .edx 28,
  andS .edx 32, xorS .edx 33, movS .eax 16, xorS .eax 22, andS .eax 24, xorR .eax .edx,
  andS .eax 30, xorR .ebx .eax, movS .eax 23, xorS .eax 36, xorS .edx 26, notR .edx, st 26 .ecx,
  movS .ecx 24, andS .ecx 37, xorR .edx .ecx, andS .edx 30, xorR .eax .edx, andS .eax 34,
  xorR .ebx .eax, st 19 .ebx, movS .eax 25, st 16 .eax, movS .eax 27, st 17 .eax, movS .eax 26,
  st 18 .eax]

def sboxCode : Nat → List Instr
  | 0 => sboxCode0 | 1 => sboxCode1 | 2 => sboxCode2 | 3 => sboxCode3
  | 4 => sboxCode4 | 5 => sboxCode5 | 6 => sboxCode6 | _ => sboxCode7

#guard (List.range 8).all fun i => sboxCode i ==
  VG.Impl.Aes.X86.compile .ebp (Circuit.gates i) sboxIns (sboxOuts i)
    [.eax, .ebx, .ecx, .edx] (List.range' 22 90)

def sbox0 : Prog isa := .block (sboxCode 0)
def sbox1 : Prog isa := .block (sboxCode 1)
def sbox2 : Prog isa := .block (sboxCode 2)
def sbox3 : Prog isa := .block (sboxCode 3)
def sbox4 : Prog isa := .block (sboxCode 4)
def sbox5 : Prog isa := .block (sboxCode 5)
def sbox6 : Prog isa := .block (sboxCode 6)
def sbox7 : Prog isa := .block (sboxCode 7)
end VG.Impl.TripleDes.X86
