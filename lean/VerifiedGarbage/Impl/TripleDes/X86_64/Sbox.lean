module

public import VerifiedGarbage.Impl.TripleDes.Circuit
meta import VerifiedGarbage.Impl.TripleDes.Circuit
public import VerifiedGarbage.Impl.Aes.X86_64.Alloc
meta import VerifiedGarbage.Impl.Aes.X86_64.Alloc

/-!
# Constant-time scalar DES S-boxes on x86-64

Six input planes are in `q 0 … q 5`; the four output planes are returned
in `q 0 … q 3`. These are general-purpose registers, so this is scalar
code. It computes the S-box independently at all 64 bit positions. Scratch
slots 8–55 are fixed spill locations; slots 0–7 are reserved for the block
function's saved registers and intermediate state. Left and right Feistel
halves (`r12`, `r13`) and argument pointers are preserved.
-/

@[expose] public section

namespace VG.Impl.TripleDes.X86_64

open VG.X86_64

def q : Nat → Reg
  | 0 => .rax | 1 => .rcx | 2 => .r8 | 3 => .r9 | 4 => .r10 | _ => .r11

def sboxIns : List (Nat × Reg) := (List.range 6).map fun i => (i, q i)
def sboxOuts (i : Nat) : List (Nat × Reg) :=
  (List.range 4).map fun j => ((Circuit.outputs i).getD j 0, q j)

/-! The code of the S-boxes, as `compile` allocates it for their circuits. It is written
out (and `#guard` checks that it is what `compile` produces) so that the kernel, which
evaluates the code in the proofs, does not have to run the allocator. -/

/-! Short forms of the instructions, on slots of the scratch buffer at `rdx`. -/
def movR (d s : Reg) : Instr := .mov d (.reg s)
def movS (d : Reg) (k : Nat) : Instr := .mov d (.mem (VG.Impl.Aes.X86_64.slotAt .rdx k))
def xorR (d s : Reg) : Instr := .alu .xor d (.reg s)
def xorS (d : Reg) (k : Nat) : Instr := .alu .xor d (.mem (VG.Impl.Aes.X86_64.slotAt .rdx k))
def andR (d s : Reg) : Instr := .alu .and d (.reg s)
def andS (d : Reg) (k : Nat) : Instr := .alu .and d (.mem (VG.Impl.Aes.X86_64.slotAt .rdx k))
def st (k : Nat) (r : Reg) : Instr := .store (VG.Impl.Aes.X86_64.slotAt .rdx k) r
def ones (d : Reg) : Instr := .movImm64 d (BitVec.allOnes 64)

/-- The code of S-box 1. -/
def sboxCode0 : List Instr := [
  ones .rbx, st 8 .rbx, movR .rbx .rax, xorR .rbx .rax, movR .rbp .rax, xorR .rbp .rbx, xorS .rbp 8,
  movR .r14 .r10, andR .r14 .rbp, movR .r15 .rax, xorR .r15 .r10, st 9 .r8, movR .r8 .rcx,
  andR .r8 .r15, xorR .r8 .r14, st 10 .r15, movR .r15 .rbp, xorR .r15 .r14, st 11 .r14,
  movR .r14 .rcx, andR .r14 .r15, xorR .r14 .rax, andR .r14 .r11, xorR .r8 .r14, movR .r14 .r10,
  andR .r14 .rax, st 12 .rax, movR .rax .r14, xorR .rax .rbx, xorS .rax 8, st 13 .r15,
  movR .r15 .rcx, andR .r15 .rax, st 14 .rbp, movR .rbp .r14, xorR .rbp .r15, st 15 .r14,
  movR .r14 .r10, xorR .r14 .rbx, xorS .r14 8, st 16 .rbx, movR .rbx .r14, xorR .rbx .r15,
  st 17 .r15, movR .r15 .r11, andR .r15 .rbx, xorR .rbp .r15, andR .rbp .r9, xorR .r8 .rbp,
  andR .r10 .rcx, movR .rbp .rax, xorR .rbp .r10, movR .r15 .rcx, andR .r15 .r14, st 18 .r10,
  movS .r10 14, xorR .r10 .r15, andR .r10 .r11, xorR .rbp .r10, movR .r10 .rcx, andS .r10 14,
  st 19 .r14, movS .r14 13, xorR .r14 .r10, andR .r14 .r11, andR .r14 .r9, xorR .rbp .r14,
  andS .rbp 9, xorR .r8 .rbp, movS .rbp 14, xorS .rbp 15, movR .r14 .rbp, xorR .r14 .r15, st 15 .r8,
  movS .r8 11, xorS .r8 16, xorS .r8 8, andR .rbp .rcx, xorR .rbp .r8, st 14 .rbx, movR .rbx .r11,
  andR .rbx .rbp, xorR .r14 .rbx, movS .rbx 13, xorS .rbx 16, xorS .rbx 8, xorR .r15 .rbx,
  st 20 .rbx, movR .rbx .rcx, andS .rbx 11, xorS .rbx 11, andR .rbx .r11, st 11 .r10,
  movR .r10 .r15, xorR .r10 .rbx, andR .r10 .r9, xorR .r14 .r10, xorR .rbp .rbx, movR .rbx .rcx,
  andS .rbx 12, movR .r10 .r8, xorR .r10 .rbx, andR .r10 .r11, st 21 .r8, movS .r8 13,
  xorR .r8 .r10, andR .r8 .r9, xorR .rbp .r8, andS .rbp 9, xorR .r14 .rbp, movS .rbp 13,
  xorR .rbp .rbx, movR .r8 .r11, andR .r8 .r15, xorR .rbp .r8, xorS .rax 11, movR .r8 .rcx,
  andS .r8 20, xorS .r8 21, andR .r8 .r11, xorR .rax .r8, andR .rax .r9, xorR .rbp .rax,
  movR .rax .r11, andS .rax 17, xorR .r15 .rax, movS .rax 12, xorR .rax .rbx, xorR .rax .r10,
  andR .rax .r9, xorR .r15 .rax, andS .r15 9, xorR .rbp .r15, movS .r15 10, xorS .r15 16,
  xorS .r15 8, xorR .r15 .rcx, movS .rax 17, xorS .rax 16, xorS .rax 8, andR .rax .r11,
  xorR .rax .r15, movS .r10 14, xorS .r10 16, xorS .r10 8, andR .r10 .r11, xorS .r10 19,
  andR .r10 .r9, xorR .rax .r10, movS .r10 13, xorS .r10 18, andR .r10 .r11, xorR .rbx .r10,
  xorS .rcx 13, andR .r11 .rcx, xorR .r15 .r11, andR .r9 .r15, xorR .rbx .r9, andS .rbx 9,
  xorR .rax .rbx, st 9 .rax, movS .rax 15, movR .rcx .r14, movR .r8 .rbp, movS .r9 9]

/-- The code of S-box 2. -/
def sboxCode1 : List Instr := [
  ones .rbx, st 8 .rbx, movR .rbx .rax, xorR .rbx .rax, movR .rbp .rax, xorR .rbp .rax, xorS .rbp 8,
  movR .r14 .r11, xorR .r14 .rbx, xorS .r14 8, movR .r15 .rcx, andR .r15 .r11, st 9 .r8,
  movR .r8 .r11, xorR .r8 .r15, st 10 .r11, movR .r11 .rax, andR .r11 .r8, xorR .r11 .r14,
  st 11 .rbp, movR .rbp .r15, xorR .rbp .rbx, xorS .rbp 8, st 12 .r15, movR .r15 .rax,
  andR .r15 .rbp, st 13 .rbp, movR .rbp .r8, xorR .rbp .r15, andR .rbp .r10, xorR .r11 .rbp,
  st 14 .r15, movR .r15 .rcx, andR .r15 .r14, st 15 .rbp, movR .rbp .r14, xorR .rbp .r15,
  xorR .r8 .rbx, xorS .r8 8, st 16 .r14, movR .r14 .rax, andR .r14 .r8, st 17 .r8, movR .r8 .rbp,
  xorR .r8 .r14, st 18 .r14, movR .r14 .rbp, xorR .r14 .rbx, xorS .r14 8, st 19 .rbp,
  movR .rbp .rax, andR .rbp .r14, xorR .rbp .rcx, andR .rbp .r10, xorR .r8 .rbp, andR .r8 .r9,
  xorR .r11 .r8, movR .r8 .rax, andR .r8 .r15, xorS .r8 11, movS .rbp 10, xorR .rbp .rcx,
  st 20 .r15, movR .r15 .rax, andR .r15 .rbp, st 21 .r9, movR .r9 .rcx, xorR .r9 .r15,
  andR .r9 .r10, xorR .r8 .r9, andS .r8 9, xorR .r11 .r8, xorR .rbp .rbx, xorS .rbp 8,
  movR .r8 .rax, andS .r8 12, movR .r9 .rbp, xorR .r9 .r8, xorS .r15 17, andR .r15 .r10,
  xorR .r9 .r15, xorS .r14 15, andS .r14 21, xorR .r9 .r14, movR .r14 .rax, andS .r14 19,
  xorS .r14 10, andR .r14 .r10, xorS .r14 13, movR .r15 .rax, andS .r15 16, st 15 .r11,
  movS .r11 19, xorR .r11 .r15, st 19 .r15, movR .r15 .r10, andS .r15 10, xorR .r11 .r15,
  andS .r11 21, xorR .r14 .r11, andS .r14 9, xorR .r9 .r14, movR .r14 .rbp, xorR .r14 .rax,
  xorR .r14 .r10, movS .r11 13, xorR .r11 .r8, andR .r11 .r10, xorR .r11 .rax, andS .r11 21,
  xorR .r14 .r11, andR .rax .rcx, movS .rcx 11, xorR .rcx .rax, movS .r11 13, xorS .r11 14,
  andR .r11 .r10, xorR .rcx .r11, andS .rax 21, xorR .rcx .rax, andS .rcx 9, xorR .r14 .rcx,
  xorS .rbp 14, movR .rcx .r10, andS .rcx 18, xorR .rbp .rcx, movR .rcx .r8, xorR .rcx .rbx,
  xorS .rcx 8, movS .rax 16, xorS .rax 19, andR .rax .r10, xorR .rcx .rax, andS .rcx 21,
  xorR .rbp .rcx, xorS .r8 20, xorR .rbx .r8, xorS .rbx 8, andR .r10 .rbx, xorR .r8 .r10,
  andS .r8 9, xorR .rbp .r8, movS .rax 15, movR .rcx .r9, movR .r8 .r14, movR .r9 .rbp]

/-- The code of S-box 3. -/
def sboxCode2 : List Instr := [
  ones .rbx, st 8 .rbx, movR .rbx .rax, xorR .rbx .rax, movR .rbp .rax, xorR .rbp .rax, xorS .rbp 8,
  movR .r14 .r11, xorR .r14 .rbx, xorS .r14 8, movR .r15 .r10, andR .r15 .r14, st 9 .r8,
  movR .r8 .r11, xorR .r8 .r15, st 10 .r15, movR .r15 .r10, andR .r15 .r11, st 11 .r10,
  movR .r10 .r14, xorR .r10 .r15, st 12 .r14, movR .r14 .rax, andR .r14 .r10, st 13 .rbp,
  movR .rbp .r8, xorR .rbp .r14, st 14 .r8, movR .r8 .r10, xorR .r8 .rbx, xorS .r8 8,
  andR .r15 .rax, st 15 .rbx, movR .rbx .r8, xorR .rbx .r15, st 16 .r8, movR .r8 .rcx,
  andR .r8 .rbx, xorR .r8 .rbp, st 17 .rbp, movR .rbp .rcx, andR .rbp .r10, xorR .rbx .rbp,
  andR .rbx .r9, xorR .r8 .rbx, andR .r11 .rax, movS .rbx 13, xorR .rbx .r11, movR .rbp .rcx,
  andS .rbp 12, xorR .rbx .rbp, andR .r15 .r9, xorR .rbx .r15, andS .rbx 9, xorR .r8 .rbx,
  movS .rbx 12, xorS .rbx 11, xorR .r14 .rbx, movS .r15 10, xorS .r15 15, xorS .r15 8,
  movR .rbp .rax, andS .rbp 10, xorR .rbp .r15, st 13 .r8, movR .r8 .rcx, andR .r8 .rbp, st 18 .r10,
  movR .r10 .r14, xorR .r10 .r8, st 19 .rbx, movS .rbx 11, xorS .rbx 15, xorS .rbx 8, st 20 .r11,
  movR .r11 .rax, andR .r11 .rbx, st 21 .rbx, movS .rbx 11, xorR .rbx .r11, st 11 .r11,
  movR .r11 .rax, andS .r11 12, st 22 .r8, movS .r8 12, xorR .r8 .r11, andR .r8 .rcx, xorR .rbx .r8,
  andR .rbx .r9, xorR .r10 .rbx, movS .rbx 17, xorS .rbx 15, xorS .rbx 8, xorS .r14 15, xorS .r14 8,
  andR .r14 .rcx, xorR .rbx .r14, movS .r14 14, xorS .r14 15, xorS .r14 8, movR .r8 .rax,
  andR .r8 .r14, st 17 .r14, movR .r14 .r15, xorR .r14 .r8, st 12 .r8, movR .r8 .r11, xorS .r8 15,
  xorS .r8 8, andR .r8 .rcx, xorR .r14 .r8, andR .r14 .r9, xorR .rbx .r14, andS .rbx 9,
  xorR .r10 .rbx, movR .rbx .rax, andR .rbx .r15, xorS .rbx 16, movR .r14 .rbp, xorS .r14 15,
  xorS .r14 8, andR .r14 .rcx, xorR .rbx .r14, xorS .rbp 22, andR .rbp .r9, xorR .rbx .rbp,
  movS .rbp 10, xorS .rbp 11, xorR .rbp .r8, movR .r8 .rcx, andS .r8 20, xorS .r8 10, andR .r8 .r9,
  xorR .rbp .r8, andS .rbp 9, xorR .rbx .rbp, xorS .r15 20, xorR .r15 .rcx, movS .rbp 19,
  xorS .rbp 15, xorS .rbp 8, andR .rax .rbp, xorS .rax 21, andR .rax .rcx, xorS .rax 18,
  andR .rax .r9, xorR .r15 .rax, movS .rax 14, xorR .rax .r11, movS .rbp 17, xorS .rbp 12,
  andR .rbp .rcx, xorR .rax .rbp, andR .rcx .r11, xorS .rcx 17, andR .r9 .rcx, xorR .rax .r9,
  andS .rax 9, xorR .r15 .rax, movS .rax 13, movR .rcx .r10, movR .r8 .rbx, movR .r9 .r15]

/-- The code of S-box 4. -/
def sboxCode3 : List Instr := [
  ones .rbx, st 8 .rbx, movR .rbx .rax, xorR .rbx .rax, movR .rbp .rax, xorR .rbp .rax, xorS .rbp 8,
  movR .r14 .r9, xorR .r14 .rbx, xorS .r14 8, movR .r15 .rcx, andR .r15 .r9, st 9 .rax,
  movR .rax .r14, xorR .rax .r15, st 10 .rbp, movR .rbp .r11, andR .rbp .rax, st 11 .r15,
  movR .r15 .r14, xorR .r15 .rbp, st 12 .rbp, movR .rbp .r9, xorR .rbp .rcx, st 13 .r9,
  movR .r9 .rbp, xorR .r9 .rbx, xorS .r9 8, st 14 .r14, movR .r14 .r11, andR .r14 .r9, st 15 .r9,
  movR .r9 .rbp, xorR .r9 .r14, andR .r9 .r10, xorR .r15 .r9, movR .r9 .rcx, xorR .r9 .rbx,
  xorS .r9 8, st 16 .rbp, movR .rbp .rcx, xorR .rbp .r14, st 17 .r14, movR .r14 .r10,
  andR .r14 .rbp, st 18 .rcx, movR .rcx .r9, xorR .rcx .r14, andR .rcx .r8, xorR .r15 .rcx,
  movR .rcx .rax, xorR .rcx .rbx, xorS .rcx 8, andR .rcx .r11, xorS .rcx 15, andR .rcx .r10,
  xorR .rbp .rcx, movS .rcx 11, xorR .rcx .rbx, xorS .rcx 8, st 11 .r14, movS .r14 18, andS .r14 14,
  st 19 .r9, movS .r9 10, xorR .r9 .r14, st 10 .rax, movR .rax .r11, andR .rax .r9, xorR .rcx .rax,
  st 20 .r9, movR .r9 .r10, andS .r9 16, xorR .rcx .r9, andR .rcx .r8, xorR .rbp .rcx, movS .rcx 9,
  andR .rcx .rbp, xorR .r15 .rcx, movR .rcx .r11, andR .rcx .r14, st 16 .r15, movS .r15 15,
  xorR .r15 .rcx, st 15 .r11, movR .r11 .rax, xorR .r11 .rbx, xorS .r11 8, andR .r11 .r10,
  xorR .r11 .r15, st 21 .r9, movR .r9 .r14, xorR .r9 .rax, st 22 .r14, movS .r14 13, xorS .r14 17,
  andR .r14 .r10, xorR .r9 .r14, andR .r9 .r8, xorR .r11 .r9, xorR .rbp .rbx, xorS .rbp 8,
  andS .rbp 9, xorR .r11 .rbp, xorS .rax 10, movR .rbp .r10, andS .rbp 14, xorR .rax .rbp,
  xorS .r14 18, andR .r14 .r8, xorR .rax .r14, xorR .r15 .rbx, xorS .r15 8, movS .r14 20,
  xorR .r14 .rcx, andR .r14 .r10, xorR .r15 .r14, movS .r14 19, xorS .r14 12, xorS .r14 21,
  andR .r14 .r8, xorR .r15 .r14, movS .r14 9, andR .r14 .r15, xorR .rax .r14, movS .r14 22,
  xorS .r14 15, movS .rbp 13, xorS .rbp 22, xorR .rbp .rcx, andR .r10 .rbp, xorR .r14 .r10,
  movS .r10 12, xorR .r10 .rbx, xorS .r10 8, xorS .r10 11, andR .r8 .r10, xorR .r14 .r8,
  xorR .r15 .rbx, xorS .r15 8, andS .r15 9, xorR .r14 .r15, st 9 .rax, movS .rax 16, movR .rcx .r11,
  movS .r8 9, movR .r9 .r14]

/-- The code of S-box 5. -/
def sboxCode4 : List Instr := [
  ones .rbx, st 8 .rbx, movR .rbx .rax, xorR .rbx .rax, movR .rbp .rax, xorR .rbp .rax, xorS .rbp 8,
  movR .r14 .r9, xorR .r14 .rbx, xorS .r14 8, movR .r15 .r14, andR .r15 .r11, st 9 .rcx,
  movR .rcx .rbp, xorR .rcx .r15, xorR .rax .rbx, xorS .rax 8, st 10 .rbp, movR .rbp .rax,
  andR .rbp .rcx, st 11 .rcx, movR .rcx .r11, xorR .rcx .rbp, st 12 .rbp, movR .rbp .r11,
  xorR .rbp .rbx, xorS .rbp 8, st 13 .r11, movR .r11 .r14, andR .r11 .rbp, st 14 .r14,
  movR .r14 .rbp, xorR .r14 .r11, xorR .r10 .rbx, xorS .r10 8, st 15 .r11, movR .r11 .r10,
  andR .r11 .r14, xorR .r11 .rcx, st 16 .rcx, movR .rcx .rbp, xorR .rcx .r15, st 17 .r14,
  movR .r14 .r10, andR .r14 .rcx, xorR .r14 .r9, xorR .r8 .rbx, xorS .r8 8, andR .r14 .r8,
  xorR .r11 .r14, movR .r14 .rax, andR .r14 .rbp, xorS .r14 14, st 18 .r9, movS .r9 13, xorS .r9 14,
  andR .r15 .rax, xorR .r15 .r9, andR .r15 .r10, xorR .r14 .r15, movS .r15 17, xorR .r15 .rbx,
  xorS .r15 8, andR .r15 .rax, st 19 .r9, movR .r9 .rbp, xorR .r9 .rax, andR .r9 .r10,
  xorR .r15 .r9, andR .r15 .r8, xorR .r14 .r15, movS .r15 9, xorR .r15 .rbx, xorS .r15 8,
  andR .r14 .r15, xorR .r11 .r14, movR .r14 .rax, andS .r14 17, movS .r9 11, xorR .r9 .r14,
  xorR .r9 .r10, st 9 .r11, movS .r11 15, xorR .r11 .rbx, xorS .r11 8, st 20 .rbx, movR .rbx .rax,
  andR .rbx .r11, st 21 .r11, movS .r11 10, xorR .r11 .rbx, st 10 .r14, movR .r14 .rax,
  andS .r14 15, st 15 .r15, movR .r15 .r10, andR .r15 .r14, xorR .r11 .r15, andR .r11 .r8,
  xorR .r9 .r11, xorR .r14 .rcx, andR .r14 .r10, xorS .r14 18, movR .r11 .rax, andS .r11 13,
  xorR .rbp .r11, movR .r15 .r10, andR .r15 .rbp, xorR .r15 .rbx, andR .r15 .r8, xorR .r14 .r15,
  andS .r14 15, xorR .r9 .r14, movS .r14 17, xorR .r14 .rax, xorR .r14 .r10, movS .r15 21,
  xorS .r15 10, st 10 .r9, movS .r9 19, xorR .r9 .rbx, andR .r9 .r10, xorR .r15 .r9, andR .r15 .r8,
  xorR .r14 .r15, movS .r15 19, xorS .r15 20, xorS .r15 8, movR .r9 .rax, andR .r9 .r15, st 21 .r11,
  movS .r11 17, xorR .r11 .r9, andR .r11 .r8, xorS .r11 11, andS .r11 15, xorR .r14 .r11,
  xorS .rbx 14, movR .r11 .r10, andS .r11 16, xorR .rbx .r11, movR .r11 .rcx, xorR .r11 .rax,
  andR .r11 .r10, xorR .rbp .r11, andR .rbp .r8, xorR .rbx .rbp, xorS .r15 12, andS .rax 18,
  xorS .rax 19, andR .rax .r10, xorR .r15 .rax, xorS .rcx 20, xorS .rcx 8, xorR .rcx .r9,
  movS .r9 21, xorS .r9 20, xorS .r9 8, andR .r10 .r9, xorR .rcx .r10, andR .r8 .rcx, xorR .r15 .r8,
  andS .r15 15, xorR .rbx .r15, movS .rax 9, movS .rcx 10, movR .r8 .r14, movR .r9 .rbx]

/-- The code of S-box 6. -/
def sboxCode5 : List Instr := [
  ones .rbx, st 8 .rbx, movR .rbx .rax, xorR .rbx .rax, movR .rbp .rax, xorR .rbp .rax, xorS .rbp 8,
  movR .r14 .r10, xorR .r14 .rbx, xorS .r14 8, movR .r15 .r9, andR .r15 .r14, st 9 .rbp,
  movR .rbp .r15, xorR .rbp .rcx, st 10 .rax, movR .rax .r10, xorR .rax .r15, st 11 .r10,
  movR .r10 .rcx, andR .r10 .r9, st 12 .r15, movR .r15 .rax, xorR .r15 .r10, andR .r15 .r8,
  xorR .rbp .r15, movR .r15 .r10, xorR .r15 .rbx, xorS .r15 8, st 13 .r10, movR .r10 .r9,
  xorR .r10 .rbx, xorS .r10 8, st 14 .rax, movR .rax .rcx, andR .rax .r10, st 15 .r10,
  movR .r10 .r9, xorR .r10 .rax, st 16 .rax, movR .rax .r8, andR .rax .r10, xorR .r15 .rax,
  andR .r15 .r11, xorR .rbp .r15, movR .r15 .r14, xorR .r15 .r9, st 17 .r10, movR .r10 .rcx,
  andR .r10 .r15, st 18 .rax, movS .rax 12, xorR .rax .r10, andR .rax .r8, andS .r9 11, st 19 .rcx,
  movR .rcx .r14, xorR .rcx .r9, st 20 .r14, movR .r14 .r15, xorR .r14 .rbx, xorS .r14 8,
  xorR .r14 .r10, andR .r14 .r8, xorR .r14 .rcx, andR .r14 .r11, xorR .rax .r14, andS .rax 10,
  xorR .rbp .rax, movS .rax 19, andS .rax 12, movR .r14 .r9, xorR .r14 .rax, st 21 .rbp,
  movS .rbp 19, andS .rbp 11, st 11 .rcx, movS .rcx 9, xorR .rcx .rbp, st 9 .r10, movR .r10 .r8,
  andR .r10 .rcx, xorR .r14 .r10, movS .r10 14, xorS .r10 16, andR .rbp .r8, xorR .r10 .rbp,
  andR .r10 .r11, xorR .r14 .r10, movR .r10 .r8, andS .r10 19, xorR .rcx .r10, movS .r10 15,
  xorR .r10 .rax, st 15 .rax, movS .rax 19, andS .rax 20, st 14 .rbp, movR .rbp .r8, andR .rbp .rax,
  xorR .r10 .rbp, andR .r10 .r11, xorR .rcx .r10, andS .rcx 10, xorR .r14 .rcx, xorS .r15 16,
  movS .rcx 20, xorS .rcx 13, andR .rcx .r8, xorR .r15 .rcx, movS .rcx 12, xorR .rcx .rbx,
  xorS .rcx 8, movS .r10 19, andR .r10 .r9, xorR .r10 .rcx, movR .rbp .r8, andS .rbp 9,
  xorR .r10 .rbp, andR .r10 .r11, xorR .r15 .r10, xorS .rbx 14, xorS .rbx 8, movS .r10 12,
  xorS .r10 15, xorS .r9 19, andR .r9 .r8, xorR .r10 .r9, andR .r10 .r11, xorR .rbx .r10,
  andS .rbx 10, xorR .r15 .rbx, movS .rbx 11, xorS .rbx 19, xorS .rbx 18, movR .r10 .r11,
  andS .r10 17, xorR .rbx .r10, movR .r10 .rcx, xorS .r10 16, andR .r10 .r8, xorS .r10 17,
  movS .r9 19, andR .r9 .rcx, xorR .rcx .r9, xorS .rax 11, andR .r8 .rax, xorR .rcx .r8,
  andR .r11 .rcx, xorR .r10 .r11, andS .r10 10, xorR .rbx .r10, movS .rax 21, movR .rcx .r14,
  movR .r8 .r15, movR .r9 .rbx]

/-- The code of S-box 7. -/
def sboxCode6 : List Instr := [
  ones .rbx, st 8 .rbx, movR .rbx .rax, xorR .rbx .rax, movR .rbp .rax, xorR .rbp .rax, xorS .rbp 8,
  movR .r14 .r11, xorR .r14 .rax, movR .r15 .rax, andR .r15 .r11, st 9 .rcx, movR .rcx .r8,
  andR .rcx .r15, st 10 .r10, movR .r10 .r14, xorR .r10 .rcx, st 11 .rcx, movR .rcx .r15,
  xorR .rcx .rbx, xorS .rcx 8, st 12 .r14, movR .r14 .r8, andR .r14 .rcx, st 13 .r15,
  movR .r15 .rbp, xorR .r15 .r14, st 14 .r14, movR .r14 .r9, andR .r14 .r15, xorR .r10 .r14,
  movR .r14 .r11, xorR .r14 .rbx, xorS .r14 8, st 15 .r11, movR .r11 .rax, andR .r11 .r14,
  st 16 .r14, movR .r14 .r8, andR .r14 .r11, st 17 .r11, movR .r11 .rbp, xorR .r11 .r14, st 18 .rbp,
  movR .rbp .r9, andR .rbp .rcx, xorR .r11 .rbp, andS .r11 10, xorR .r10 .r11, movR .r11 .r9,
  andS .r11 14, xorR .r15 .r11, movR .r11 .r8, andR .r11 .rax, xorS .r11 13, andS .r11 10,
  xorR .r15 .r11, andS .r15 9, xorR .r10 .r15, movS .r15 13, xorR .r15 .r8, movS .r11 12,
  xorR .r11 .rbx, xorS .r11 8, st 19 .r10, movR .r10 .r11, xorR .r10 .r14, andR .r10 .r9,
  xorR .r15 .r10, movR .r10 .r8, andS .r10 15, st 20 .rbp, movS .rbp 18, xorR .rbp .r10, st 21 .r10,
  movS .r10 15, xorS .r10 13, st 13 .rcx, movR .rcx .r10, xorR .rcx .r14, andR .rcx .r9,
  xorR .rbp .rcx, andS .rbp 10, xorR .r15 .rbp, movS .rbp 16, xorS .rbp 17, xorR .rax .rbx,
  xorS .rax 8, andR .rax .r8, xorR .rax .rbp, xorR .rax .rcx, movR .rcx .r8, andR .rcx .r11,
  st 22 .rbp, movR .rbp .r9, andR .rbp .r10, xorR .rcx .rbp, andS .rcx 10, xorR .rax .rcx,
  andS .rax 9, xorR .r15 .rax, xorR .r10 .rbx, xorS .r10 8, movR .rbx .r8, andS .rbx 16,
  movR .rax .r10, xorR .rax .rbx, movR .rcx .r9, andS .rcx 15, xorR .rax .rcx, xorS .r11 14,
  movS .rbp 13, xorS .rbp 21, andR .rbp .r9, xorR .r11 .rbp, andS .r11 10, xorR .rax .r11,
  movR .r11 .r8, andS .r11 12, andR .r11 .r9, xorS .r11 18, andS .r14 10, xorR .r11 .r14,
  andS .r11 9, xorR .rax .r11, movS .r11 17, xorS .r11 21, xorS .r11 20, xorS .rbx 15, andS .r8 22,
  movS .r14 22, xorR .r14 .r8, andR .r14 .r9, xorR .rbx .r14, andS .rbx 10, xorR .r11 .rbx,
  xorS .r10 11, xorS .r8 15, andR .r9 .r8, xorR .r10 .r9, xorS .rcx 21, andS .rcx 10,
  xorR .r10 .rcx, andS .r10 9, xorR .r11 .r10, st 9 .rax, movS .rax 19, movR .rcx .r15, movS .r8 9,
  movR .r9 .r11]

/-- The code of S-box 8. -/
def sboxCode7 : List Instr := [
  ones .rbx, st 8 .rbx, movR .rbx .rax, xorR .rbx .rax, movR .rbp .rax, xorR .rbp .rax, xorS .rbp 8,
  movR .r14 .rax, xorR .r14 .rbx, xorS .r14 8, movR .r15 .r11, xorR .r15 .r14, xorR .r9 .rbx,
  xorS .r9 8, st 9 .r8, movR .r8 .r15, xorR .r8 .r9, xorR .rcx .rbx, xorS .rcx 8, xorR .r8 .rcx,
  st 10 .r15, movR .r15 .r9, andR .r15 .rax, st 11 .rax, movR .rax .r14, andR .rax .r11, st 12 .rbp,
  movR .rbp .r9, andR .rbp .rax, st 13 .r9, movR .r9 .r14, xorR .r9 .rbp, andR .r9 .rcx,
  xorR .r9 .r15, xorR .r10 .rbx, xorS .r10 8, andR .r9 .r10, xorR .r8 .r9, movR .r9 .r11,
  xorR .r9 .rbx, xorS .r9 8, st 14 .rbp, movR .rbp .r14, andR .rbp .r9, st 15 .r8, movS .r8 12,
  xorR .r8 .rbp, st 16 .rbp, movR .rbp .r8, xorR .rbp .r15, andR .rbp .rcx, xorR .r14 .rbp,
  movR .rbp .r11, xorR .rbp .rax, st 17 .r8, movS .r8 13, andR .r8 .rbp, st 18 .r15, movS .r15 12,
  xorR .r15 .r8, st 12 .r11, movR .r11 .rcx, andR .r11 .r9, xorR .r15 .r11, andR .r15 .r10,
  xorR .r14 .r15, movS .r15 9, xorR .r15 .rbx, xorS .r15 8, andR .r14 .r15, xorS .r14 15,
  st 15 .r14, movR .r14 .rax, xorR .r14 .rbx, xorS .r14 8, st 9 .rax, movR .rax .r14, xorR .rax .r8,
  xorR .rbp .rbx, xorS .rbp 8, st 19 .r8, movS .r8 13, andR .r8 .rbp, xorR .r9 .r8, andR .r9 .rcx,
  xorR .rax .r9, movS .r9 14, xorR .r9 .rbx, xorS .r9 8, st 20 .rbp, movR .rbp .rcx, andS .rbp 14,
  xorR .rbp .r9, andR .rbp .r10, xorR .rax .rbp, movS .rbp 12, xorS .rbp 16, st 21 .r9,
  movR .r9 .rbp, xorS .r9 18, st 18 .r11, movR .r11 .rcx, andS .r11 10, st 10 .r8, movR .r8 .r9,
  xorR .r8 .r11, xorR .r9 .rbx, xorS .r9 8, xorR .rbp .rbx, xorS .rbp 8, andR .rbp .rcx,
  xorR .r9 .rbp, andR .r9 .r10, xorR .r8 .r9, andR .r8 .r15, xorR .rax .r8, movS .r8 16,
  xorS .r8 14, movS .r9 13, andR .r9 .r14, xorS .r9 12, movR .rbp .rcx, andR .rbp .r9,
  xorR .r8 .rbp, movR .rbp .r14, xorS .rbp 10, andR .rbp .r10, xorR .r8 .rbp, xorS .r14 18,
  movS .rbp 9, xorS .rbp 14, xorS .rbp 18, andR .rbp .r10, xorR .r14 .rbp, andR .r14 .r15,
  xorR .r8 .r14, movR .r14 .rcx, andS .r14 21, xorR .r9 .r14, movS .r14 13, andS .r14 16,
  xorS .r14 9, movS .rbp 11, xorS .rbp 19, andR .rbp .rcx, xorR .rbp .r14, andR .rbp .r10,
  xorR .r9 .rbp, xorS .r11 17, xorR .r14 .rbx, xorS .r14 8, andS .rcx 20, xorR .r14 .rcx,
  andR .r10 .r14, xorR .r11 .r10, andR .r15 .r11, xorR .r9 .r15, st 20 .rax, movS .rax 15,
  movS .rcx 20]

def sboxCode : Nat → List Instr
  | 0 => sboxCode0 | 1 => sboxCode1 | 2 => sboxCode2 | 3 => sboxCode3
  | 4 => sboxCode4 | 5 => sboxCode5 | 6 => sboxCode6 | _ => sboxCode7

#guard (List.range 8).all fun i => sboxCode i ==
  VG.Impl.Aes.X86_64.compile .rdx (Circuit.gates i) sboxIns (sboxOuts i)
    [.rbx, .rbp, .r14, .r15] 8 (List.range' 9 47)

def sbox0 : Prog isa := .block (sboxCode 0)
def sbox1 : Prog isa := .block (sboxCode 1)
def sbox2 : Prog isa := .block (sboxCode 2)
def sbox3 : Prog isa := .block (sboxCode 3)
def sbox4 : Prog isa := .block (sboxCode 4)
def sbox5 : Prog isa := .block (sboxCode 5)
def sbox6 : Prog isa := .block (sboxCode 6)
def sbox7 : Prog isa := .block (sboxCode 7)

end VG.Impl.TripleDes.X86_64
