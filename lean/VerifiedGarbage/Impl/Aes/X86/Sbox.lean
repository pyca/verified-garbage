module

public import VerifiedGarbage.Impl.Aes.X86.Alloc
meta import VerifiedGarbage.Impl.Aes.X86.Alloc

/-!
# The bitsliced AES S-box on x86 (32-bit), in general registers

Short forms of the instructions on registers and slots of the scratch buffer
at `edi`, and the circuit `Circuit.sbox` on 32-bit slices: slot `j` holds bit
`j` of 32 bytes, in place, with `eax`, `ebx`, `ecx`, `edx` and `ebp` and
spilling to slots 8–31. It is the code that `compile` produces, written out
(`#guard` checks that it is that) so that the kernel does not have to run
the allocator.
-/

@[expose] public section

namespace VG.Impl.Aes.X86

open VG.X86 VG.Impl.Aes.Circuit

/-- The scratch buffer's base. -/
def sb : Reg := .edi

/-- The registers the S-box and the layers change. -/
def tmpRegs : List Reg := [.eax, .ebx, .ecx, .edx, .ebp]

/-- The slots the S-box may spill to. -/
def spillSlots : List Nat := List.range' 8 24

def sboxIns : List (Nat × Nat) := (List.range 8).map fun i => (x i, i)
def sboxOuts : List (Nat × Nat) := (List.range 8).map fun i => (s i, i)

/-! Short forms, on registers and slots of `sb`. -/

def movR (d s : Reg) : Instr := .mov d (.reg s)
def movS (d : Reg) (k : Nat) : Instr := .mov d (.mem (slotAt sb k))
def xorR (d s : Reg) : Instr := .alu .xor d (.reg s)
def xorS (d : Reg) (k : Nat) : Instr := .alu .xor d (.mem (slotAt sb k))
def andR (d s : Reg) : Instr := .alu .and d (.reg s)
def andS (d : Reg) (k : Nat) : Instr := .alu .and d (.mem (slotAt sb k))
def notR (d : Reg) : Instr := .alu .xor d (.imm (BitVec.allOnes 32))
def st (k : Nat) (r : Reg) : Instr := .store (slotAt sb k) r

/-- The S-box on the slices in slots `0 … 7`, in place. -/
def sboxCode : List Instr := [
  movS .eax 5, xorS .eax 2, movR .ebx .eax, xorS .ebx 1, movR .ecx .ebx, xorS .ecx 6, movR .edx .ebx,
  xorS .edx 0, movR .ebp .ecx, xorS .ebp 3, xorS .ebp 7, st 8 .ebx, movR .ebx .ebp, xorR .ebx .eax, st 9 .eax,
  movR .eax .ebx, xorR .eax .edx, st 10 .ebp, movR .ebp .eax, xorS .ebp 5, st 11 .ebx, movR .ebx .edx,
  xorS .ebx 7, st 12 .edx, movR .edx .eax, xorS .edx 4, st 13 .ebx, movR .ebx .eax, xorR .ebx .ecx, st 14 .ebx,
  movR .ebx .ebp, xorS .ebx 7, st 15 .ebp, movR .ebp .edx, xorR .ebp .ebx, st 16 .ebp, movR .ebp .edx,
  andR .ebp .eax, st 17 .eax, movS .eax 11, xorS .eax 4, st 18 .ebp, movS .ebp 10, xorS .ebp 4, st 19 .ebp,
  movR .ebp .edx, xorS .ebp 10, st 10 .edx, movR .edx .ebx, andR .edx .ecx, st 20 .ecx, movR .ecx .eax,
  andR .ecx .ebp, st 21 .ebp, movR .ebp .eax, xorS .ebp 1, xorR .edx .ecx, st 22 .ebx, movS .ebx 16,
  andS .ebx 14, xorR .ecx .ebx, movS .ebx 14, xorR .ebx .ebp, st 23 .edx, movR .edx .eax, xorS .edx 15,
  st 24 .eax, movS .eax 13, andR .eax .ebp, st 25 .ebp, movR .ebp .edx, andR .ebp .ebx, xorR .eax .ecx,
  xorR .ecx .ebp, movS .ebp 12, andS .ebp 19, st 26 .ebx, movS .ebx 7, andS .ebx 8, xorS .eax 18,
  xorR .ecx .ebp, xorS .ebx 18, xorS .ebp 23, st 18 .edx, movS .edx 22, xorS .edx 6, xorS .eax 9, xorS .ebx 23,
  st 23 .eax, movS .eax 15, andS .eax 6, xorR .ebx .edx, xorR .ebp .eax, movS .eax 15, xorS .eax 8,
  xorR .ebp .eax, xorS .ecx 11, movS .eax 23, xorR .eax .ecx, movR .edx .ebx, andS .edx 23, st 11 .ebx,
  movR .ebx .ecx, xorR .ebx .edx, xorR .edx .ebp, andR .edx .eax, movS .eax 11, xorR .eax .ebp, xorR .edx .ecx,
  st 11 .ebp, movS .ebp 23, xorR .ebp .edx, st 23 .eax, movR .eax .edx, andS .eax 7, st 9 .eax, movR .eax .ebx,
  xorR .eax .edx, andR .ecx .eax, xorR .ebp .ecx, movR .eax .ebp, andS .eax 22, xorR .ecx .ebx, andS .ebx 23,
  xorS .ebx 11, st 11 .eax, movR .eax .ebp, andS .eax 20, andR .ecx .ebx, xorS .ecx 23, st 23 .eax,
  movR .eax .ebx, xorR .eax .ecx, st 20 .ebp, movR .ebp .eax, andS .ebp 18, st 18 .ebp, movR .ebp .ebx,
  xorR .ebp .edx, st 22 .ebx, movR .ebx .ebp, andS .ebx 19, andS .eax 26, st 26 .ebx, movR .ebx .ecx,
  andS .ebx 16, st 16 .ebx, movR .ebx .ebp, andS .ebx 12, xorS .ebx 18, st 12 .ebx, movR .ebx .ecx,
  andS .ebx 14, xorS .ecx 20, xorR .ebp .ecx, st 14 .ecx, movS .ecx 9, xorS .ecx 18, st 18 .ecx, movR .ecx .edx,
  xorS .ecx 20, andS .edx 8, xorR .eax .ebx, st 8 .ebx, movR .ebx .eax, xorS .ebx 26, st 26 .ebx,
  movR .ebx .ebp, andS .ebx 21, xorR .eax .ebx, xorR .eax .edx, xorS .edx 23, st 23 .ebx, movR .ebx .ecx,
  andS .ebx 6, andS .ecx 15, xorR .eax .ebx, andS .ebp 24, movS .ebx 22, andS .ebx 25, xorS .ebp 16,
  xorS .ebx 8, st 8 .eax, movS .eax 14, andS .eax 10, st 10 .ecx, movS .ecx 22, andS .ecx 13, xorR .eax .ebp,
  xorR .ebx .edx, st 13 .edx, movS .edx 18, xorR .edx .eax, xorR .eax .ecx, notR .eax, st 18 .ecx, movS .ecx 14,
  andS .ecx 17, xorS .edx 10, st 10 .edx, movS .edx 8, xorR .edx .ecx, xorS .ebp 12, xorR .ebp .ebx, notR .ebp,
  xorR .ebx .eax, st 12 .ebx, movR .ebx .eax, xorS .ebx 23, notR .ebx, st 23 .edx, movR .edx .ebx, xorS .edx 13,
  xorS .ebx 10, st 13 .eax, movR .eax .ebp, xorS .eax 18, notR .eax, xorS .eax 11, xorS .ebx 26, notR .ebx,
  xorR .edx .ecx, xorS .eax 16, xorS .eax 9, st 0 .ebp, st 4 .eax, st 6 .ebx, st 7 .edx, movS .eax 13,
  st 1 .eax, movS .eax 10, st 2 .eax, movS .eax 23, st 3 .eax, movS .eax 12, st 5 .eax]

#guard sboxCode == compile sb sbox sboxIns sboxOuts tmpRegs spillSlots

end VG.Impl.Aes.X86
