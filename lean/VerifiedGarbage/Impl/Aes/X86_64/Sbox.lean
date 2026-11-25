module

public import VerifiedGarbage.Impl.Aes.X86_64.Alloc
meta import VerifiedGarbage.Impl.Aes.X86_64.Alloc

/-!
# The bitsliced AES S-box on x86-64

The registers of eight bit slices, short forms of the instructions on them
and on slots of the scratch buffer, and the circuit `Circuit.sbox` on the
slices (`q j` holds bit `j` of 64 bytes), in place, spilling to slots of the
scratch buffer: the code `compile` allocates for it, written out (`#guard`
checks that it is that) so that the kernel need not run the allocator.
-/

@[expose] public section

namespace VG.Impl.Aes.X86_64

open VG.X86_64 VG.Impl.Aes.Circuit

/-- The slices: bit `j` is in `q j`. -/
def q : Nat → Reg
  | 0 => .rax | 1 => .rbx | 2 => .rcx | 3 => .rbp
  | 4 => .r10 | 5 => .r11 | 6 => .r12 | _ => .r13

/-- Two temporaries. -/
def t0 : Reg := .r14
def t1 : Reg := .r15

/-- The scratch buffer's base. -/
def sb : Reg := .r9

/-- The slot of all ones, and the slots the S-box may spill to. -/
def onesSlot : Nat := 0
def spillSlots : List Nat := List.range' 1 47

def sboxIns : List (Nat × Reg) := (List.range 8).map fun i => (x i, q i)
def sboxOuts : List (Nat × Reg) := (List.range 8).map fun i => (s i, q i)

/-! Short forms, on registers and slots of `sb`. -/

def movR (d s : Reg) : Instr := .mov d (.reg s)
def movS (d : Reg) (k : Nat) : Instr := .mov d (.mem (slotAt sb k))
def xorR (d s : Reg) : Instr := .alu .xor d (.reg s)
def xorS (d : Reg) (k : Nat) : Instr := .alu .xor d (.mem (slotAt sb k))
def andR (d s : Reg) : Instr := .alu .and d (.reg s)
def andS (d : Reg) (k : Nat) : Instr := .alu .and d (.mem (slotAt sb k))
def st (k : Nat) (r : Reg) : Instr := .store (slotAt sb k) r
def ones (d : Reg) : Instr := .movImm64 d (BitVec.allOnes 64)

/-- The S-box on the slices in `q 0 … q 7`, in place. -/
def sboxCode : List Instr := [
  ones .r14, st 0 .r14, xorR .rcx .r11, movR .r14 .rcx, xorR .r14 .rbx, movR .r15 .r14,
  xorR .r15 .r12, xorR .rax .r14, xorR .rbp .r15, xorR .rbp .r13, st 1 .r12, movR .r12 .rbp,
  xorR .r12 .rcx, st 2 .rcx, movR .rcx .r12, xorR .rcx .rax, xorR .r11 .rcx, st 3 .r14,
  movR .r14 .rax, xorR .r14 .r13, st 4 .rax, movR .rax .rcx, xorR .rax .r10, st 5 .r14,
  movR .r14 .rcx, xorR .r14 .r15, st 6 .r14, movR .r14 .r11, xorR .r14 .r13, st 7 .r13,
  movR .r13 .rax, xorR .r13 .r14, st 8 .r11, movR .r11 .rax, andR .r11 .rcx, st 9 .rcx,
  movR .rcx .r12, xorR .rcx .r10, xorR .r10 .rbp, xorR .rbp .rax, st 10 .rax, movR .rax .r14,
  andR .rax .r15, st 11 .r15, movR .r15 .rcx, andR .r15 .rbp, xorR .rbx .rcx, xorR .rax .r15,
  st 12 .rbp, movR .rbp .r13, andS .rbp 6, xorR .r15 .rbp, movS .rbp 6, xorR .rbp .rbx,
  st 13 .r13, movR .r13 .rcx, xorS .r13 8, st 14 .rcx, movS .rcx 5, andR .rcx .rbx, st 15 .rbx,
  movR .rbx .r13, andR .rbx .rbp, xorR .rcx .r15, xorR .r15 .rbx, movS .rbx 4, andR .rbx .r10,
  st 16 .rbp, movS .rbp 7, andS .rbp 3, xorR .rcx .r11, xorR .r15 .rbx, xorR .r11 .rbp,
  xorR .rbx .rax, movR .rbp .r14, xorS .rbp 1, xorS .rcx 2, xorR .r11 .rax, movS .rax 8,
  andS .rax 1, xorR .r11 .rbp, xorR .rbx .rax, movS .rax 8, xorS .rax 3, xorR .rbx .rax,
  xorR .r15 .r12, movR .r12 .rcx, xorR .r12 .r15, movR .rax .r11, andR .rax .rcx,
  movR .rbp .r15, xorR .rbp .rax, xorR .rax .rbx, andR .rax .r12, xorR .r11 .rbx,
  xorR .rax .r15, xorR .rcx .rax, movR .r12 .rax, andS .r12 7, st 7 .r12, movR .r12 .rbp,
  xorR .r12 .rax, andR .r15 .r12, xorR .rcx .r15, andR .r14 .rcx, xorR .r15 .rbp,
  andR .rbp .r11, xorR .rbx .rbp, movR .rbp .rcx, andS .rbp 11, andR .r15 .rbx, xorR .r15 .r11,
  movR .r11 .rbx, xorR .r11 .r15, andR .r13 .r11, movR .r12 .rbx, xorR .r12 .rax,
  andR .r10 .r12, andS .r11 16, st 16 .r14, movR .r14 .r15, andS .r14 13, st 13 .r14,
  movR .r14 .r12, andS .r14 4, xorR .r14 .r13, st 4 .r14, movR .r14 .r15, andS .r14 6,
  xorR .r15 .rcx, xorR .r12 .r15, xorS .r13 7, xorR .rcx .rax, andS .rax 3, xorR .r11 .r14,
  xorR .r10 .r11, st 3 .r10, movR .r10 .r12, andS .r10 12, xorR .r11 .r10, xorR .r11 .rax,
  xorR .rbp .rax, movR .rax .rcx, andS .rax 1, andS .rcx 8, xorR .r11 .rax, andS .r12 14,
  movR .rax .rbx, andS .rax 15, xorS .r12 13, xorR .r14 .rax, movR .rax .r15, andS .rax 10,
  andS .rbx 5, xorR .rax .r12, xorR .r14 .rbp, xorR .r13 .rax, xorR .rax .rbx, xorS .rax 0,
  andS .r15 9, xorR .r13 .rcx, xorR .r11 .r15, xorS .r12 4, xorR .r12 .r14, xorS .r12 0,
  xorR .r14 .rax, xorR .r10 .rax, xorS .r10 0, xorR .rbp .r10, xorR .r10 .r13, xorR .rbx .r12,
  xorS .rbx 0, xorS .rbx 16, xorS .r10 3, xorS .r10 0, xorR .rbp .r15, xorS .rbx 13,
  xorS .rbx 7, st 7 .rax, movR .rax .r12, st 13 .rbx, movS .rbx 7, movR .rcx .r13, st 3 .rbp,
  movR .rbp .r11, st 16 .r10, movS .r10 13, movR .r11 .r14, movS .r12 16, movS .r13 3]

#guard sboxCode == compile sb sbox sboxIns sboxOuts [t0, t1] onesSlot spillSlots

end VG.Impl.Aes.X86_64
