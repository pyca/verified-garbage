import VerifiedGarbage.Impl.TripleDes.BitsliceLayout
import VerifiedGarbage.Impl.TripleDes.X86_64.BitsliceAlloc

/-!
# Bitsliced Triple DES ECB on x86-64

`vg_triple_des_ecb_{en,de}crypt(schedule = rdi, data = rsi, n = rdx, scratch = rcx)`.

Constant-time Triple DES on 64 blocks at a time, bitsliced in 64-bit words
(Biham's bitslicing; the S-box circuits are Rusakov's, `BitsliceCircuit`).
Everything lives in the 128 slots of the scratch buffer (`rcx`, which no
instruction writes): the circuits' spills in slots 0–5, the 64 state words
in slots 8–71 (`stSlot`), then the callee-saved registers, the arguments and
the loop state.

* Up to 64 blocks are copied into the state words and transposed in place,
  so that word `j` holds bit `j` of every block (`BitsliceLayout`); IP only
  renames words. The words of the other lanes hold whatever they held:
  their results are not stored.
* A round shifts the round key (in `r15`, its bit 47 at the top) out a bit
  at a time: `add r15, r15` moves the next key bit into CF and `sbb` makes
  an all-zero or all-one mask of it, which is XORed with the state word of
  `E` to give the next input of the S-box. Each S-box's circuit then runs
  and its four outputs are XORed into the state words of `L` that P sends
  them to. Rounds alternate between reading the words of `R` (`.ba`: the
  right half of IP) and of `L` (`.ab`), so no word moves; a pass of sixteen
  rounds, eight times both, ends by exchanging the halves, as DES's swap and
  the next pass's IP do.
* Three passes, in the order and key direction of the operation, choose
  their first key and its step by the pass count; then the state is
  transposed back and the blocks copied out.
* Every address and branch depends only on the pointers, `n` and the loop
  counters.
-/

namespace VG.Impl.TripleDes.X86_64.Bitslice

open VG.X86_64 VG.Impl.TripleDes.Bitslice
open VG.Spec.TripleDes (Direction)

/-- Slot `k` of the scratch buffer (`rcx`). -/
def at_ (k : Nat) : MemOp := { base := .rcx, disp := ((8 * k : Nat) : Int) }

def rr (d s : Reg) : Instr := .mov d (.reg s)
def ld (d : Reg) (k : Nat) : Instr := .mov d (.mem (at_ k))
def st (k : Nat) (r : Reg) : Instr := .store (at_ k) r

/-! ## Scratch slots -/

/-- The spill slots the circuits may use: slots `0 … spills - 1`. -/
def spills : Nat := 6

/-- State word `j`. -/
def stSlot (j : Nat) : Nat := 8 + j

def savedRegs : List (Reg × Nat) :=
  [(.rbx, 72), (.rbp, 73), (.r12, 74), (.r13, 75), (.r14, 76), (.r15, 77)]
def schedSlot : Nat := 78
def dataSlot : Nat := 79
def leftSlot : Nat := 80
def batchSlot : Nat := 81
def keySlot : Nat := 82
def stepSlot : Nat := 83
def roundSlot : Nat := 84
def passSlot : Nat := 85

/-! ## S-boxes -/

def inRegs : List Reg := [.rax, .rbx, .rdx, .rsi, .rdi, .rbp]
def outRegs : List Reg := [.rax, .rbx, .rdx, .rsi]
def freeRegs : List Reg := [.r8, .r9, .r10, .r11, .r12, .r13, .r14]
def inReg (i : Nat) : Reg := inRegs.getD i .rax
def outReg (i : Nat) : Reg := outRegs.getD i .rax

/-! The code of the S-boxes, as `compile` allocates it for their circuits. It is written
out (and `#guard` checks that it is what `compile` produces) so that the kernel, which
evaluates the code in the proofs, does not have to run the allocator. -/

/-- The code of S-box 1. -/
def sboxCode0 : List Instr := [
  .mov .r8 (.reg .rbx), .alu .xor .r8 (.imm 0xffffffff#32), .alu .and .r8 (.reg .rbp),
  .mov .r9 (.reg .rdx), .alu .xor .r9 (.reg .r8), .mov .r10 (.reg .rsi), .alu .or .r10 (.reg .rax),
  .mov .r11 (.reg .rbp), .alu .xor .r11 (.reg .rsi), .mov .r12 (.reg .r10),
  .alu .and .r12 (.reg .r11), .mov .r13 (.reg .rdx), .alu .xor .r13 (.reg .r12),
  .mov .r14 (.reg .r9), .alu .xor .r14 (.imm 0xffffffff#32), .alu .and .r14 (.reg .r13),
  .store (spillAt 0) .rdi, .mov .rdi (.reg .rbx),
  .alu .xor .rdi (.reg .rax), .store (spillAt 1) .r10,
  .mov .r10 (.reg .rsi), .alu .xor .r10 (.reg .rdi), .alu .xor .r10 (.imm 0xffffffff#32),
  .alu .and .r10 (.reg .r9), .alu .or .r12 (.reg .rax), .alu .xor .r10 (.reg .r12),
  .mov .r12 (.reg .r14), .alu .xor .r12 (.imm 0xffffffff#32), .alu .and .r12 (.reg .r10),
  .alu .or .rax (.reg .rbp), .store (spillAt 2) .r12,
  .mov .r12 (.reg .r10), .alu .or .r12 (.reg .rax), .alu .xor .r13 (.imm 0xffffffff#32),
  .alu .and .r13 (.reg .rbx), .store (spillAt 3) .rbx,
  .mov .rbx (.reg .r12), .alu .xor .rbx (.reg .r13), .alu .xor .rax (.imm 0xffffffff#32),
  .alu .and .rax (.reg .rdx), .alu .xor .rax (.reg .r13), .alu .xor .r11 (.imm 0xffffffff#32),
  .alu .and .r11 (.reg .rdi), .alu .or .rax (.reg .r11), .alu .xor .r8 (.imm 0xffffffff#32),
  .alu .and .r8 (.reg .rsi), .mov .rsi (.reg .r9), .alu .xor .rsi (.reg .r12),
  .alu .xor .r8 (.imm 0xffffffff#32), .alu .and .r8 (.reg .rsi), .mov .rsi (.reg .r8),
  .alu .xor .rsi (.imm 0xffffffff#32),
  .alu .and .r10 (.mem (spillAt 1)),
  .alu .xor .rsi (.reg .r10),
  .alu .or .rbx (.mem (spillAt 0)),
  .alu .xor .rbx (.mem (spillAt 0)),
  .alu .xor .rbx (.reg .rsi), .alu .xor .r8 (.reg .rdi), .alu .or .r13 (.reg .r8),
  .alu .xor .r13 (.mem (spillAt 1)),
  .alu .xor .rbp (.reg .r13), .alu .xor .rsi (.reg .rbp),
  .alu .or .r14 (.mem (spillAt 0)),
  .alu .xor .r14 (.reg .rsi),
  .alu .xor .r12 (.mem (spillAt 1)),
  .alu .or .r12 (.reg .rax), .alu .xor .r12 (.reg .rbp), .alu .or .rdi (.reg .rsi),
  .alu .xor .rdi (.reg .r12),
  .mov .rsi (.mem (spillAt 2)),
  .alu .or .rsi (.mem (spillAt 0)),
  .alu .xor .rsi (.reg .rdi),
  .alu .or .r9 (.mem (spillAt 3)),
  .alu .xor .r12 (.imm 0xffffffff#32), .alu .and .r12 (.reg .r9),
  .alu .and .rbp (.mem (spillAt 2)),
  .alu .xor .r12 (.reg .rbp),
  .alu .or .r12 (.mem (spillAt 0)),
  .alu .xor .r12 (.reg .rax), .mov .rax (.reg .r12), .mov .rdx (.reg .rsi), .mov .rsi (.reg .r14)]

/-- The code of S-box 2. -/
def sboxCode1 : List Instr := [
  .mov .r8 (.reg .rdi), .alu .xor .r8 (.reg .rbx), .mov .r9 (.reg .rax),
  .alu .xor .r9 (.imm 0xffffffff#32), .alu .and .r9 (.reg .rbp), .alu .xor .r9 (.imm 0xffffffff#32),
  .alu .and .r9 (.reg .rbx), .mov .r10 (.reg .rdi), .alu .or .r10 (.reg .r9), .mov .r11 (.reg .rax),
  .alu .xor .r11 (.imm 0xffffffff#32), .alu .and .r11 (.reg .r8), .mov .r12 (.reg .rbp),
  .alu .and .r12 (.reg .r8), .alu .xor .rbx (.reg .r12), .mov .r12 (.reg .r11),
  .alu .xor .r12 (.imm 0xffffffff#32), .alu .and .r12 (.reg .rbx), .mov .r13 (.reg .rsi),
  .alu .and .r13 (.reg .rax), .alu .xor .r9 (.reg .r11), .alu .and .r9 (.reg .r10),
  .mov .r11 (.reg .r13), .alu .xor .r11 (.imm 0xffffffff#32), .alu .and .r11 (.reg .r9),
  .mov .r14 (.reg .rsi), .alu .and .r14 (.reg .r9), .alu .xor .rbp (.imm 0xffffffff#32),
  .alu .xor .rbp (.reg .r14), .alu .xor .rax (.reg .r8),
  .store (spillAt 0) .r12, .mov .r12 (.reg .r13),
  .alu .xor .r12 (.imm 0xffffffff#32), .alu .and .r12 (.reg .rax),
  .store (spillAt 1) .r8, .mov .r8 (.reg .rbp),
  .alu .xor .r8 (.reg .r12), .alu .xor .r11 (.imm 0xffffffff#32), .alu .and .r11 (.reg .rdx),
  .alu .xor .r11 (.reg .r8), .alu .xor .r12 (.imm 0xffffffff#32), .alu .and .r12 (.reg .rdi),
  .alu .xor .rbx (.reg .r12), .alu .or .rbp (.reg .rbx), .alu .xor .rbp (.reg .rbx),
  .alu .xor .rsi (.reg .rax), .alu .xor .rbp (.reg .rsi), .mov .rdi (.reg .rdx),
  .alu .xor .rdi (.imm 0xffffffff#32), .alu .and .rdi (.reg .r10), .alu .xor .rdi (.reg .rbp),
  .alu .xor .r14 (.reg .r12), .alu .or .rsi (.reg .r14), .alu .xor .r10 (.reg .r8),
  .alu .or .r13 (.reg .r10), .mov .r14 (.reg .rsi), .alu .xor .r14 (.reg .r13),
  .alu .xor .r9 (.reg .r8), .alu .xor .rbp (.reg .r9), .alu .and .r13 (.reg .rbp),
  .alu .and .rsi (.mem (spillAt 1)),
  .alu .xor .r13 (.reg .rsi), .mov .rsi (.reg .r13), .alu .or .rsi (.reg .rdx),
  .alu .xor .rsi (.reg .r14), .alu .xor .rbx (.imm 0xffffffff#32), .alu .and .rbx (.reg .r13),
  .alu .or .rax (.reg .r10), .alu .xor .rbx (.reg .rax),
  .alu .or .rdx (.mem (spillAt 0)),
  .alu .xor .rdx (.reg .rbx), .mov .rax (.reg .rdx), .mov .rbx (.reg .rsi), .mov .rdx (.reg .r11),
  .mov .rsi (.reg .rdi)]

/-- The code of S-box 3. -/
def sboxCode2 : List Instr := [
  .mov .r8 (.reg .rdi), .alu .xor .r8 (.imm 0xffffffff#32), .alu .and .r8 (.reg .rbp),
  .mov .r9 (.reg .rsi), .alu .xor .r9 (.reg .rax), .mov .r10 (.reg .r8), .alu .or .r10 (.reg .r9),
  .mov .r11 (.reg .rdx), .alu .xor .r11 (.reg .rax), .mov .r12 (.reg .rbp),
  .alu .xor .r12 (.imm 0xffffffff#32), .alu .and .r12 (.reg .r11), .mov .r13 (.reg .r10),
  .alu .xor .r13 (.reg .r12), .mov .r14 (.reg .rdi), .alu .xor .r14 (.reg .r9),
  .store (spillAt 0) .r8, .mov .r8 (.reg .rax),
  .alu .xor .r8 (.imm 0xffffffff#32), .alu .and .r8 (.reg .r14), .alu .xor .r10 (.reg .r8),
  .mov .r8 (.reg .r10), .alu .xor .r8 (.imm 0xffffffff#32), .alu .and .r8 (.reg .r13),
  .store (spillAt 1) .r8, .mov .r8 (.reg .rax),
  .alu .and .r8 (.reg .r13), .alu .or .r8 (.reg .rdx), .alu .and .r8 (.reg .rbp),
  .alu .xor .r8 (.reg .r14), .store (spillAt 2) .r14,
  .mov .r14 (.reg .rbx), .alu .xor .r14 (.imm 0xffffffff#32), .alu .and .r14 (.reg .r13),
  .alu .xor .r14 (.reg .r8), .alu .and .r9 (.reg .r11), .mov .r11 (.reg .rbp),
  .alu .xor .r11 (.reg .rdx), .store (spillAt 3) .r14,
  .mov .r14 (.reg .r10), .alu .xor .r14 (.reg .r11), .alu .or .r14 (.reg .rsi),
  .alu .xor .r9 (.imm 0xffffffff#32), .alu .and .r9 (.reg .r14), .alu .or .r12 (.reg .r11),
  .mov .r11 (.reg .r12), .alu .xor .r11 (.imm 0xffffffff#32), .alu .and .r11 (.reg .r8),
  .alu .and .rax (.reg .rdx), .mov .r14 (.reg .rdi), .alu .xor .r14 (.imm 0xffffffff#32),
  .alu .and .r14 (.reg .rax), .alu .xor .r11 (.reg .r14), .alu .and .r10 (.reg .r11),
  .alu .or .rax (.mem (spillAt 2)),
  .alu .xor .r10 (.imm 0xffffffff#32), .alu .and .r10 (.reg .rax), .alu .xor .rbp (.reg .r10),
  .alu .and .r9 (.reg .rbx), .alu .xor .r9 (.reg .rbp), .alu .xor .r13 (.imm 0xffffffff#32),
  .alu .or .rdi (.reg .r13), .alu .or .rsi (.reg .rdi),
  .alu .xor .rsi (.mem (spillAt 2)),
  .alu .xor .r12 (.reg .rsi),
  .mov .rdi (.mem (spillAt 1)),
  .alu .xor .rdi (.imm 0xffffffff#32), .alu .and .rdi (.reg .rbx), .alu .xor .rdi (.reg .r12),
  .alu .and .rdx (.reg .r13), .alu .xor .r8 (.reg .rdx), .alu .or .rsi (.reg .r8),
  .alu .xor .rbp (.mem (spillAt 0)),
  .alu .xor .rsi (.reg .rbp), .alu .or .r11 (.reg .rbx), .alu .xor .r11 (.reg .rsi),
  .mov .rax (.mem (spillAt 3)), .mov .rbx (.reg .r11),
  .mov .rdx (.reg .r9), .mov .rsi (.reg .rdi)]

/-- The code of S-box 4. -/
def sboxCode3 : List Instr := [
  .alu .xor .rbp (.reg .rsi), .alu .xor .rsi (.reg .rbx), .mov .r8 (.reg .rdi),
  .alu .or .r8 (.reg .rdx), .alu .xor .r8 (.reg .rbx), .alu .xor .r8 (.imm 0xffffffff#32),
  .alu .and .r8 (.reg .rsi), .mov .r9 (.reg .rdi), .alu .xor .r9 (.imm 0xffffffff#32),
  .alu .and .r9 (.reg .rsi), .mov .r10 (.reg .rdx), .alu .xor .r10 (.reg .r9),
  .mov .r11 (.reg .rbp), .alu .or .r11 (.reg .r10), .alu .or .r11 (.reg .r8),
  .alu .xor .r11 (.reg .r8), .mov .r12 (.reg .rdi), .alu .xor .r12 (.reg .r11),
  .alu .and .r10 (.reg .r12), .alu .or .rsi (.reg .r10), .alu .xor .rsi (.reg .r10),
  .alu .xor .rbp (.reg .r12), .alu .xor .rsi (.imm 0xffffffff#32), .alu .and .rsi (.reg .rbp),
  .alu .xor .r8 (.reg .rsi), .alu .xor .rdi (.reg .rdx), .alu .or .rbx (.reg .r9),
  .alu .xor .rbp (.reg .rbx), .mov .rbx (.reg .rdi), .alu .xor .rbx (.imm 0xffffffff#32),
  .alu .and .rbx (.reg .rbp), .alu .xor .r11 (.reg .rbx), .mov .rbx (.reg .r8),
  .alu .xor .rbx (.imm 0xffffffff#32), .alu .and .rbx (.reg .rax), .alu .xor .rbx (.reg .r11),
  .alu .xor .r11 (.imm 0xffffffff#32), .mov .r9 (.reg .rax), .alu .xor .r9 (.imm 0xffffffff#32),
  .alu .and .r9 (.reg .r8), .alu .xor .r9 (.reg .r11), .alu .xor .r8 (.reg .r11),
  .alu .xor .rdi (.imm 0xffffffff#32), .alu .and .rdi (.reg .r8), .alu .or .r10 (.reg .rdi),
  .alu .xor .rbp (.reg .r10), .mov .r10 (.reg .r12), .alu .or .r10 (.reg .rax),
  .alu .xor .r10 (.reg .rbp), .alu .and .rax (.reg .r12), .alu .xor .rax (.reg .rbp),
  .store (spillAt 0) .rbx, .mov .rbx (.reg .r10),
  .mov .rdx (.reg .r9), .mov .rsi (.mem (spillAt 0))]

/-- The code of S-box 5. -/
def sboxCode4 : List Instr := [
  .mov .r8 (.reg .rbp), .alu .or .r8 (.reg .rsi), .mov .r9 (.reg .rax),
  .alu .xor .r9 (.imm 0xffffffff#32), .alu .and .r9 (.reg .r8), .mov .r10 (.reg .rbp),
  .alu .xor .r10 (.reg .r9), .mov .r11 (.reg .rsi), .alu .xor .r11 (.reg .r10),
  .mov .r12 (.reg .rdx), .alu .or .r12 (.reg .r11), .alu .or .r9 (.reg .rdx),
  .alu .xor .r9 (.reg .rdx), .alu .xor .rsi (.reg .r9), .mov .r9 (.reg .rbx),
  .alu .and .r9 (.reg .rsi), .alu .or .r11 (.reg .rbp), .alu .xor .r9 (.reg .r11),
  .alu .xor .r9 (.reg .rdx), .alu .xor .rax (.reg .r9), .mov .r13 (.reg .r10),
  .alu .or .r13 (.reg .rax), .mov .r14 (.reg .rbx), .alu .and .r14 (.reg .r13),
  .store (spillAt 0) .r8, .mov .r8 (.reg .r10),
  .alu .xor .r8 (.reg .r14), .store (spillAt 1) .r10,
  .mov .r10 (.reg .rdx), .alu .and .r10 (.reg .r11), .alu .xor .r8 (.reg .r10),
  .alu .or .r13 (.reg .rbp), .alu .xor .r13 (.reg .rbp), .mov .r10 (.reg .rsi),
  .alu .xor .r10 (.reg .r13), .alu .xor .rbx (.reg .r12), .alu .xor .r10 (.imm 0xffffffff#32),
  .alu .and .r10 (.reg .rbx), .alu .xor .r10 (.imm 0xffffffff#32), .alu .or .r10 (.reg .rdi),
  .alu .xor .r10 (.reg .rdi), .alu .xor .r10 (.reg .r9), .mov .r9 (.reg .r14),
  .alu .xor .r9 (.imm 0xffffffff#32), .alu .and .r9 (.reg .rsi), .alu .xor .r13 (.reg .rbx),
  .alu .or .r13 (.reg .r8), .alu .xor .r9 (.imm 0xffffffff#32), .alu .and .r9 (.reg .r13),
  .mov .r13 (.reg .r9), .alu .xor .r13 (.imm 0xffffffff#32), .alu .and .r13 (.reg .r12),
  .alu .and .rax (.reg .r9), .alu .xor .rbx (.reg .rax), .alu .and .r11 (.reg .rsi),
  .alu .or .r11 (.reg .rbx), .alu .xor .r14 (.reg .r11), .alu .and .r14 (.reg .rdi),
  .alu .xor .r14 (.reg .r8),
  .alu .xor .rbp (.mem (spillAt 0)),
  .alu .xor .r9 (.reg .rbp), .alu .and .rdx (.reg .rbx), .alu .xor .r9 (.reg .rdx),
  .alu .or .r13 (.reg .rdi), .alu .xor .r13 (.reg .r9), .alu .xor .rsi (.reg .r12),
  .alu .xor .r9 (.imm 0xffffffff#32), .alu .and .r9 (.reg .rsi),
  .alu .xor .rbx (.mem (spillAt 1)),
  .alu .xor .r9 (.reg .rbx), .alu .and .r12 (.reg .rdi), .alu .xor .r12 (.reg .r9),
  .mov .rax (.reg .r14), .mov .rbx (.reg .r10), .mov .rdx (.reg .r12), .mov .rsi (.reg .r13)]

/-- The code of S-box 6. -/
def sboxCode5 : List Instr := [
  .mov .r8 (.reg .rdi), .alu .xor .r8 (.reg .rbx), .mov .r9 (.reg .rdi), .alu .or .r9 (.reg .rax),
  .alu .and .r9 (.reg .rbp), .alu .xor .r8 (.reg .r9), .mov .r10 (.reg .rax),
  .alu .xor .r10 (.reg .r8), .mov .r11 (.reg .r10), .alu .xor .r11 (.imm 0xffffffff#32),
  .alu .and .r11 (.reg .rbx), .alu .and .r10 (.reg .rbp), .mov .r12 (.reg .rdi),
  .alu .xor .r12 (.reg .r10), .mov .r13 (.reg .rbp), .alu .xor .r13 (.reg .rsi),
  .mov .r14 (.reg .r12), .alu .or .r14 (.reg .r13),
  .store (spillAt 0) .r10, .mov .r10 (.reg .r8),
  .alu .xor .r10 (.reg .r14), .store (spillAt 1) .r8,
  .mov .r8 (.reg .rsi), .alu .and .r8 (.reg .r10),
  .store (spillAt 2) .rbp, .mov .rbp (.reg .rax),
  .alu .xor .rbp (.imm 0xffffffff#32), .alu .and .rbp (.reg .r8), .alu .or .r12 (.reg .r11),
  .store (spillAt 3) .r11, .mov .r11 (.reg .rbp),
  .alu .xor .r11 (.reg .r12), .store (spillAt 4) .rbp,
  .mov .rbp (.reg .r11), .alu .and .rbp (.reg .rdx), .alu .xor .rbp (.reg .r10),
  .alu .xor .r14 (.reg .rdi), .store (spillAt 5) .rbp,
  .mov .rbp (.reg .r14), .alu .xor .rbp (.imm 0xffffffff#32), .alu .and .rbp (.reg .rax),
  .alu .xor .rsi (.reg .rbp), .mov .rbp (.reg .r8), .alu .xor .rbp (.imm 0xffffffff#32),
  .alu .and .rbp (.reg .rbx), .alu .or .rbp (.reg .rsi), .alu .or .rdi (.reg .r13),
  .alu .xor .r11 (.reg .rdi), .alu .or .r9 (.reg .rbp), .alu .xor .r11 (.reg .r9),
  .alu .or .r10 (.mem (spillAt 2)),
  .alu .and .r12 (.reg .r10), .alu .xor .r12 (.reg .rsi),
  .mov .r10 (.mem (spillAt 4)),
  .alu .xor .r10 (.imm 0xffffffff#32), .alu .and .r10 (.reg .r12),
  .mov .r9 (.mem (spillAt 3)), .alu .or .r9 (.reg .rdx),
  .alu .xor .r9 (.reg .r10),
  .alu .xor .r12 (.mem (spillAt 1)),
  .alu .xor .r12 (.imm 0xffffffff#32), .alu .and .r12 (.reg .rbx),
  .alu .xor .rdi (.imm 0xffffffff#32), .alu .xor .r14 (.reg .rdi), .alu .xor .r12 (.reg .r14),
  .alu .or .r12 (.reg .rdx), .alu .xor .r12 (.reg .rdx), .alu .xor .r12 (.reg .r11),
  .alu .xor .rax (.mem (spillAt 0)),
  .alu .xor .rsi (.mem (spillAt 2)),
  .alu .and .rax (.reg .rsi), .alu .xor .r8 (.reg .r14), .alu .xor .rax (.reg .r8),
  .alu .xor .rdx (.imm 0xffffffff#32), .alu .and .rdx (.reg .rbp), .alu .xor .rdx (.reg .rax),
  .mov .rax (.mem (spillAt 5)), .mov .rbx (.reg .r9),
  .store (spillAt 2) .rdx, .mov .rdx (.reg .r12),
  .mov .rsi (.mem (spillAt 2))]

/-- The code of S-box 7. -/
def sboxCode6 : List Instr := [
  .mov .r8 (.reg .rdx), .alu .xor .r8 (.reg .rbx), .mov .r9 (.reg .rsi), .alu .xor .r9 (.reg .r8),
  .mov .r10 (.reg .rax), .alu .and .r10 (.reg .r9), .mov .r11 (.reg .rdx),
  .alu .and .r11 (.reg .r8), .mov .r12 (.reg .rdi), .alu .xor .r12 (.reg .r11),
  .mov .r13 (.reg .r10), .alu .and .r13 (.reg .r12), .mov .r14 (.reg .rax),
  .alu .and .r14 (.reg .r11), .store (spillAt 0) .r11,
  .mov .r11 (.reg .rsi), .alu .xor .r11 (.reg .r14),
  .store (spillAt 1) .rsi, .mov .rsi (.reg .r12),
  .alu .or .rsi (.reg .r11), .alu .xor .r8 (.reg .rax),
  .store (spillAt 2) .rax, .mov .rax (.reg .rsi),
  .alu .xor .rax (.reg .r8), .store (spillAt 3) .rsi,
  .mov .rsi (.reg .r13), .alu .xor .rsi (.imm 0xffffffff#32), .alu .and .rsi (.reg .rbp),
  .alu .xor .rsi (.reg .rax), .alu .xor .r9 (.imm 0xffffffff#32), .alu .and .r9 (.reg .rbx),
  .mov .rax (.reg .r12), .alu .or .rax (.reg .r9), .alu .xor .r11 (.reg .r10),
  .alu .xor .rax (.reg .r11), .alu .xor .r10 (.reg .r8), .alu .or .rdx (.reg .r10),
  .alu .xor .rdx (.reg .r10), .mov .r8 (.reg .rdx), .alu .xor .r8 (.imm 0xffffffff#32),
  .alu .and .r8 (.reg .r12), .alu .xor .rbx (.reg .r11), .alu .xor .r8 (.reg .rbx),
  .alu .xor .r14 (.imm 0xffffffff#32), .alu .and .r14 (.reg .r10), .alu .or .rdx (.reg .r14),
  .mov .r10 (.reg .rdi),
  .alu .xor .r10 (.mem (spillAt 3)),
  .alu .and .r10 (.reg .r8), .alu .xor .r10 (.reg .rdx), .mov .rbx (.reg .r10),
  .alu .and .rbx (.reg .rbp), .alu .xor .rbx (.reg .r8),
  .alu .or .r12 (.mem (spillAt 1)),
  .alu .xor .r12 (.mem (spillAt 1)),
  .alu .or .r14 (.reg .r12),
  .alu .or .r8 (.mem (spillAt 0)),
  .alu .and .r14 (.reg .r8), .alu .xor .r10 (.reg .r14), .alu .xor .r9 (.reg .rdx),
  .alu .and .r9 (.mem (spillAt 2)),
  .alu .or .r13 (.reg .r9), .alu .xor .r14 (.reg .r13), .mov .r9 (.reg .rbp),
  .alu .xor .r9 (.imm 0xffffffff#32), .alu .and .r9 (.reg .r14), .alu .xor .r9 (.reg .rax),
  .alu .and .rdi (.reg .r13), .alu .xor .rax (.imm 0xffffffff#32), .alu .xor .rdi (.reg .rax),
  .alu .xor .r14 (.reg .rdi), .alu .or .r10 (.reg .rbp), .alu .xor .r10 (.reg .r14),
  .mov .rax (.reg .rsi), .mov .rdx (.reg .r10), .mov .rsi (.reg .r9)]

/-- The code of S-box 8. -/
def sboxCode7 : List Instr := [
  .mov .r8 (.reg .rdi), .alu .xor .r8 (.imm 0xffffffff#32), .alu .and .r8 (.reg .rsi),
  .mov .r9 (.reg .rsi), .alu .xor .r9 (.imm 0xffffffff#32), .alu .and .r9 (.reg .rbx),
  .alu .xor .r9 (.reg .rdx), .mov .r10 (.reg .rbp), .alu .and .r10 (.reg .r9), .mov .r11 (.reg .r8),
  .alu .xor .r11 (.imm 0xffffffff#32), .alu .and .r11 (.reg .r10), .mov .r12 (.reg .r9),
  .alu .xor .r12 (.imm 0xffffffff#32), .alu .and .r12 (.reg .rdi), .mov .r13 (.reg .rbp),
  .alu .or .r13 (.reg .r12), .mov .r14 (.reg .rsi), .alu .xor .r14 (.imm 0xffffffff#32),
  .alu .and .r14 (.reg .rdi), .alu .xor .r14 (.reg .rbx),
  .store (spillAt 0) .rdx, .mov .rdx (.reg .r13),
  .alu .and .rdx (.reg .r14), .alu .or .r10 (.reg .rdx), .alu .xor .r9 (.imm 0xffffffff#32),
  .alu .xor .rdx (.reg .r9), .alu .xor .r13 (.imm 0xffffffff#32), .alu .and .r13 (.reg .rsi),
  .alu .xor .rdx (.reg .r13), .alu .xor .r8 (.reg .rdx), .mov .r13 (.reg .r11),
  .alu .or .r13 (.reg .rax), .alu .xor .r13 (.reg .r8), .alu .xor .r8 (.reg .rbp),
  .mov .rsi (.reg .rbx), .alu .and .rsi (.reg .r8), .alu .xor .rdx (.reg .rdi),
  .alu .xor .rsi (.reg .rdx), .alu .xor .r12 (.reg .rsi), .alu .xor .rsi (.reg .r10),
  .alu .or .rdi (.reg .rsi), .alu .xor .rbx (.reg .r8), .alu .xor .rdi (.reg .rbx),
  .alu .and .r10 (.reg .rax), .alu .xor .r10 (.reg .rdi), .alu .xor .r14 (.reg .r12),
  .alu .or .rdx (.mem (spillAt 0)),
  .alu .xor .rdx (.reg .r14), .alu .xor .rbp (.reg .rdx), .alu .and .rbp (.reg .rax),
  .alu .xor .rbp (.reg .r12),
  .alu .or .r14 (.mem (spillAt 0)),
  .alu .xor .r14 (.mem (spillAt 0)),
  .alu .and .rdi (.reg .r14), .alu .xor .r11 (.reg .rdx), .alu .xor .rdi (.reg .r11),
  .alu .or .rdi (.reg .rax), .alu .xor .rdi (.reg .r12), .mov .rax (.reg .rbp),
  .mov .rbx (.reg .r10), .mov .rdx (.reg .r13), .mov .rsi (.reg .rdi)]

def sboxCode : Nat → List Instr
  | 0 => sboxCode0 | 1 => sboxCode1 | 2 => sboxCode2 | 3 => sboxCode3
  | 4 => sboxCode4 | 5 => sboxCode5 | 6 => sboxCode6 | _ => sboxCode7

#guard (List.range 8).all fun j => sboxCode j ==
  compile (box j) ((List.range 6).map fun i => (i, inReg i))
    ((List.range 4).map fun i => ((outputs j).getD i 0, outReg i)) freeRegs (List.range spills)

/-- S-box `j`'s input `i`: the next key bit, as a mask, ⊕ the word of `E`. -/
def inputStep (ρ : Role) (j i : Nat) : List Instr :=
  [.alu .add .r15 (.reg .r15), .alu .sbb (inReg i) (.reg (inReg i)),
   .alu .xor (inReg i) (.mem (at_ (stSlot (readWord ρ (eBit (inBit j i))))))]

/-- S-box `j`'s inputs, from the most significant (whose key bit is next). -/
def inputCode (ρ : Role) (j : Nat) : List Instr :=
  (List.range 6).reverse.flatMap (inputStep ρ j)

/-- XOR S-box `j`'s outputs into their words. -/
def outputCode (ρ : Role) (j : Nat) : List Instr :=
  (List.range 4).flatMap fun i =>
    [.alu .xor (outReg i) (.mem (at_ (stSlot (writeWord ρ (outBit j i))))),
     st (stSlot (writeWord ρ (outBit j i))) (outReg i)]

def sboxStep (ρ : Role) (j : Nat) : List Instr := inputCode ρ j ++ sboxCode j ++ outputCode ρ j

/-! ## Rounds -/

/-- Load the round key into `r15`, its bit 47 at the top, and advance the
key pointer. -/
def keyLoad : List Instr :=
  [ld .rax keySlot, .mov .r15 (.mem { base := .rax, disp := 0 }), ld .rdx stepSlot,
   .alu .add .rax (.reg .rdx), st keySlot .rax, .shift .ror .r15 48]

def round (ρ : Role) : List Instr := keyLoad ++ (List.range 8).flatMap (sboxStep ρ)

/-- Two rounds, and the count of pairs left. -/
def roundPair : List Instr :=
  round .ba ++ round .ab ++ [ld .rax roundSlot, .alu .sub .rax (.imm 1), st roundSlot .rax]

/-- Exchange the halves. -/
def swapHalves : List Instr :=
  (List.range 32).flatMap fun q =>
    [ld .rax (stSlot (lWord q)), ld .rdx (stSlot (rWord q)), st (stSlot (lWord q)) .rdx,
     st (stSlot (rWord q)) .rax]

/-- The first key of each pass (an offset into the schedule) and its step,
for the passes counted down from 3. -/
def passKey : Direction → Nat → Nat × Int
  | .encrypt, 3 => (0, 8)
  | .encrypt, 2 => (8 * 31, -8)
  | .encrypt, _ => (8 * 32, 8)
  | .decrypt, 3 => (8 * 47, -8)
  | .decrypt, 2 => (8 * 16, 8)
  | .decrypt, _ => (8 * 15, -8)

/-- Point at the pass's first key, with its step. -/
def passKeyCode (d : Direction) (p : Nat) : List Instr :=
  [ld .rdx schedSlot, .alu .add .rdx (.imm (BitVec.ofNat 32 (passKey d p).1)), st keySlot .rdx,
   .mov .rdx (.imm (BitVec.ofInt 32 (passKey d p).2)), st stepSlot .rdx]

/-- Choose the pass's first key and step by the pass count, and count 8 pairs. -/
def passStart (d : Direction) : Prog isa :=
  .seq (.block [ld .rax passSlot, .alu .cmp .rax (.imm 3)])
    (.seq (.ite .e (.block (passKeyCode d 3))
      (.seq (.block [.alu .cmp .rax (.imm 2)])
        (.ite .e (.block (passKeyCode d 2)) (.block (passKeyCode d 1)))))
    (.block [.mov .rax (.imm 8), st roundSlot .rax]))

def passEnd : List Instr := [ld .rax passSlot, .alu .sub .rax (.imm 1), st passSlot .rax]

def pass (d : Direction) : Prog isa :=
  .seq (passStart d) (.seq (.loop (.block roundPair) .ne) (.block (swapHalves ++ passEnd)))

/-! ## Transposition -/

/-- The bits `p` with `p &&& s = 0`. -/
def swapMask (s : Nat) : BitVec 64 :=
  BitVec.ofNat 64 ((List.range 64).foldl (fun m p => if p &&& s = 0 then m ||| 2 ^ p else m) 0)

/-- Exchange the bits `p + s` of `a` and `p` of `b` (`p &&& s = 0`), masked by `m`. -/
def swapBits (a b t m : Reg) (s : Nat) : List Instr :=
  [rr t a, .shift .shr t s, .alu .xor t (.reg b), .alu .and t (.reg m),
   .alu .xor b (.reg t), .shift .ror t (64 - s), .alu .xor a (.reg t)]

def groupRegs : List Reg := [.rax, .rbx, .rdx, .rsi, .rdi, .rbp, .r8, .r9]
def groupReg (k : Nat) : Reg := groupRegs.getD k .rax

/-- Three stages on eight words, the state words `word k`: the stage of
shift `unit * d` pairs the words `k` and `k + d`, for `d` = 4, 2, 1. -/
def group (word : Nat → Nat) (unit : Nat) : List Instr :=
  (List.range 8).map (fun k => ld (groupReg k) (stSlot (word k))) ++
  ([(4, Reg.r13), (2, .r14), (1, .r15)].flatMap fun (d, m) =>
    ((List.range 8).filter (fun k => k &&& d = 0)).flatMap fun k =>
      swapBits (groupReg k) (groupReg (k + d)) .r10 m (unit * d)) ++
  (List.range 8).map (fun k => st (stSlot (word k)) (groupReg k))

def masks (unit : Nat) : List Instr :=
  [.movImm64 .r13 (swapMask (4 * unit)), .movImm64 .r14 (swapMask (2 * unit)),
   .movImm64 .r15 (swapMask unit)]

/-- Transpose the 64 state words in place: stages 32, 16, 8, then 4, 2, 1. -/
def transpose : List Instr :=
  masks 8 ++ (List.range 8).flatMap (fun i => group (fun k => i + 8 * k) 8) ++
  masks 1 ++ (List.range 8).flatMap (fun g => group (fun k => 8 * g + k) 1)

/-! ## Batches -/

/-- `k := min(n, 64)` blocks in this batch. -/
def batchSize : Prog isa :=
  .seq (.block [ld .rax leftSlot, .alu .cmp .rax (.imm 64)])
    (.seq (.ite .b (.block []) (.block [.mov .rax (.imm 64)])) (.block [st batchSlot .rax]))

/-- The public words the copies keep in registers: a store of the data to a
pointer that moves, or into the data buffer, does not keep the constant-time
analysis' knowledge that scratch slots hold public values. -/
def keepIn : List Instr :=
  [ld .r8 schedSlot, ld .r9 dataSlot, ld .r10 leftSlot, ld .r11 batchSlot]

def copyBody (src dst : Reg) : List Instr :=
  [.mov .rax (.mem { base := src, disp := 0 }), .store { base := dst, disp := 0 } .rax,
   .alu .add .rsi (.imm 8), .alu .add .rdi (.imm 8), .alu .sub .rdx (.imm 1)]

/-- Copy the batch's blocks into the state words. -/
def copyIn : Prog isa :=
  .seq (.block (keepIn ++ [rr .rsi .r9, rr .rdi .rcx, .alu .add .rdi (.imm 64), rr .rdx .r11]))
    (.seq (.loop (.block (copyBody .rsi .rdi)) .ne)
      (.block [st schedSlot .r8, st dataSlot .r9, st leftSlot .r10, st batchSlot .r11]))

/-- Copy the state words out to the batch's blocks. -/
def copyOut : Prog isa :=
  .seq (.block (keepIn ++ [rr .rsi .r9, rr .rdi .rcx, .alu .add .rdi (.imm 64), rr .rdx .r11]))
    (.loop (.block (copyBody .rdi .rsi)) .ne)

/-- Count three passes. -/
def passesStart : List Instr := [.mov .rax (.imm 3), st passSlot .rax]

/-- Advance the data pointer (`rsi`, after `copyOut`) and count the blocks left. -/
def batchEnd : List Instr :=
  [st schedSlot .r8, st dataSlot .rsi, rr .rax .r10, .alu .sub .rax (.reg .r11), st leftSlot .rax]

def batch (d : Direction) : Prog isa :=
  .seq batchSize (.seq copyIn (.seq (.block (transpose ++ passesStart))
    (.seq (.loop (pass d) .ne) (.seq (.block transpose) (.seq copyOut (.block batchEnd))))))

/-! ## The function -/

def setup : List Instr :=
  savedRegs.map (fun (r, k) => st k r) ++
  [st schedSlot .rdi, st dataSlot .rsi, st leftSlot .rdx, .alu .cmp .rdx (.imm 0)]

def restore : List Instr := savedRegs.map fun (r, k) => ld r k

def ecb (d : Direction) : Prog isa :=
  .seq (.block setup) (.seq (.ite .e (.block []) (.loop (batch d) .ne)) (.block restore))

def encrypt : Prog isa := ecb .encrypt
def decrypt : Prog isa := ecb .decrypt

end VG.Impl.TripleDes.X86_64.Bitslice
