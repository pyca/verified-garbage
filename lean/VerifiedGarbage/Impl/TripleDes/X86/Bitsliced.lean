module

public import VerifiedGarbage.Impl.TripleDes.BitsliceLayout
public import VerifiedGarbage.Spec.TripleDes
public import VerifiedGarbage.TCB.X86.Isa
meta import VerifiedGarbage.Impl.TripleDes.BitsliceLayout
public import VerifiedGarbage.Impl.TripleDes.X86.BitsliceAlloc
meta import VerifiedGarbage.Impl.TripleDes.X86.BitsliceAlloc

/-!
# Bitsliced Triple DES on x86 (32-bit): 32 blocks at a time

`batch d` (cdecl: the working space at `[esp + 4]`, the schedule at
`[esp + 8]`): `vg_triple_des_encrypt_batch` and
`vg_triple_des_decrypt_batch`, internal functions that encrypt or decrypt
in place the 32 blocks in the working space, from its word `bufSlot` on.

Constant-time Triple DES on 32 blocks at a time, bitsliced in 32-bit words
(Biham's bitslicing; the S-box circuits are Rusakov's, `BitsliceCircuit`),
as on ARMv7 (`Impl/TripleDes/Arm/Bitsliced.lean`), with seven registers:
everything lives in the working space, at `ebp`, which no instruction
between the entry and the exit writes: the circuits' inputs and spilled
values (`spills` words), the 64 state words (`stSlot`), the round key's two
words (`kloSlot`, `khiSlot`), its pointer (`kpSlot`), the count of pairs of
rounds left (`cntSlot`), the schedule's address (`schedSlot`), the
caller's registers (`saved`) and, from word `bufSlot` on, the 32 blocks. The
words between are the caller's.

* Block `b`'s low word (its first four bytes, as a little-endian word) is
  copied to state word `b` and its high word to state word `32 + b`; each
  half is transposed in place, so that word `j` holds bit `j` of every block
  (`BitsliceLayout`, with 32-bit words); IP only renames words.
* A round copies its key's two words into the working space and steps the
  key pointer. S-box `j`'s input `i` is key bit `inBit j i` as a mask (the
  bit shifted out into the carry, and `sbb` of a register with itself),
  XORed with the state word of `E`, in slot `i`. Each S-box's circuit then
  runs in the six registers and the `spills` words (`BitsliceAlloc`), and
  its four outputs are XORed into the state words of `L` that P sends them
  to. Rounds alternate between reading the words of `R` (`.ba`) and of `L`
  (`.ab`), so no word moves; a pass of sixteen rounds, eight times both,
  ends by exchanging the halves, as DES's swap and the next pass's IP do.
* Each of the three passes sets its schedule component's first key and the
  count, and calls the rounds of its key direction and the exchange of the
  halves, `vg_triple_des_pass_forward` or `vg_triple_des_pass_backward`
  (`passRounds`), which the two functions share (4 bytes of stack, the
  return address); then the state is transposed back and copied to the
  blocks.

Every address and branch depends only on the pointers and the loop
counters, which are in registers or in words of the working space that only
they are stored to.
-/

@[expose] public section

namespace VG.Impl.TripleDes.X86.Bitslice

open VG.X86 VG.Impl.TripleDes.Bitslice
open VG.Spec.TripleDes (Direction)

/-! ## The working space -/

/-- The working space's base. -/
def base : Reg := .ebp

/-- Word `k` of the working space. -/
def ws (k : Nat) : MemOp := { base := .ebp, disp := 4 * k }

/-- The words the circuits use, the first of the working space: their six
inputs, then the values they spill. -/
def spills : Nat := 14
/-- State word `j`. -/
def stSlot (j : Nat) : Nat := spills + j
/-- The round key's low and high words. -/
def kloSlot : Nat := 78
def khiSlot : Nat := 79
/-- The round key's pointer. -/
def kpSlot : Nat := 80
/-- The pairs of rounds left. -/
def cntSlot : Nat := 81
/-- The schedule. -/
def schedSlot : Nat := 82

/-- The registers the function saves, and their words in the working space. -/
def saved : List (Reg × Nat) := [(.ebx, 83), (.esi, 84), (.edi, 85), (.ebp, 86)]

/-- The 32 blocks: block `b`'s words are words `bufSlot + 2 b` and
`bufSlot + 2 b + 1`. -/
def bufSlot : Nat := 132

/-- The word of the blocks that state word `j` is: block `j % 32`'s low
word for `j < 32`, its high word otherwise. -/
def bufWord (j : Nat) : Nat := bufSlot + 2 * (j % 32) + j / 32

/-- The words of the working space. -/
def wsWords : Nat := 196

/-! ## S-boxes -/

/-- The registers of an S-box's outputs. -/
def outRegs : List Reg := [.eax, .ebx, .ecx, .edx]
def freeRegs : List Reg := [.eax, .ebx, .ecx, .edx, .esi, .edi]
def outReg (i : Nat) : Reg := outRegs.getD i .eax

/-! The code of the S-boxes, as `compile` allocates it for their circuits, whose
inputs are in the slots `0 … 5`. It is written out (and `#guard` checks that it is
what `compile` produces) so that the kernel, which evaluates the code in the proofs,
does not have to run the allocator. -/

/-- The code of S-box 1. -/
def sboxCode0 : List Instr := [
  .mov .eax (.mem (spillAt 1)), .alu .xor .eax Alloc.ones, .alu .and .eax (.mem (spillAt 5)),
  .mov .ebx (.mem (spillAt 2)), .alu .xor .ebx (.reg .eax), .mov .ecx (.mem (spillAt 3)),
  .alu .or .ecx (.mem (spillAt 0)), .mov .edx (.mem (spillAt 5)), .alu .xor .edx (.mem (spillAt 3)),
  .mov .esi (.reg .ecx), .alu .and .esi (.reg .edx), .mov .edi (.mem (spillAt 2)),
  .alu .xor .edi (.reg .esi), .store (spillAt 6) .ecx, .mov .ecx (.reg .ebx), .alu .xor .ecx Alloc.ones,
  .alu .and .ecx (.reg .edi), .store (spillAt 7) .eax, .mov .eax (.mem (spillAt 1)),
  .alu .xor .eax (.mem (spillAt 0)), .store (spillAt 8) .edx, .mov .edx (.mem (spillAt 3)),
  .alu .xor .edx (.reg .eax), .alu .xor .edx Alloc.ones, .alu .and .edx (.reg .ebx),
  .alu .or .esi (.mem (spillAt 0)), .alu .xor .edx (.reg .esi), .mov .esi (.reg .ecx), .alu .xor .esi Alloc.ones,
  .alu .and .esi (.reg .edx), .store (spillAt 9) .esi, .mov .esi (.mem (spillAt 5)),
  .alu .or .esi (.mem (spillAt 0)), .store (spillAt 0) .ecx, .mov .ecx (.reg .edx),
  .alu .or .ecx (.reg .esi), .alu .xor .edi Alloc.ones, .alu .and .edi (.mem (spillAt 1)),
  .store (spillAt 10) .edx, .mov .edx (.reg .ecx), .alu .xor .edx (.reg .edi), .alu .xor .esi Alloc.ones,
  .alu .and .esi (.mem (spillAt 2)), .alu .xor .esi (.reg .edi), .store (spillAt 2) .edi,
  .mov .edi (.mem (spillAt 8)), .alu .xor .edi Alloc.ones, .alu .and .edi (.reg .eax), .alu .or .esi (.reg .edi),
  .mov .edi (.mem (spillAt 7)), .alu .xor .edi Alloc.ones, .alu .and .edi (.mem (spillAt 3)),
  .store (spillAt 7) .esi, .mov .esi (.reg .ebx), .alu .xor .esi (.reg .ecx), .alu .xor .edi Alloc.ones,
  .alu .and .edi (.reg .esi), .mov .esi (.reg .edi), .alu .xor .esi Alloc.ones, .store (spillAt 3) .ebx,
  .mov .ebx (.mem (spillAt 6)), .alu .and .ebx (.mem (spillAt 10)), .alu .xor .esi (.reg .ebx),
  .alu .or .edx (.mem (spillAt 4)), .alu .xor .edx (.mem (spillAt 4)), .alu .xor .edx (.reg .esi),
  .alu .xor .edi (.reg .eax), .alu .or .edi (.mem (spillAt 2)), .alu .xor .edi (.mem (spillAt 6)),
  .alu .xor .edi (.mem (spillAt 5)), .alu .xor .esi (.reg .edi), .mov .ebx (.mem (spillAt 0)),
  .alu .or .ebx (.mem (spillAt 4)), .alu .xor .ebx (.reg .esi), .alu .xor .ecx (.mem (spillAt 6)),
  .alu .or .ecx (.mem (spillAt 7)), .alu .xor .ecx (.reg .edi), .alu .or .eax (.reg .esi),
  .alu .xor .eax (.reg .ecx), .mov .esi (.mem (spillAt 9)), .alu .or .esi (.mem (spillAt 4)),
  .alu .xor .esi (.reg .eax), .mov .eax (.mem (spillAt 1)), .alu .or .eax (.mem (spillAt 3)),
  .alu .xor .ecx Alloc.ones, .alu .and .ecx (.reg .eax), .alu .and .edi (.mem (spillAt 9)),
  .alu .xor .ecx (.reg .edi), .alu .or .ecx (.mem (spillAt 4)), .alu .xor .ecx (.mem (spillAt 7)),
  .mov .eax (.reg .ecx), .store (spillAt 7) .ebx, .mov .ebx (.reg .edx), .mov .ecx (.reg .esi),
  .mov .edx (.mem (spillAt 7))]

/-- The code of S-box 2. -/
def sboxCode1 : List Instr := [
  .mov .eax (.mem (spillAt 4)), .alu .xor .eax (.mem (spillAt 1)), .mov .ebx (.mem (spillAt 0)),
  .alu .xor .ebx Alloc.ones, .alu .and .ebx (.mem (spillAt 5)), .alu .xor .ebx Alloc.ones,
  .alu .and .ebx (.mem (spillAt 1)), .mov .ecx (.mem (spillAt 4)), .alu .or .ecx (.reg .ebx),
  .mov .edx (.mem (spillAt 0)), .alu .xor .edx Alloc.ones, .alu .and .edx (.reg .eax),
  .mov .esi (.mem (spillAt 5)), .alu .and .esi (.reg .eax), .alu .xor .esi (.mem (spillAt 1)),
  .mov .edi (.reg .edx), .alu .xor .edi Alloc.ones, .alu .and .edi (.reg .esi), .store (spillAt 1) .edi,
  .mov .edi (.mem (spillAt 3)), .alu .and .edi (.mem (spillAt 0)), .alu .xor .ebx (.reg .edx),
  .alu .and .ebx (.reg .ecx), .mov .edx (.reg .edi), .alu .xor .edx Alloc.ones, .alu .and .edx (.reg .ebx),
  .store (spillAt 6) .ecx, .mov .ecx (.mem (spillAt 3)), .alu .and .ecx (.reg .ebx),
  .store (spillAt 7) .ebx, .mov .ebx (.mem (spillAt 5)), .alu .xor .ebx Alloc.ones, .alu .xor .ebx (.reg .ecx),
  .store (spillAt 5) .ecx, .mov .ecx (.mem (spillAt 0)), .alu .xor .ecx (.reg .eax),
  .store (spillAt 0) .eax, .mov .eax (.reg .edi), .alu .xor .eax Alloc.ones, .alu .and .eax (.reg .ecx),
  .store (spillAt 8) .edi, .mov .edi (.reg .ebx), .alu .xor .edi (.reg .eax), .alu .xor .edx Alloc.ones,
  .alu .and .edx (.mem (spillAt 2)), .alu .xor .edx (.reg .edi), .alu .xor .eax Alloc.ones,
  .alu .and .eax (.mem (spillAt 4)), .alu .xor .esi (.reg .eax), .alu .or .ebx (.reg .esi),
  .alu .xor .ebx (.reg .esi), .store (spillAt 4) .edx, .mov .edx (.mem (spillAt 3)),
  .alu .xor .edx (.reg .ecx), .alu .xor .ebx (.reg .edx), .store (spillAt 3) .ecx,
  .mov .ecx (.mem (spillAt 2)), .alu .xor .ecx Alloc.ones, .alu .and .ecx (.mem (spillAt 6)),
  .alu .xor .ecx (.reg .ebx), .alu .xor .eax (.mem (spillAt 5)), .alu .or .edx (.reg .eax),
  .mov .eax (.mem (spillAt 6)), .alu .xor .eax (.reg .edi), .store (spillAt 6) .ecx,
  .mov .ecx (.mem (spillAt 8)), .alu .or .ecx (.reg .eax), .store (spillAt 8) .eax, .mov .eax (.reg .edx),
  .alu .xor .eax (.reg .ecx), .alu .xor .edi (.mem (spillAt 7)), .alu .xor .ebx (.reg .edi),
  .alu .and .ecx (.reg .ebx), .alu .and .edx (.mem (spillAt 0)), .alu .xor .ecx (.reg .edx),
  .mov .edx (.reg .ecx), .alu .or .edx (.mem (spillAt 2)), .alu .xor .edx (.reg .eax), .alu .xor .esi Alloc.ones,
  .alu .and .esi (.reg .ecx), .mov .ecx (.mem (spillAt 3)), .alu .or .ecx (.mem (spillAt 8)),
  .alu .xor .esi (.reg .ecx), .mov .ecx (.mem (spillAt 1)), .alu .or .ecx (.mem (spillAt 2)),
  .alu .xor .ecx (.reg .esi), .mov .eax (.reg .ecx), .mov .ebx (.reg .edx), .mov .ecx (.mem (spillAt 4)),
  .mov .edx (.mem (spillAt 6))]

/-- The code of S-box 3. -/
def sboxCode2 : List Instr := [
  .mov .eax (.mem (spillAt 4)), .alu .xor .eax Alloc.ones, .alu .and .eax (.mem (spillAt 5)),
  .mov .ebx (.mem (spillAt 3)), .alu .xor .ebx (.mem (spillAt 0)), .mov .ecx (.reg .eax),
  .alu .or .ecx (.reg .ebx), .mov .edx (.mem (spillAt 2)), .alu .xor .edx (.mem (spillAt 0)),
  .mov .esi (.mem (spillAt 5)), .alu .xor .esi Alloc.ones, .alu .and .esi (.reg .edx), .mov .edi (.reg .ecx),
  .alu .xor .edi (.reg .esi), .store (spillAt 6) .eax, .mov .eax (.mem (spillAt 4)),
  .alu .xor .eax (.reg .ebx), .store (spillAt 7) .esi, .mov .esi (.mem (spillAt 0)), .alu .xor .esi Alloc.ones,
  .alu .and .esi (.reg .eax), .alu .xor .ecx (.reg .esi), .mov .esi (.reg .ecx), .alu .xor .esi Alloc.ones,
  .alu .and .esi (.reg .edi), .store (spillAt 8) .esi, .mov .esi (.mem (spillAt 0)),
  .alu .and .esi (.reg .edi), .alu .or .esi (.mem (spillAt 2)), .alu .and .esi (.mem (spillAt 5)),
  .alu .xor .esi (.reg .eax), .store (spillAt 9) .eax, .mov .eax (.mem (spillAt 1)), .alu .xor .eax Alloc.ones,
  .alu .and .eax (.reg .edi), .alu .xor .eax (.reg .esi), .alu .and .ebx (.reg .edx),
  .mov .edx (.mem (spillAt 5)), .alu .xor .edx (.mem (spillAt 2)), .store (spillAt 10) .eax,
  .mov .eax (.reg .ecx), .alu .xor .eax (.reg .edx), .alu .or .eax (.mem (spillAt 3)), .alu .xor .ebx Alloc.ones,
  .alu .and .ebx (.reg .eax), .alu .or .edx (.mem (spillAt 7)), .mov .eax (.reg .edx), .alu .xor .eax Alloc.ones,
  .alu .and .eax (.reg .esi), .store (spillAt 7) .esi, .mov .esi (.mem (spillAt 2)),
  .alu .and .esi (.mem (spillAt 0)), .store (spillAt 0) .edx, .mov .edx (.mem (spillAt 4)),
  .alu .xor .edx Alloc.ones, .alu .and .edx (.reg .esi), .alu .xor .eax (.reg .edx), .alu .and .ecx (.reg .eax),
  .alu .or .esi (.mem (spillAt 9)), .alu .xor .ecx Alloc.ones, .alu .and .ecx (.reg .esi),
  .alu .xor .ecx (.mem (spillAt 5)), .alu .and .ebx (.mem (spillAt 1)), .alu .xor .ebx (.reg .ecx),
  .alu .xor .edi Alloc.ones, .mov .esi (.mem (spillAt 4)), .alu .or .esi (.reg .edi),
  .alu .or .esi (.mem (spillAt 3)), .alu .xor .esi (.mem (spillAt 9)), .mov .edx (.mem (spillAt 0)),
  .alu .xor .edx (.reg .esi), .store (spillAt 0) .ebx, .mov .ebx (.mem (spillAt 8)), .alu .xor .ebx Alloc.ones,
  .alu .and .ebx (.mem (spillAt 1)), .alu .xor .ebx (.reg .edx), .alu .and .edi (.mem (spillAt 2)),
  .alu .xor .edi (.mem (spillAt 7)), .alu .or .esi (.reg .edi), .alu .xor .ecx (.mem (spillAt 6)),
  .alu .xor .esi (.reg .ecx), .alu .or .eax (.mem (spillAt 1)), .alu .xor .eax (.reg .esi),
  .store (spillAt 1) .eax, .mov .eax (.mem (spillAt 10)), .store (spillAt 6) .ebx,
  .mov .ebx (.mem (spillAt 1)), .mov .ecx (.mem (spillAt 0)), .mov .edx (.mem (spillAt 6))]

/-- The code of S-box 4. -/
def sboxCode3 : List Instr := [
  .mov .eax (.mem (spillAt 5)), .alu .xor .eax (.mem (spillAt 3)), .mov .ebx (.mem (spillAt 3)),
  .alu .xor .ebx (.mem (spillAt 1)), .mov .ecx (.mem (spillAt 4)), .alu .or .ecx (.mem (spillAt 2)),
  .alu .xor .ecx (.mem (spillAt 1)), .alu .xor .ecx Alloc.ones, .alu .and .ecx (.reg .ebx),
  .mov .edx (.mem (spillAt 4)), .alu .xor .edx Alloc.ones, .alu .and .edx (.reg .ebx),
  .mov .esi (.mem (spillAt 2)), .alu .xor .esi (.reg .edx), .mov .edi (.reg .eax),
  .alu .or .edi (.reg .esi), .alu .or .edi (.reg .ecx), .alu .xor .edi (.reg .ecx), .store (spillAt 3) .edx,
  .mov .edx (.mem (spillAt 4)), .alu .xor .edx (.reg .edi), .alu .and .esi (.reg .edx),
  .alu .or .ebx (.reg .esi), .alu .xor .ebx (.reg .esi), .alu .xor .eax (.reg .edx), .alu .xor .ebx Alloc.ones,
  .alu .and .ebx (.reg .eax), .alu .xor .ecx (.reg .ebx), .mov .ebx (.mem (spillAt 4)),
  .alu .xor .ebx (.mem (spillAt 2)), .store (spillAt 2) .edx, .mov .edx (.mem (spillAt 1)),
  .alu .or .edx (.mem (spillAt 3)), .alu .xor .eax (.reg .edx), .mov .edx (.reg .ebx), .alu .xor .edx Alloc.ones,
  .alu .and .edx (.reg .eax), .alu .xor .edi (.reg .edx), .mov .edx (.reg .ecx), .alu .xor .edx Alloc.ones,
  .alu .and .edx (.mem (spillAt 0)), .alu .xor .edx (.reg .edi), .alu .xor .edi Alloc.ones,
  .store (spillAt 3) .edx, .mov .edx (.mem (spillAt 0)), .alu .xor .edx Alloc.ones, .alu .and .edx (.reg .ecx),
  .alu .xor .edx (.reg .edi), .alu .xor .ecx (.reg .edi), .alu .xor .ebx Alloc.ones, .alu .and .ebx (.reg .ecx),
  .alu .or .esi (.reg .ebx), .alu .xor .eax (.reg .esi), .mov .esi (.mem (spillAt 2)),
  .alu .or .esi (.mem (spillAt 0)), .alu .xor .esi (.reg .eax), .mov .ebx (.mem (spillAt 0)),
  .alu .and .ebx (.mem (spillAt 2)), .alu .xor .ebx (.reg .eax), .mov .eax (.reg .ebx),
  .mov .ebx (.reg .esi), .mov .ecx (.reg .edx), .mov .edx (.mem (spillAt 3))]

/-- The code of S-box 5. -/
def sboxCode4 : List Instr := [
  .mov .eax (.mem (spillAt 5)), .alu .or .eax (.mem (spillAt 3)), .mov .ebx (.mem (spillAt 0)),
  .alu .xor .ebx Alloc.ones, .alu .and .ebx (.reg .eax), .mov .ecx (.mem (spillAt 5)), .alu .xor .ecx (.reg .ebx),
  .mov .edx (.mem (spillAt 3)), .alu .xor .edx (.reg .ecx), .mov .esi (.mem (spillAt 2)),
  .alu .or .esi (.reg .edx), .alu .or .ebx (.mem (spillAt 2)), .alu .xor .ebx (.mem (spillAt 2)),
  .alu .xor .ebx (.mem (spillAt 3)), .mov .edi (.mem (spillAt 1)), .alu .and .edi (.reg .ebx),
  .alu .or .edx (.mem (spillAt 5)), .alu .xor .edi (.reg .edx), .alu .xor .edi (.mem (spillAt 2)),
  .store (spillAt 3) .eax, .mov .eax (.mem (spillAt 0)), .alu .xor .eax (.reg .edi),
  .store (spillAt 0) .edi, .mov .edi (.reg .ecx), .alu .or .edi (.reg .eax), .store (spillAt 6) .eax,
  .mov .eax (.mem (spillAt 1)), .alu .and .eax (.reg .edi), .store (spillAt 7) .esi, .mov .esi (.reg .ecx),
  .alu .xor .esi (.reg .eax), .store (spillAt 8) .ecx, .mov .ecx (.mem (spillAt 2)),
  .alu .and .ecx (.reg .edx), .alu .xor .esi (.reg .ecx), .alu .or .edi (.mem (spillAt 5)),
  .alu .xor .edi (.mem (spillAt 5)), .mov .ecx (.reg .ebx), .alu .xor .ecx (.reg .edi),
  .store (spillAt 9) .edx, .mov .edx (.mem (spillAt 1)), .alu .xor .edx (.mem (spillAt 7)),
  .alu .xor .ecx Alloc.ones, .alu .and .ecx (.reg .edx), .alu .xor .ecx Alloc.ones, .alu .or .ecx (.mem (spillAt 4)),
  .alu .xor .ecx (.mem (spillAt 4)), .alu .xor .ecx (.mem (spillAt 0)), .store (spillAt 0) .ecx,
  .mov .ecx (.reg .eax), .alu .xor .ecx Alloc.ones, .alu .and .ecx (.reg .ebx), .alu .xor .edi (.reg .edx),
  .alu .or .edi (.reg .esi), .alu .xor .ecx Alloc.ones, .alu .and .ecx (.reg .edi), .mov .edi (.reg .ecx),
  .alu .xor .edi Alloc.ones, .alu .and .edi (.mem (spillAt 7)), .store (spillAt 1) .edi,
  .mov .edi (.mem (spillAt 6)), .alu .and .edi (.reg .ecx), .alu .xor .edx (.reg .edi),
  .mov .edi (.reg .ebx), .alu .and .edi (.mem (spillAt 9)), .alu .or .edi (.reg .edx),
  .alu .xor .eax (.reg .edi), .alu .and .eax (.mem (spillAt 4)), .alu .xor .eax (.reg .esi),
  .mov .esi (.mem (spillAt 5)), .alu .xor .esi (.mem (spillAt 3)), .alu .xor .ecx (.reg .esi),
  .mov .esi (.mem (spillAt 2)), .alu .and .esi (.reg .edx), .alu .xor .ecx (.reg .esi),
  .mov .esi (.mem (spillAt 1)), .alu .or .esi (.mem (spillAt 4)), .alu .xor .esi (.reg .ecx),
  .alu .xor .ebx (.mem (spillAt 7)), .alu .xor .ecx Alloc.ones, .alu .and .ecx (.reg .ebx),
  .alu .xor .edx (.mem (spillAt 8)), .alu .xor .ecx (.reg .edx), .mov .edx (.mem (spillAt 7)),
  .alu .and .edx (.mem (spillAt 4)), .alu .xor .edx (.reg .ecx), .mov .ebx (.mem (spillAt 0)),
  .mov .ecx (.reg .edx), .mov .edx (.reg .esi)]

/-- The code of S-box 6. -/
def sboxCode5 : List Instr := [
  .mov .eax (.mem (spillAt 4)), .alu .xor .eax (.mem (spillAt 1)), .mov .ebx (.mem (spillAt 4)),
  .alu .or .ebx (.mem (spillAt 0)), .alu .and .ebx (.mem (spillAt 5)), .alu .xor .eax (.reg .ebx),
  .mov .ecx (.mem (spillAt 0)), .alu .xor .ecx (.reg .eax), .mov .edx (.reg .ecx), .alu .xor .edx Alloc.ones,
  .alu .and .edx (.mem (spillAt 1)), .alu .and .ecx (.mem (spillAt 5)), .mov .esi (.mem (spillAt 4)),
  .alu .xor .esi (.reg .ecx), .mov .edi (.mem (spillAt 5)), .alu .xor .edi (.mem (spillAt 3)),
  .store (spillAt 6) .ecx, .mov .ecx (.reg .esi), .alu .or .ecx (.reg .edi), .store (spillAt 7) .ebx,
  .mov .ebx (.reg .eax), .alu .xor .ebx (.reg .ecx), .store (spillAt 8) .eax, .mov .eax (.mem (spillAt 3)),
  .alu .and .eax (.reg .ebx), .store (spillAt 9) .edi, .mov .edi (.mem (spillAt 0)), .alu .xor .edi Alloc.ones,
  .alu .and .edi (.reg .eax), .alu .or .esi (.reg .edx), .store (spillAt 10) .edx, .mov .edx (.reg .edi),
  .alu .xor .edx (.reg .esi), .store (spillAt 11) .edi, .mov .edi (.reg .edx),
  .alu .and .edi (.mem (spillAt 2)), .alu .xor .edi (.reg .ebx), .alu .xor .ecx (.mem (spillAt 4)),
  .store (spillAt 12) .edi, .mov .edi (.reg .ecx), .alu .xor .edi Alloc.ones, .alu .and .edi (.mem (spillAt 0)),
  .alu .xor .edi (.mem (spillAt 3)), .store (spillAt 3) .ecx, .mov .ecx (.reg .eax), .alu .xor .ecx Alloc.ones,
  .alu .and .ecx (.mem (spillAt 1)), .alu .or .ecx (.reg .edi), .store (spillAt 13) .eax,
  .mov .eax (.mem (spillAt 4)), .alu .or .eax (.mem (spillAt 9)), .alu .xor .edx (.reg .eax),
  .store (spillAt 9) .eax, .mov .eax (.mem (spillAt 7)), .alu .or .eax (.reg .ecx),
  .alu .xor .edx (.reg .eax), .alu .or .ebx (.mem (spillAt 5)), .alu .and .esi (.reg .ebx),
  .alu .xor .esi (.reg .edi), .mov .ebx (.mem (spillAt 11)), .alu .xor .ebx Alloc.ones,
  .alu .and .ebx (.reg .esi), .mov .eax (.mem (spillAt 10)), .alu .or .eax (.mem (spillAt 2)),
  .alu .xor .eax (.reg .ebx), .alu .xor .esi (.mem (spillAt 8)), .alu .xor .esi Alloc.ones,
  .alu .and .esi (.mem (spillAt 1)), .mov .ebx (.mem (spillAt 9)), .alu .xor .ebx Alloc.ones,
  .alu .xor .ebx (.mem (spillAt 3)), .alu .xor .esi (.reg .ebx), .alu .or .esi (.mem (spillAt 2)),
  .alu .xor .esi (.mem (spillAt 2)), .alu .xor .esi (.reg .edx), .mov .edx (.mem (spillAt 0)),
  .alu .xor .edx (.mem (spillAt 6)), .alu .xor .edi (.mem (spillAt 5)), .alu .and .edx (.reg .edi),
  .alu .xor .ebx (.mem (spillAt 13)), .alu .xor .edx (.reg .ebx), .alu .or .ecx (.mem (spillAt 2)),
  .alu .xor .ecx (.mem (spillAt 2)), .alu .xor .ecx (.reg .edx), .store (spillAt 2) .eax,
  .mov .eax (.mem (spillAt 12)), .mov .ebx (.mem (spillAt 2)), .store (spillAt 13) .ecx,
  .mov .ecx (.reg .esi), .mov .edx (.mem (spillAt 13))]

/-- The code of S-box 7. -/
def sboxCode6 : List Instr := [
  .mov .eax (.mem (spillAt 2)), .alu .xor .eax (.mem (spillAt 1)), .mov .ebx (.mem (spillAt 3)),
  .alu .xor .ebx (.reg .eax), .mov .ecx (.mem (spillAt 0)), .alu .and .ecx (.reg .ebx),
  .mov .edx (.mem (spillAt 2)), .alu .and .edx (.reg .eax), .mov .esi (.mem (spillAt 4)),
  .alu .xor .esi (.reg .edx), .mov .edi (.reg .ecx), .alu .and .edi (.reg .esi), .store (spillAt 6) .ecx,
  .mov .ecx (.mem (spillAt 0)), .alu .and .ecx (.reg .edx), .store (spillAt 7) .edx,
  .mov .edx (.mem (spillAt 3)), .alu .xor .edx (.reg .ecx), .store (spillAt 8) .ecx, .mov .ecx (.reg .esi),
  .alu .or .ecx (.reg .edx), .alu .xor .eax (.mem (spillAt 0)), .store (spillAt 9) .edx,
  .mov .edx (.reg .ecx), .alu .xor .edx (.reg .eax), .store (spillAt 10) .ecx, .mov .ecx (.reg .edi),
  .alu .xor .ecx Alloc.ones, .alu .and .ecx (.mem (spillAt 5)), .alu .xor .ecx (.reg .edx), .alu .xor .ebx Alloc.ones,
  .alu .and .ebx (.mem (spillAt 1)), .mov .edx (.reg .esi), .alu .or .edx (.reg .ebx),
  .store (spillAt 11) .ecx, .mov .ecx (.mem (spillAt 6)), .alu .xor .ecx (.mem (spillAt 9)),
  .alu .xor .edx (.reg .ecx), .alu .xor .eax (.mem (spillAt 6)), .store (spillAt 6) .edx,
  .mov .edx (.reg .eax), .alu .xor .edx Alloc.ones, .alu .and .edx (.mem (spillAt 2)), .store (spillAt 2) .edi,
  .mov .edi (.reg .edx), .alu .xor .edi Alloc.ones, .alu .and .edi (.reg .esi), .alu .xor .ecx (.mem (spillAt 1)),
  .alu .xor .edi (.reg .ecx), .alu .or .eax (.mem (spillAt 8)), .alu .xor .eax (.mem (spillAt 8)),
  .alu .or .edx (.reg .eax), .mov .ecx (.mem (spillAt 4)), .alu .xor .ecx (.mem (spillAt 10)),
  .alu .and .ecx (.reg .edi), .alu .xor .ecx (.reg .edx), .store (spillAt 10) .edx, .mov .edx (.reg .ecx),
  .alu .and .edx (.mem (spillAt 5)), .alu .xor .edx (.reg .edi), .alu .or .esi (.mem (spillAt 3)),
  .alu .xor .esi (.mem (spillAt 3)), .alu .or .eax (.reg .esi), .alu .or .edi (.mem (spillAt 7)),
  .alu .and .eax (.reg .edi), .alu .xor .ecx (.reg .eax), .alu .xor .ebx (.mem (spillAt 10)),
  .alu .and .ebx (.mem (spillAt 0)), .alu .or .ebx (.mem (spillAt 2)), .alu .xor .eax (.reg .ebx),
  .mov .edi (.mem (spillAt 5)), .alu .xor .edi Alloc.ones, .alu .and .edi (.reg .eax),
  .alu .xor .edi (.mem (spillAt 6)), .alu .and .ebx (.mem (spillAt 4)), .mov .esi (.mem (spillAt 6)),
  .alu .xor .esi Alloc.ones, .alu .xor .ebx (.reg .esi), .alu .xor .eax (.reg .ebx),
  .alu .or .ecx (.mem (spillAt 5)), .alu .xor .ecx (.reg .eax), .mov .eax (.mem (spillAt 11)),
  .mov .ebx (.reg .edx), .mov .edx (.reg .edi)]

/-- The code of S-box 8. -/
def sboxCode7 : List Instr := [
  .mov .eax (.mem (spillAt 4)), .alu .xor .eax Alloc.ones, .alu .and .eax (.mem (spillAt 3)),
  .mov .ebx (.mem (spillAt 3)), .alu .xor .ebx Alloc.ones, .alu .and .ebx (.mem (spillAt 1)),
  .alu .xor .ebx (.mem (spillAt 2)), .mov .ecx (.mem (spillAt 5)), .alu .and .ecx (.reg .ebx),
  .mov .edx (.reg .eax), .alu .xor .edx Alloc.ones, .alu .and .edx (.reg .ecx), .mov .esi (.reg .ebx),
  .alu .xor .esi Alloc.ones, .alu .and .esi (.mem (spillAt 4)), .mov .edi (.mem (spillAt 5)),
  .alu .or .edi (.reg .esi), .store (spillAt 6) .esi, .mov .esi (.mem (spillAt 3)), .alu .xor .esi Alloc.ones,
  .alu .and .esi (.mem (spillAt 4)), .alu .xor .esi (.mem (spillAt 1)), .store (spillAt 7) .edx,
  .mov .edx (.reg .edi), .alu .and .edx (.reg .esi), .alu .or .ecx (.reg .edx), .alu .xor .ebx Alloc.ones,
  .alu .xor .edx (.reg .ebx), .alu .xor .edi Alloc.ones, .alu .and .edi (.mem (spillAt 3)),
  .alu .xor .edx (.reg .edi), .alu .xor .eax (.reg .edx), .mov .edi (.mem (spillAt 7)),
  .alu .or .edi (.mem (spillAt 0)), .alu .xor .edi (.reg .eax), .alu .xor .eax (.mem (spillAt 5)),
  .mov .ebx (.mem (spillAt 1)), .alu .and .ebx (.reg .eax), .alu .xor .edx (.mem (spillAt 4)),
  .alu .xor .ebx (.reg .edx), .store (spillAt 3) .edi, .mov .edi (.mem (spillAt 6)),
  .alu .xor .edi (.reg .ebx), .alu .xor .ebx (.reg .ecx), .alu .or .ebx (.mem (spillAt 4)),
  .alu .xor .eax (.mem (spillAt 1)), .alu .xor .ebx (.reg .eax), .alu .and .ecx (.mem (spillAt 0)),
  .alu .xor .ecx (.reg .ebx), .alu .xor .esi (.reg .edi), .alu .or .edx (.mem (spillAt 2)),
  .alu .xor .edx (.reg .esi), .mov .eax (.mem (spillAt 5)), .alu .xor .eax (.reg .edx),
  .alu .and .eax (.mem (spillAt 0)), .alu .xor .eax (.reg .edi), .alu .or .esi (.mem (spillAt 2)),
  .alu .xor .esi (.mem (spillAt 2)), .alu .and .ebx (.reg .esi), .alu .xor .edx (.mem (spillAt 7)),
  .alu .xor .ebx (.reg .edx), .alu .or .ebx (.mem (spillAt 0)), .alu .xor .ebx (.reg .edi),
  .store (spillAt 0) .ebx, .mov .ebx (.reg .ecx), .mov .ecx (.mem (spillAt 3)),
  .mov .edx (.mem (spillAt 0))]

/-- Each S-box's code. -/
def sboxCode : Nat → List Instr
  | 0 => sboxCode0 | 1 => sboxCode1 | 2 => sboxCode2 | 3 => sboxCode3
  | 4 => sboxCode4 | 5 => sboxCode5 | 6 => sboxCode6 | _ => sboxCode7

#guard (List.range 8).all fun j =>
  compile (box j) ((List.range 6).map fun i => (i, i)) ((outputs j).zip outRegs) freeRegs
    ((List.range (spills - 6)).map (6 + ·)) == sboxCode j

/-- Bit `c` of the key word in slot `kslot` as a mask (the bit into the
carry, then `ecx - ecx - CF`), ⊕ the state word in slot `st`, into slot `i`. -/
def inputAt (kslot c st i : Nat) : List Instr :=
  [.mov .eax (.mem (ws kslot))] ++
    (if c = 31 then [.alu .add .eax (.reg .eax)] else [.shift .shr .eax (c + 1)]) ++
    [.alu .sbb .ecx (.reg .ecx), .alu .xor .ecx (.mem (ws st)), .store (ws i) .ecx]

/-- S-box `j`'s input `i`: key bit `inBit j i` as a mask, ⊕ the word of `E`. -/
def inputStep (ρ : Role) (j i : Nat) : List Instr :=
  inputAt (if inBit j i < 32 then kloSlot else khiSlot) (inBit j i % 32)
    (stSlot (readWord ρ (eBit (inBit j i)))) i

def inputCode (ρ : Role) (j : Nat) : List Instr := (List.range 6).flatMap (inputStep ρ j)

/-- XOR S-box `j`'s outputs into their words. -/
def outputCode (ρ : Role) (j : Nat) : List Instr :=
  (List.range 4).flatMap fun i =>
    [.alu .xor (outReg i) (.mem (ws (stSlot (writeWord ρ (outBit j i))))),
     .store (ws (stSlot (writeWord ρ (outBit j i)))) (outReg i)]

def sboxStep (ρ : Role) (j : Nat) : List Instr := inputCode ρ j ++ sboxCode j ++ outputCode ρ j

/-! ## Rounds and passes -/

/-- Copy the round key's words into the working space and step its pointer. -/
def keyLoad (d : Direction) : List Instr :=
  [.mov .eax (.mem (ws kpSlot)), .mov .ecx (.mem { base := .eax, disp := 0 }), .store (ws kloSlot) .ecx,
   .mov .ecx (.mem { base := .eax, disp := 4 }), .store (ws khiSlot) .ecx,
   .alu (if d = .encrypt then .add else .sub) .eax (.imm 8), .store (ws kpSlot) .eax]

def round (d : Direction) (ρ : Role) : List Instr := keyLoad d ++ (List.range 8).flatMap (sboxStep ρ)

/-- Two rounds, and the count of pairs left. -/
def roundPair (d : Direction) : List Instr :=
  round d .ba ++ round d .ab ++
    ([.mov .eax (.mem (ws cntSlot)), .alu .sub .eax (.imm 1), .store (ws cntSlot) .eax] : List Instr)

/-- Exchange the halves. -/
def swapHalves : List Instr :=
  (List.range 32).flatMap fun q =>
    [.mov .eax (.mem (ws (stSlot (lWord q)))), .mov .ecx (.mem (ws (stSlot (rWord q)))),
     .store (ws (stSlot (lWord q))) .ecx, .store (ws (stSlot (rWord q))) .eax]

/-- The offset in the schedule of a pass's first key. -/
def keyOff (c : Nat) (d : Direction) : Nat := 128 * c + if d = .encrypt then 0 else 120

/-- The key pointer at the pass's first key, and eight pairs of rounds to go. -/
def passStart (c : Nat) (d : Direction) : List Instr :=
  [.mov .eax (.mem (ws schedSlot)), .alu .add .eax (.imm (BitVec.ofNat 32 (keyOff c d))),
   .store (ws kpSlot) .eax, .mov .eax (.imm 8), .store (ws cntSlot) .eax]

/-- The caller's `ebx`, `esi` and `edi`, which `passRounds` restores, from
their slots. -/
def callerRegs : List Instr := [.mov .ebx (.mem (ws 83)), .mov .esi (.mem (ws 84)), .mov .edi (.mem (ws 85))]

/-- `vg_triple_des_pass_forward` and `vg_triple_des_pass_backward`: the
sixteen rounds of a pass with the key pointer stepping in direction `d`, and
the exchange of the halves, on the working space at `ebp`, called with the
key pointer and the count in their slots and `ebx`, `esi` and `edi` the words
in their slots (`callerRegs`), to which it restores them. -/
def passRounds (d : Direction) : Prog isa :=
  .seq (.loop (.block (roundPair d)) .ne) (.block (swapHalves ++ callerRegs))

/-- The name of `passRounds d`. -/
def passName : Direction → String
  | .encrypt => "vg_triple_des_pass_forward"
  | .decrypt => "vg_triple_des_pass_backward"

/-- A DES pass with schedule component `c`, in direction `d`: a call of
`passRounds d`. -/
def pass (c : Nat) (d : Direction) : Prog isa :=
  .seq (.block (passStart c d ++ callerRegs)) (.call (passName d) (passRounds d))

/-- The three passes of the operation. -/
def passes : Direction → Prog isa
  | .encrypt => .seq (pass 0 .encrypt) (.seq (pass 1 .decrypt) (pass 2 .encrypt))
  | .decrypt => .seq (pass 2 .decrypt) (.seq (pass 1 .encrypt) (pass 0 .decrypt))

/-! ## Transposition -/

/-- The bits `p` with `p &&& s = 0`. -/
def swapMask (s : Nat) : Nat :=
  (List.range 32).foldl (fun m p => if p &&& s = 0 then m ||| 2 ^ p else m) 0

/-- Exchange the bits `p + s` of the word in slot `a` and `p` of the word in
slot `b` (`p &&& s = 0`). -/
def swapBits (a b s : Nat) : List Instr :=
  [.mov .eax (.mem (ws a)), .mov .ecx (.mem (ws b)), .mov .edx (.reg .eax), .shift .shr .edx s,
   .alu .xor .edx (.reg .ecx), .alu .and .edx (.imm (BitVec.ofNat 32 (swapMask s))),
   .alu .xor .ecx (.reg .edx), .shift .ror .edx (32 - s), .alu .xor .eax (.reg .edx),
   .store (ws a) .eax, .store (ws b) .ecx]

/-- The stage of distance `s` on half `h`: the words `k` and `k + s` of each
`k` with `k &&& s = 0`. -/
def stage (h s : Nat) : List Instr :=
  ((List.range 32).filter fun k => k &&& s = 0).flatMap fun k =>
    swapBits (stSlot (32 * h + k)) (stSlot (32 * h + k + s)) s

/-- Transpose each half of the state words, the words `32 h + k`, in place. -/
def transpose : List Instr :=
  (List.range 2).flatMap fun h => [16, 8, 4, 2, 1].flatMap (stage h)

/-! ## The functions -/

/-- The working space's address into `ebp`, with the schedule's address and
the caller's registers in it. -/
def enter : List Instr :=
  [.mov .eax (.mem { base := .esp, disp := 4 }), .mov .ecx (.mem { base := .esp, disp := 8 }),
   .mov .edx (.reg .ebp), .mov .ebp (.reg .eax), .store (ws schedSlot) .ecx, .store (ws 83) .ebx,
   .store (ws 84) .esi, .store (ws 85) .edi, .store (ws 86) .edx]

/-- The caller's registers back, `ebp` last. -/
def leave : List Instr := saved.map fun p => .mov p.1 (.mem (ws p.2))

/-- The blocks' words to the state words. -/
def loadState : List Instr :=
  (List.range 64).flatMap fun j => [.mov .eax (.mem (ws (bufWord j))), .store (ws (stSlot j)) .eax]

/-- The state words back to the blocks. -/
def storeState : List Instr :=
  (List.range 64).flatMap fun j => [.mov .eax (.mem (ws (stSlot j))), .store (ws (bufWord j)) .eax]

/-- The blocks into the state words, through the transposition, the three
passes of the direction `d` and the transposition back, and out again. -/
def batch (d : Direction) : Prog isa :=
  .seq (.block (enter ++ loadState)) (.seq (.block transpose) (.seq (passes d)
    (.seq (.block transpose) (.block (storeState ++ leave)))))

def encryptBatch : Prog isa := batch .encrypt
def decryptBatch : Prog isa := batch .decrypt

end VG.Impl.TripleDes.X86.Bitslice
