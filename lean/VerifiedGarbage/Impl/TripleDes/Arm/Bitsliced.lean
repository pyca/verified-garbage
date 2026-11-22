module

public import VerifiedGarbage.Impl.TripleDes.BitsliceLayout
public import VerifiedGarbage.Spec.TripleDes
public import VerifiedGarbage.TCB.Arm.Isa
meta import VerifiedGarbage.Impl.TripleDes.BitsliceLayout
import VerifiedGarbage.Impl.TripleDes.Arm.BitsliceAlloc
meta import VerifiedGarbage.Impl.TripleDes.Arm.BitsliceAlloc

/-!
# Bitsliced Triple DES ECB on ARMv7

`ecb d` (schedule = r0, data = r1, n = r2, scratch = r3): the code of
`vg_triple_des_ecb_encrypt` and `vg_triple_des_ecb_decrypt` with their
working space, 1024 bytes, as an argument.

Constant-time Triple DES on 32 blocks at a time, bitsliced in 32-bit words
(Biham's bitslicing; the S-box circuits are Rusakov's, `BitsliceCircuit`),
as the 64-bit targets do on 64 blocks (`Impl/TripleDes/RISCV64/Bitsliced.lean`).
Everything lives in the working space, at `r3`, which no instruction writes:
the circuits' spilled values (`spills` words), the 64 state words (`stOff`),
the round key's two words (`kloOff`, `khiOff`), its pointer (`kpOff`), the
count of pairs of rounds left (`cntOff`), the function's arguments and the
batch's count while every register is in use (`schedOff`, `dataOff`, `nOff`,
`kOff`), and the callee-saved registers and `lr` (`savedOff`), which the
code uses.

* Up to 32 blocks are copied into the state words, block `b`'s low word to
  word `b` and its high word to word `32 + b`, and each half transposed in
  place, so that word `j` holds bit `j` of every block (`BitsliceLayout`,
  with 32-bit words); IP only renames words. The words of the other lanes
  hold whatever they held: their results are not stored.
* A round copies its key's two words into the working space and steps the
  key pointer. S-box `j`'s input `i` is key bit `inBit j i` as a mask (the
  bit, isolated, subtracted from zero), XORed with the state word of `E`.
  Each S-box's circuit then runs in registers and `spills` words of the
  working space (`BitsliceAlloc`), and its four outputs are XORed into the
  state words of `L` that P sends them to. Rounds alternate between reading
  the words of `R` (`.ba`) and of `L` (`.ab`), so no word moves; a pass of
  sixteen rounds, eight times both, ends by exchanging the halves, as DES's
  swap and the next pass's IP do.
* The three passes are unrolled, each with its schedule component and key
  direction, in a function of their own (`passesCall`).
* The state is transposed back and the blocks copied out; the data pointer
  `r1` and the blocks left `r2` advance.

Every address and branch depends only on the pointers, `n` and the loop
counters, which are in registers or in words of the working space that only
they are stored to.
-/

@[expose] public section

namespace VG.Impl.TripleDes.Arm.Bitslice

open VG.Arm VG.Impl.TripleDes.Bitslice
open VG.Spec.TripleDes (Direction)

/-! ## Registers and the working space -/

/-- The working space's base. -/
def base : Reg := .r3

/-- The words the circuits spill to, the first of the working space. -/
def spills : Nat := 8
/-- State word `j`. -/
def stOff (j : Nat) : Nat := 4 * (spills + j)
/-- The round key's low and high words. -/
def kloOff : Nat := 288
def khiOff : Nat := 292
/-- The round key's pointer. -/
def kpOff : Nat := 296
/-- The pairs of rounds left. -/
def cntOff : Nat := 300
/-- The schedule, the data, the blocks left and the batch's blocks. -/
def schedOff : Nat := 304
def dataOff : Nat := 308
def nOff : Nat := 312
def kOff : Nat := 316
/-- The saved registers. -/
def savedOff : Nat := 320

/-- The registers the code saves, and their offsets in the working space. -/
def saved : List (Reg × Nat) :=
  [(.r4, 320), (.r5, 324), (.r6, 328), (.r7, 332), (.r8, 336), (.r9, 340), (.r10, 344), (.r11, 348),
   (.lr, 352)]

/-! ## S-boxes -/

def inRegs : List Reg := [.r4, .r5, .r6, .r7, .r8, .r9]
def freeRegs : List Reg := [.r0, .r1, .r2, .r10, .r11, .r12, .lr]
def inReg (i : Nat) : Reg := inRegs.getD i .r4

/-! The code of the S-boxes, as `compile` allocates it for their circuits. It is written
out (and `#guard` checks that it is what `compile` produces) so that the kernel, which
evaluates the code in the proofs, does not have to run the allocator. -/

/-- The code of S-box 1. -/
def sboxCode0 : List Instr := [
  .dp .bic .r0 .r9 (.reg .r5), .dp .eor .r1 .r6 (.reg .r0), .dp .orr .r2 .r7 (.reg .r4),
  .dp .eor .r10 .r9 (.reg .r7), .dp .and .r11 .r2 (.reg .r10), .dp .eor .r12 .r6 (.reg .r11),
  .dp .bic .lr .r12 (.reg .r1), .str .r8 .r3 0, .dp .eor .r8 .r5 (.reg .r4), .str .r2 .r3 4,
  .dp .eor .r2 .r7 (.reg .r8), .dp .bic .r2 .r1 (.reg .r2), .dp .orr .r11 .r4 (.reg .r11),
  .dp .eor .r2 .r2 (.reg .r11), .dp .bic .r11 .r2 (.reg .lr), .dp .orr .r4 .r9 (.reg .r4),
  .str .r11 .r3 8, .dp .orr .r11 .r2 (.reg .r4), .dp .bic .r12 .r5 (.reg .r12), .str .r5 .r3 12,
  .dp .eor .r5 .r11 (.reg .r12), .dp .bic .r6 .r6 (.reg .r4), .dp .eor .r6 .r12 (.reg .r6),
  .dp .bic .r10 .r8 (.reg .r10), .dp .orr .r6 .r6 (.reg .r10), .dp .bic .r7 .r7 (.reg .r0),
  .dp .eor .r0 .r1 (.reg .r11), .dp .bic .r0 .r0 (.reg .r7), .ldr .r7 .r3 4,
  .dp .and .r2 .r7 (.reg .r2), .dp .eor .r2 .r0 (.reg .r2), .ldr .r10 .r3 0,
  .dp .bic .r5 .r5 (.reg .r10), .dp .eor .r5 .r5 (.reg .r2), .dp .eor .r0 .r8 (.reg .r0),
  .dp .orr .r12 .r12 (.reg .r0), .dp .eor .r12 .r7 (.reg .r12), .dp .eor .r9 .r9 (.reg .r12),
  .dp .eor .r2 .r2 (.reg .r9), .dp .orr .lr .lr (.reg .r10), .dp .eor .lr .lr (.reg .r2),
  .dp .eor .r7 .r7 (.reg .r11), .dp .orr .r7 .r6 (.reg .r7), .dp .eor .r7 .r9 (.reg .r7),
  .dp .bic .r8 .r2 (.reg .r8), .dp .eor .r8 .r7 (.reg .r8), .ldr .r2 .r3 8,
  .dp .orr .r11 .r2 (.reg .r10), .dp .eor .r11 .r11 (.reg .r8), .ldr .r8 .r3 12,
  .dp .orr .r8 .r8 (.reg .r1), .dp .bic .r8 .r8 (.reg .r7), .dp .and .r2 .r2 (.reg .r9),
  .dp .eor .r8 .r8 (.reg .r2), .dp .orr .r8 .r8 (.reg .r10), .dp .eor .r8 .r8 (.reg .r6),
  .mvn .r5 (.reg .r5), .mvn .r11 (.reg .r11), .mvn .lr (.reg .lr)]

/-- The code of S-box 2. -/
def sboxCode1 : List Instr := [
  .dp .eor .r0 .r8 (.reg .r5), .dp .bic .r1 .r9 (.reg .r4), .dp .bic .r1 .r5 (.reg .r1),
  .dp .orr .r2 .r8 (.reg .r1), .dp .bic .r10 .r0 (.reg .r4), .dp .and .r11 .r9 (.reg .r0),
  .dp .eor .r5 .r5 (.reg .r11), .dp .bic .r11 .r5 (.reg .r10), .dp .and .r12 .r7 (.reg .r4),
  .dp .eor .r1 .r1 (.reg .r10), .dp .and .r1 .r2 (.reg .r1), .dp .bic .r10 .r1 (.reg .r12),
  .dp .and .lr .r7 (.reg .r1), .dp .eor .r9 .lr (.reg .r9), .dp .eor .r4 .r4 (.reg .r0),
  .str .r11 .r3 0, .dp .bic .r11 .r4 (.reg .r12), .str .r0 .r3 4, .dp .eor .r0 .r9 (.reg .r11),
  .dp .bic .r10 .r6 (.reg .r10), .dp .eor .r10 .r10 (.reg .r0), .dp .bic .r8 .r8 (.reg .r11),
  .dp .eor .r5 .r5 (.reg .r8), .dp .orr .r9 .r9 (.reg .r5), .dp .eor .r7 .r7 (.reg .r4),
  .dp .eor .r9 .r9 (.reg .r7), .dp .bic .r11 .r2 (.reg .r6), .dp .eor .r11 .r11 (.reg .r9),
  .dp .eor .lr .lr (.reg .r8), .dp .orr .r7 .r7 (.reg .lr), .dp .eor .r2 .r2 (.reg .r0),
  .dp .bic .r12 .r2 (.reg .r12), .dp .eor .lr .r7 (.reg .r12), .dp .eor .r1 .r1 (.reg .r0),
  .dp .eor .r9 .r9 (.reg .r1), .dp .bic .r12 .r9 (.reg .r12), .ldr .r9 .r3 4,
  .dp .and .r9 .r9 (.reg .r7), .dp .eor .r12 .r12 (.reg .r9), .dp .orr .r9 .r12 (.reg .r6),
  .dp .eor .r9 .r9 (.reg .lr), .dp .bic .r12 .r12 (.reg .r5), .dp .bic .r4 .r2 (.reg .r4),
  .dp .eor .r12 .r12 (.reg .r4), .ldr .r4 .r3 0, .dp .orr .r4 .r4 (.reg .r6),
  .dp .eor .r4 .r4 (.reg .r12), .mvn .r4 (.reg .r4), .mvn .r9 (.reg .r9), .mvn .r10 (.reg .r10),
  .mvn .r11 (.reg .r11)]

/-- The code of S-box 3. -/
def sboxCode2 : List Instr := [
  .dp .bic .r0 .r9 (.reg .r8), .dp .eor .r1 .r7 (.reg .r4), .dp .orr .r2 .r0 (.reg .r1),
  .dp .eor .r10 .r6 (.reg .r4), .dp .bic .r11 .r10 (.reg .r9), .dp .eor .r12 .r2 (.reg .r11),
  .dp .eor .lr .r8 (.reg .r1), .str .r0 .r3 0, .dp .bic .r0 .lr (.reg .r4),
  .dp .eor .r2 .r2 (.reg .r0), .dp .bic .r0 .r12 (.reg .r2), .str .r0 .r3 4,
  .dp .and .r0 .r4 (.reg .r12), .dp .orr .r0 .r6 (.reg .r0), .dp .and .r0 .r9 (.reg .r0),
  .dp .eor .r0 .lr (.reg .r0), .str .lr .r3 8, .dp .bic .lr .r12 (.reg .r5),
  .dp .eor .lr .lr (.reg .r0), .dp .and .r1 .r1 (.reg .r10), .dp .eor .r10 .r9 (.reg .r6),
  .str .lr .r3 12, .dp .eor .lr .r2 (.reg .r10), .dp .orr .lr .r7 (.reg .lr),
  .dp .bic .lr .lr (.reg .r1), .dp .orr .r11 .r11 (.reg .r10), .dp .bic .r10 .r0 (.reg .r11),
  .dp .and .r4 .r6 (.reg .r4), .dp .bic .r1 .r4 (.reg .r8), .dp .eor .r10 .r10 (.reg .r1),
  .dp .and .r2 .r2 (.reg .r10), .ldr .r1 .r3 8, .dp .orr .r4 .r1 (.reg .r4),
  .dp .bic .r4 .r4 (.reg .r2), .dp .eor .r9 .r9 (.reg .r4), .dp .and .lr .lr (.reg .r5),
  .dp .eor .lr .lr (.reg .r9), .dp .bic .r8 .r12 (.reg .r8), .dp .bic .r7 .r8 (.reg .r7),
  .dp .eor .r1 .r1 (.reg .r7), .dp .eor .r11 .r11 (.reg .r1), .ldr .r7 .r3 4,
  .dp .bic .r7 .r5 (.reg .r7), .dp .eor .r7 .r7 (.reg .r11), .dp .bic .r6 .r6 (.reg .r12),
  .dp .eor .r0 .r0 (.reg .r6), .dp .bic .r1 .r1 (.reg .r0), .ldr .r0 .r3 0,
  .dp .eor .r0 .r0 (.reg .r9), .dp .eor .r1 .r1 (.reg .r0), .dp .orr .r10 .r10 (.reg .r5),
  .dp .eor .r10 .r10 (.reg .r1), .ldr .r1 .r3 12, .mvn .r10 (.reg .r10), .mvn .r7 (.reg .r7)]

/-- The code of S-box 4. -/
def sboxCode3 : List Instr := [
  .dp .eor .r9 .r9 (.reg .r7), .dp .eor .r7 .r7 (.reg .r5), .dp .orr .r0 .r8 (.reg .r6),
  .dp .eor .r0 .r5 (.reg .r0), .dp .bic .r0 .r7 (.reg .r0), .dp .bic .r1 .r7 (.reg .r8),
  .dp .eor .r2 .r6 (.reg .r1), .dp .orr .r10 .r9 (.reg .r2), .dp .bic .r10 .r10 (.reg .r0),
  .dp .eor .r11 .r8 (.reg .r10), .dp .and .r2 .r2 (.reg .r11), .dp .bic .r7 .r7 (.reg .r2),
  .dp .eor .r9 .r9 (.reg .r11), .dp .bic .r7 .r9 (.reg .r7), .dp .eor .r0 .r0 (.reg .r7),
  .dp .eor .r8 .r8 (.reg .r6), .dp .orr .r5 .r5 (.reg .r1), .dp .eor .r9 .r9 (.reg .r5),
  .dp .bic .r5 .r9 (.reg .r8), .dp .eor .r10 .r10 (.reg .r5), .dp .bic .r5 .r4 (.reg .r0),
  .dp .eor .r5 .r5 (.reg .r10), .dp .bic .r1 .r0 (.reg .r4), .dp .eor .r1 .r1 (.reg .r10),
  .dp .eor .r0 .r0 (.reg .r10), .dp .orr .r0 .r0 (.reg .r8), .dp .bic .r2 .r0 (.reg .r2),
  .dp .eor .r9 .r9 (.reg .r2), .dp .orr .r2 .r11 (.reg .r4), .dp .eor .r2 .r2 (.reg .r9),
  .dp .and .r4 .r4 (.reg .r11), .dp .eor .r4 .r4 (.reg .r9), .mvn .r4 (.reg .r4),
  .mvn .r2 (.reg .r2), .mvn .r1 (.reg .r1)]

/-- The code of S-box 5. -/
def sboxCode4 : List Instr := [
  .dp .orr .r0 .r9 (.reg .r7), .dp .bic .r1 .r0 (.reg .r4), .dp .eor .r2 .r9 (.reg .r1),
  .dp .eor .r10 .r7 (.reg .r2), .dp .orr .r11 .r6 (.reg .r10), .dp .bic .r1 .r1 (.reg .r6),
  .dp .eor .r7 .r7 (.reg .r1), .dp .and .r1 .r5 (.reg .r7), .dp .orr .r10 .r9 (.reg .r10),
  .dp .eor .r1 .r1 (.reg .r10), .dp .eor .r1 .r6 (.reg .r1), .dp .eor .r4 .r4 (.reg .r1),
  .dp .orr .r12 .r2 (.reg .r4), .dp .and .lr .r5 (.reg .r12), .str .r0 .r3 0,
  .dp .eor .r0 .r2 (.reg .lr), .str .r2 .r3 4, .dp .and .r2 .r6 (.reg .r10),
  .dp .eor .r0 .r0 (.reg .r2), .dp .bic .r12 .r12 (.reg .r9), .dp .eor .r2 .r7 (.reg .r12),
  .dp .eor .r5 .r5 (.reg .r11), .dp .bic .r2 .r5 (.reg .r2), .dp .orr .r2 .r2 (.reg .r8),
  .dp .eor .r2 .r2 (.reg .r1), .dp .bic .r1 .r7 (.reg .lr), .dp .eor .r12 .r12 (.reg .r5),
  .dp .orr .r12 .r0 (.reg .r12), .dp .bic .r12 .r12 (.reg .r1), .dp .bic .r1 .r11 (.reg .r12),
  .dp .and .r4 .r4 (.reg .r12), .dp .eor .r5 .r5 (.reg .r4), .dp .and .r10 .r7 (.reg .r10),
  .dp .orr .r10 .r5 (.reg .r10), .dp .eor .lr .lr (.reg .r10), .dp .and .lr .lr (.reg .r8),
  .dp .eor .lr .lr (.reg .r0), .ldr .r0 .r3 0, .dp .eor .r9 .r9 (.reg .r0),
  .dp .eor .r12 .r12 (.reg .r9), .dp .and .r6 .r6 (.reg .r5), .dp .eor .r12 .r12 (.reg .r6),
  .dp .orr .r1 .r1 (.reg .r8), .dp .eor .r1 .r1 (.reg .r12), .dp .eor .r7 .r11 (.reg .r7),
  .dp .bic .r7 .r7 (.reg .r12), .ldr .r12 .r3 4, .dp .eor .r12 .r12 (.reg .r5),
  .dp .eor .r7 .r7 (.reg .r12), .dp .and .r11 .r11 (.reg .r8), .dp .eor .r11 .r11 (.reg .r7),
  .mvn .r2 (.reg .r2)]

/-- The code of S-box 6. -/
def sboxCode5 : List Instr := [
  .dp .eor .r0 .r8 (.reg .r5), .dp .orr .r1 .r8 (.reg .r4), .dp .and .r1 .r9 (.reg .r1),
  .dp .eor .r0 .r0 (.reg .r1), .dp .eor .r2 .r4 (.reg .r0), .dp .bic .r10 .r5 (.reg .r2),
  .dp .and .r2 .r9 (.reg .r2), .dp .eor .r11 .r8 (.reg .r2), .dp .eor .r12 .r9 (.reg .r7),
  .dp .orr .lr .r11 (.reg .r12), .str .r2 .r3 0, .dp .eor .r2 .r0 (.reg .lr), .str .r0 .r3 4,
  .dp .and .r0 .r7 (.reg .r2), .str .r9 .r3 8, .dp .bic .r9 .r0 (.reg .r4),
  .dp .orr .r11 .r10 (.reg .r11), .str .r10 .r3 12, .dp .eor .r10 .r9 (.reg .r11), .str .r9 .r3 16,
  .dp .and .r9 .r10 (.reg .r6), .dp .eor .r9 .r9 (.reg .r2), .dp .eor .lr .r8 (.reg .lr),
  .str .r9 .r3 20, .dp .bic .r9 .r4 (.reg .lr), .dp .eor .r7 .r7 (.reg .r9),
  .dp .bic .r9 .r5 (.reg .r0), .dp .orr .r9 .r7 (.reg .r9), .dp .orr .r8 .r8 (.reg .r12),
  .dp .eor .r10 .r10 (.reg .r8), .dp .orr .r1 .r1 (.reg .r9), .dp .eor .r10 .r10 (.reg .r1),
  .ldr .r1 .r3 8, .dp .orr .r2 .r1 (.reg .r2), .dp .and .r11 .r11 (.reg .r2),
  .dp .eor .r11 .r7 (.reg .r11), .ldr .r2 .r3 16, .dp .bic .r2 .r11 (.reg .r2), .ldr .r12 .r3 12,
  .dp .orr .r12 .r12 (.reg .r6), .dp .eor .r12 .r12 (.reg .r2), .ldr .r2 .r3 4,
  .dp .eor .r2 .r2 (.reg .r11), .dp .bic .r5 .r5 (.reg .r2), .dp .eor .lr .lr (.reg .r8),
  .dp .eor .r5 .r5 (.reg .lr), .dp .orr .r5 .r5 (.reg .r6), .dp .eor .r5 .r5 (.reg .r10),
  .ldr .r10 .r3 0, .dp .eor .r4 .r4 (.reg .r10), .dp .eor .r1 .r1 (.reg .r7),
  .dp .and .r4 .r4 (.reg .r1), .dp .eor .r0 .r0 (.reg .lr), .dp .eor .r4 .r4 (.reg .r0),
  .dp .bic .r9 .r9 (.reg .r6), .dp .eor .r9 .r9 (.reg .r4), .ldr .r4 .r3 20, .mvn .r5 (.reg .r5),
  .mvn .r9 (.reg .r9)]

/-- The code of S-box 7. -/
def sboxCode6 : List Instr := [
  .dp .eor .r0 .r6 (.reg .r5), .dp .eor .r1 .r7 (.reg .r0), .dp .and .r2 .r4 (.reg .r1),
  .dp .and .r10 .r6 (.reg .r0), .dp .eor .r11 .r8 (.reg .r10), .dp .and .r12 .r2 (.reg .r11),
  .dp .and .lr .r4 (.reg .r10), .str .r10 .r3 0, .dp .eor .r10 .r7 (.reg .lr), .str .r7 .r3 4,
  .dp .orr .r7 .r11 (.reg .r10), .dp .eor .r0 .r4 (.reg .r0), .str .r4 .r3 8,
  .dp .eor .r4 .r7 (.reg .r0), .str .r7 .r3 12, .dp .bic .r7 .r9 (.reg .r12),
  .dp .eor .r7 .r7 (.reg .r4), .dp .bic .r1 .r5 (.reg .r1), .dp .orr .r4 .r11 (.reg .r1),
  .dp .eor .r10 .r2 (.reg .r10), .dp .eor .r4 .r4 (.reg .r10), .dp .eor .r2 .r2 (.reg .r0),
  .dp .bic .r6 .r6 (.reg .r2), .dp .bic .r0 .r11 (.reg .r6), .dp .eor .r5 .r5 (.reg .r10),
  .dp .eor .r0 .r0 (.reg .r5), .dp .bic .r2 .r2 (.reg .lr), .dp .orr .r6 .r6 (.reg .r2),
  .ldr .lr .r3 12, .dp .eor .lr .r8 (.reg .lr), .dp .and .lr .r0 (.reg .lr),
  .dp .eor .lr .r6 (.reg .lr), .dp .and .r5 .lr (.reg .r9), .dp .eor .r5 .r5 (.reg .r0),
  .ldr .r10 .r3 4, .dp .bic .r11 .r11 (.reg .r10), .dp .orr .r2 .r2 (.reg .r11), .ldr .r11 .r3 0,
  .dp .orr .r11 .r11 (.reg .r0), .dp .and .r2 .r2 (.reg .r11), .dp .eor .lr .lr (.reg .r2),
  .dp .eor .r1 .r1 (.reg .r6), .ldr .r6 .r3 8, .dp .and .r6 .r6 (.reg .r1),
  .dp .orr .r12 .r12 (.reg .r6), .dp .eor .r2 .r2 (.reg .r12), .dp .bic .r6 .r2 (.reg .r9),
  .dp .eor .r6 .r6 (.reg .r4), .dp .and .r8 .r8 (.reg .r12), .dp .eor .r8 .r8 (.reg .r4),
  .dp .eor .r2 .r2 (.reg .r8), .dp .orr .lr .lr (.reg .r9), .dp .eor .lr .lr (.reg .r2),
  .mvn .lr (.reg .lr)]

/-- The code of S-box 8. -/
def sboxCode7 : List Instr := [
  .dp .bic .r0 .r7 (.reg .r8), .dp .bic .r1 .r5 (.reg .r7), .dp .eor .r1 .r6 (.reg .r1),
  .dp .and .r2 .r9 (.reg .r1), .dp .bic .r10 .r2 (.reg .r0), .dp .bic .r11 .r8 (.reg .r1),
  .dp .orr .r12 .r9 (.reg .r11), .dp .bic .lr .r8 (.reg .r7), .dp .eor .lr .r5 (.reg .lr),
  .str .r6 .r3 0, .dp .and .r6 .r12 (.reg .lr), .dp .orr .r2 .r2 (.reg .r6),
  .dp .eor .r6 .r6 (.reg .r1), .dp .bic .r7 .r7 (.reg .r12), .dp .eor .r6 .r6 (.reg .r7),
  .dp .eor .r0 .r0 (.reg .r6), .dp .orr .r7 .r10 (.reg .r4), .dp .eor .r7 .r7 (.reg .r0),
  .dp .eor .r0 .r9 (.reg .r0), .dp .bic .r12 .r5 (.reg .r0), .dp .eor .r6 .r8 (.reg .r6),
  .dp .eor .r12 .r12 (.reg .r6), .dp .eor .r11 .r11 (.reg .r12), .dp .eor .r12 .r2 (.reg .r12),
  .dp .bic .r8 .r12 (.reg .r8), .dp .eor .r5 .r5 (.reg .r0), .dp .eor .r8 .r8 (.reg .r5),
  .dp .and .r2 .r2 (.reg .r4), .dp .eor .r2 .r2 (.reg .r8), .dp .eor .lr .lr (.reg .r11),
  .ldr .r5 .r3 0, .dp .bic .r6 .r6 (.reg .r5), .dp .eor .r6 .lr (.reg .r6),
  .dp .eor .r9 .r9 (.reg .r6), .dp .and .r9 .r9 (.reg .r4), .dp .eor .r9 .r9 (.reg .r11),
  .dp .orr .lr .lr (.reg .r5), .dp .bic .r8 .r8 (.reg .lr), .dp .eor .r10 .r10 (.reg .r6),
  .dp .eor .r8 .r8 (.reg .r10), .dp .orr .r8 .r8 (.reg .r4), .dp .eor .r8 .r8 (.reg .r11),
  .mvn .r9 (.reg .r9), .mvn .r7 (.reg .r7), .mvn .r8 (.reg .r8)]

/-- Each S-box's code and the registers of its outputs. -/
def sboxCompiled : Nat → List Instr × List Reg
  | 0 => (sboxCode0, [.r8, .r5, .r11, .lr])
  | 1 => (sboxCode1, [.r4, .r9, .r10, .r11])
  | 2 => (sboxCode2, [.r1, .r10, .lr, .r7])
  | 3 => (sboxCode3, [.r4, .r2, .r1, .r5])
  | 4 => (sboxCode4, [.lr, .r2, .r11, .r1])
  | 5 => (sboxCode5, [.r4, .r12, .r5, .r9])
  | 6 => (sboxCode6, [.r7, .r5, .lr, .r6])
  | _ => (sboxCode7, [.r9, .r2, .r7, .r8])

#guard (List.range 8).all fun j =>
  let c := compile base (box j) inRegs (outputs j) freeRegs (List.range spills)
  c.2.2 && (c.1, c.2.1) == sboxCompiled j

def sboxCode (j : Nat) : List Instr := (sboxCompiled j).1

/-- The registers of each S-box's outputs. -/
def outRegsTable : List (List Reg) := (List.range 8).map fun j => (sboxCompiled j).2

/-- The register of S-box `j`'s output `i`. -/
def outReg (j i : Nat) : Reg := (outRegsTable.getD j []).getD i .r0

/-- The round key's low and high words, zero, and a temporary for the state words. -/
def klo : Reg := .r0
def khi : Reg := .r1
def zero : Reg := .r2
def tmp : Reg := .r10

/-- The round key's words and zero into their registers. -/
def keyRegs : List Instr := [.ldr klo base kloOff, .ldr khi base khiOff, .mov zero (.imm 0)]

/-- `r >> n`, as a second operand. -/
def shrOp (r : Reg) (n : Nat) : Op2 := if n = 0 then .reg r else .shifted r .lsr n

/-- Bit `c` of the key word in `kr` as a mask in `q`, ⊕ the state word at `off`. -/
def inputAt (q kr : Reg) (c off : Nat) : List Instr :=
  [.dp .and q kr (.imm (BitVec.ofNat 32 (2 ^ c))), .dp .sub q zero (shrOp q c),
   .ldr tmp base off, .dp .eor q q (.reg tmp)]

/-- S-box `j`'s input `i`: key bit `inBit j i` as a mask, ⊕ the word of `E`. -/
def inputStep (ρ : Role) (j i : Nat) : List Instr :=
  inputAt (inReg i) (if inBit j i < 32 then klo else khi) (inBit j i % 32)
    (stOff (readWord ρ (eBit (inBit j i))))

def inputCode (ρ : Role) (j : Nat) : List Instr := (List.range 6).flatMap (inputStep ρ j)

/-- A register that holds none of S-box `j`'s outputs. -/
def outTmp (j : Nat) : Reg :=
  ([Reg.r0, .r1, .r2, .r10, .r12].find? fun r => (List.range 4).all fun i => outReg j i != r).getD .r0

/-- XOR S-box `j`'s outputs into their words. -/
def outputCode (ρ : Role) (j : Nat) : List Instr :=
  (List.range 4).flatMap fun i =>
    [.ldr (outTmp j) base (stOff (writeWord ρ (outBit j i))),
     .dp .eor (outTmp j) (outTmp j) (.reg (outReg j i)),
     .str (outTmp j) base (stOff (writeWord ρ (outBit j i)))]

def sboxStep (ρ : Role) (j : Nat) : List Instr :=
  keyRegs ++ inputCode ρ j ++ sboxCode j ++ outputCode ρ j

/-! ## Rounds and passes -/

/-- Copy the round key's words into the working space and step its pointer. -/
def keyLoad (d : Direction) : List Instr :=
  [.ldr .r0 base kpOff, .ldr .r1 .r0 0, .ldr .r2 .r0 4, .str .r1 base kloOff, .str .r2 base khiOff,
   .dp (if d = .encrypt then .add else .sub) .r0 .r0 (.imm 8), .str .r0 base kpOff]

def round (d : Direction) (ρ : Role) : List Instr := keyLoad d ++ (List.range 8).flatMap (sboxStep ρ)

/-- Two rounds, and the count of pairs left. -/
def roundPair (d : Direction) : List Instr :=
  round d .ba ++ round d .ab ++
    ([.ldr .r0 base cntOff, .subs .r0 .r0 (.imm 1), .str .r0 base cntOff] : List Instr)

/-- Exchange the halves. -/
def swapHalves : List Instr :=
  (List.range 32).flatMap fun q =>
    [.ldr .r0 base (stOff (lWord q)), .ldr .r1 base (stOff (rWord q)),
     .str .r1 base (stOff (lWord q)), .str .r0 base (stOff (rWord q))]

/-- The offset in the schedule of a pass's first key. -/
def keyOff (c : Nat) (d : Direction) : Nat := 128 * c + if d = .encrypt then 0 else 120

/-- The key pointer at the pass's first key, and eight pairs of rounds to go. -/
def passStart (c : Nat) (d : Direction) : List Instr :=
  [.ldr .r0 base schedOff, .dp .add .r0 .r0 (.imm (BitVec.ofNat 32 (keyOff c d))), .str .r0 base kpOff,
   .mov .r0 (.imm 8), .str .r0 base cntOff]

/-- A DES pass with schedule component `c`, in direction `d`. -/
def pass (c : Nat) (d : Direction) : Prog isa :=
  .seq (.block (passStart c d)) (.seq (.loop (.block (roundPair d)) .ne) (.block swapHalves))

/-- The three passes of the operation. -/
def passes : Direction → Prog isa
  | .encrypt => .seq (pass 0 .encrypt) (.seq (pass 1 .decrypt) (pass 2 .encrypt))
  | .decrypt => .seq (pass 2 .decrypt) (.seq (pass 1 .encrypt) (pass 0 .decrypt))

/-- The word of the working space that keeps the return address of the
passes as a function: word 6, a word of the spills that the circuits do not
use (`Proof/TripleDes/Arm/Bitsliced/Pass.lean`, `keepsLr`, checks that no
instruction of the passes stores to it). -/
def lrOff : Nat := 24

/-- `vg_triple_des_passes_encrypt` and `vg_triple_des_passes_decrypt`: the
three passes, which every bitsliced function of the direction calls, so that
their code is in the crate once. -/
def passesFn (d : Direction) : Prog isa :=
  .seq (.block [.str .lr base lrOff]) (.seq (passes d) (.block [.ldr .lr base lrOff]))

def passesName : Direction → String
  | .encrypt => "vg_triple_des_passes_encrypt"
  | .decrypt => "vg_triple_des_passes_decrypt"

/-- A call of the passes. -/
def passesCall (d : Direction) : Prog isa := .call (passesName d) (passesFn d)

/-! ## Transposition -/

/-- The bits `p` with `p &&& s = 0`. -/
def swapMask (s : Nat) : Nat :=
  (List.range 32).foldl (fun m p => if p &&& s = 0 then m ||| 2 ^ p else m) 0

/-- The constant `v` into `d`. -/
def movImm (d : Reg) (v : Nat) : List Instr :=
  [.movw d (BitVec.ofNat 16 v), .movt d (BitVec.ofNat 16 (v / 65536))]

/-- Exchange the bits `p + s` of `a` and `p` of `b` (`p &&& s = 0`), masked by `m`. -/
def swapBits (a b t m : Reg) (s : Nat) : List Instr :=
  [.dp .eor t b (.shifted a .lsr s), .dp .and t t (.reg m), .dp .eor b b (.reg t),
   .dp .eor a a (.shifted t .ror (32 - s))]

def groupRegs : List Reg := [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11]
def groupReg (k : Nat) : Reg := groupRegs.getD k .r4

/-- The stages `ds` (the distance between a pair's words, in words of the
group, and the mask's register) on `n` words, the state words `word k`: the
stage of distance `d` exchanges bits `unit * d` apart. -/
def group (n : Nat) (ds : List (Nat × Reg)) (word : Nat → Nat) (unit : Nat) : List Instr :=
  (List.range n).map (fun k => .ldr (groupReg k) base (stOff (word k))) ++
  (ds.flatMap fun (d, m) =>
    ((List.range n).filter (fun k => k &&& d = 0)).flatMap fun k =>
      swapBits (groupReg k) (groupReg (k + d)) .r12 m (unit * d)) ++
  (List.range n).map (fun k => .str (groupReg k) base (stOff (word k)))

/-- Transpose each half of the state words, the words `32 h + k`, in place:
stages 16 and 8 on the words `i + 8 k` of each `i`, then 4, 2, 1 on the
words `8 g + k` of each `g`. -/
def transpose : List Instr :=
  movImm .r0 (swapMask 16) ++ movImm .r1 (swapMask 8) ++
  (List.range 2).flatMap (fun h => (List.range 8).flatMap fun i =>
    group 4 [(2, .r0), (1, .r1)] (fun k => 32 * h + i + 8 * k) 8) ++
  movImm .r0 (swapMask 4) ++ movImm .r1 (swapMask 2) ++ movImm .r2 (swapMask 1) ++
  (List.range 2).flatMap (fun h => (List.range 4).flatMap fun g =>
    group 8 [(4, .r0), (2, .r1), (1, .r2)] (fun k => 32 * h + 8 * g + k) 1)

/-! ## Batches -/

/-- The batch's blocks, `min(n, 32)`, into `r12`. -/
def batchCount : Prog isa :=
  .seq (.block [.mov .r12 (.shifted .r2 .lsr 5), .cmp .r12 (.imm 0)])
    (.ite .eq (.block [.mov .r12 (.reg .r2)]) (.block [.mov .r12 (.imm 32)]))

/-- The pointers of a copy: the state words, the data and the count. -/
def copyStart : List Instr :=
  [.dp .add .r4 base (.imm (BitVec.ofNat 32 (stOff 0))), .mov .r5 (.reg .r1), .mov .r6 (.reg .r12)]

/-- The next block, counted. -/
def copyNext : List Instr :=
  [.dp .add .r5 .r5 (.imm 8), .dp .add .r4 .r4 (.imm 4), .subs .r6 .r6 (.imm 1)]

/-- The batch's blocks into the state words: block `b`'s low word to word
`b`, its high word to word `32 + b`. -/
def copyIn : Prog isa :=
  .seq (.block copyStart)
    (.loop (.block ([.ldr .r7 .r5 0, .str .r7 .r4 0, .ldr .r7 .r5 4, .str .r7 .r4 128] ++ copyNext)) .ne)

/-- The state words back to the batch's blocks. -/
def copyOut : Prog isa :=
  .seq (.block copyStart)
    (.loop (.block ([.ldr .r7 .r4 0, .str .r7 .r5 0, .ldr .r7 .r4 128, .str .r7 .r5 4] ++ copyNext)) .ne)

/-- The arguments and the batch's count to the working space, and back. -/
def stash : List Instr :=
  [.str .r0 base schedOff, .str .r1 base dataOff, .str .r2 base nOff, .str .r12 base kOff]
def unstash : List Instr :=
  [.ldr .r0 base schedOff, .ldr .r1 base dataOff, .ldr .r2 base nOff, .ldr .r12 base kOff]

/-- Past the batch's blocks. -/
def advance : List Instr := [.dp .add .r1 .r1 (.shifted .r12 .lsl 3), .subs .r2 .r2 (.reg .r12)]

/-- One batch: the next `min(n, 32)` blocks into the state words, through
the three passes, and back; then the next blocks. -/
def batch (d : Direction) : Prog isa :=
  .seq batchCount (.seq copyIn (.seq (.block stash) (.seq (.block transpose) (.seq (passesCall d)
    (.seq (.block transpose) (.seq (.block unstash) (.seq copyOut (.block advance))))))))

/-! ## The function -/

def save : List Instr := saved.map fun p => .str p.1 base p.2
def restore : List Instr := saved.map fun p => .ldr p.1 base p.2

def ecb (d : Direction) : Prog isa :=
  .seq (.block [.cmp .r2 (.imm 0)])
    (.ite .eq (.block []) (.seq (.block save) (.seq (.loop (batch d) .ne) (.block restore))))

def encrypt : Prog isa := ecb .encrypt
def decrypt : Prog isa := ecb .decrypt

end VG.Impl.TripleDes.Arm.Bitslice
