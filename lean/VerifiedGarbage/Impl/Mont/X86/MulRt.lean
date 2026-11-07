module

public import VerifiedGarbage.Impl.Mont.X86

/-! # Montgomery multiplication at a width given at run time (32-bit x86)

`vg_rsa_mont_mul_at` (`Proof/Rsa/MontMulContract.lean`) takes the width and every
offset as arguments, so its code depends on none of them: it reaches the
numbers through pointers, the working space's address plus an offset, which
move by a word, and each loop ends when a pointer reaches an end it keeps in
memory. `edi` holds the base of the function's own range (at the offset
`s`), whose first words hold the pointers' ends, the rows' multiplier, the
inverse and the length `8 n` of a number in bytes (`ctl*`), then the
callee-saved registers, then the accumulator of `2 N + 1` words
(`N = 2 n` 32-bit words) and the subtraction's temporary of `N` words.

Equal public input offsets select a symmetric column square: each off-diagonal
input product is computed once and doubled, with scalar multiplication and
SSE2 64-bit accumulators. Unequal offsets use coarsely
integrated operand scanning,
row `i` adding `a_i B` and then `q_i M` to the accumulator from word `i` on,
with `q_i` from `-M⁻¹`, and the conditional subtraction of `M` from the high
half, selected into the result by a mask. Every address is a pointer that
moves by a public step, and every branch depends only on public offsets or loop indices,
so the timing does not depend on the numbers.
-/

@[expose] public section

namespace VG.Impl.Mont.X86.Rt
open VG VG.X86 VG.Impl.Mont.X86

/-! ## The arguments and the function's own range -/

/-- The arguments on entry: `ws`, `ws_len`, `n`, then the offsets `m`, `inv`,
`s`, `o`, `a` and `b`. -/
def arg (i : Nat) : MemOp := at_ .esp (4 + 4 * i)

def argWs : MemOp := arg 0
def argN : MemOp := arg 2
def argM : MemOp := arg 3
def argInv : MemOp := arg 4
def argA : MemOp := arg 7
def argB : MemOp := arg 8

/-- The word of the function's own range holding a row's multiplier. -/
def multOff : Nat := 20

/-- The accumulator's offset in the function's range: `2 N + 1` words, then
the subtraction's temporary of `N` words. -/
def accOff : Nat := 52

/-! ## The code

Everything public is in a register or computed from the arguments, which
are read-only: no public value goes through the working space. -/

/-- `r = ws + ` the offset argument `x`, through `t`: both are loaded, as
the taint analysis knows a register loaded from an argument public, not the
sum of a register and an argument in memory. -/
def ptr (r : Reg) (x : MemOp) (t : Reg) : List Instr := [.mov r (.mem argWs), .mov t (.mem x), .alu .add r (.reg t)]

/-- `r = 8 n` (the bytes of a number), times `2 ^ k` more. -/
def lenTimes (r : Reg) (k : Nat) : List Instr :=
  .mov r (.mem argN) :: List.replicate (3 + k) (.alu .add r (.reg r))

/-- `[ebp + d] += [edi + mo] · [ecx + d]` with the carry `ebx`. -/
def macAt (mo d : Nat) : List Instr :=
  [.mov .eax (.mem (sc mo)), .mov .edx (.mem (at_ .ecx d)), .mul .edx,
   .alu .add .eax (.mem (at_ .ebp d)), .alu .adc .edx (.imm 0),
   .alu .add .eax (.reg .ebx), .alu .adc .edx (.imm 0),
   .store (at_ .ebp d) .eax, .mov .ebx (.reg .edx)]

/-- One step of a row, two words: `[ebp] += [multOff] · [ecx]` and the same a
word up, with the carry `ebx`, both pointers up two words, `esi` down 8; ZF
when it reaches zero. A row has `N = 2 n` words, an even number. -/
def pairStep : List Instr :=
  macAt multOff 0 ++ macAt multOff 4 ++ [.alu .add .ecx (.imm 8), .alu .add .ebp (.imm 8), .alu .sub .esi (.imm 8)]

/-- One word of a row, with the multiplier at `[edi + mo]`, both pointers up a
word, `esi` down 4; ZF when it reaches zero. -/
def mulStepAt (mo : Nat) : List Instr :=
  [.mov .eax (.mem (sc mo)), .mov .edx (.mem (at_ .ecx 0)), .mul .edx,
   .alu .add .eax (.mem (at_ .ebp 0)), .alu .adc .edx (.imm 0),
   .alu .add .eax (.reg .ebx), .alu .adc .edx (.imm 0),
   .store (at_ .ebp 0) .eax, .mov .ebx (.reg .edx),
   .alu .add .ecx (.imm 4), .alu .add .ebp (.imm 4), .alu .sub .esi (.imm 4)]

/-- The carry `ebx` into the two words at `ebp`. -/
def carryWords : List Instr :=
  [.mov .eax (.mem (at_ .ebp 0)), .alu .add .eax (.reg .ebx), .store (at_ .ebp 0) .eax,
   .mov .eax (.mem (at_ .ebp 4)), .alu .adc .eax (.imm 0), .store (at_ .ebp 4) .eax]

/-- The carry, and `ebp` back to the row's start. -/
def carryUp : List Instr := carryWords ++ lenTimes .eax 0 ++ [.alu .sub .ebp (.reg .eax)]

/-- The window at `ebp` `+= [multOff] ·` the number at the offset argument `x`. -/
def mulRow (x : MemOp) : Prog isa :=
  .seq (.block ([.mov .ebx (.imm 0)] ++ ptr .ecx x .edx ++ lenTimes .esi 0)) <|
  .seq (.loop (.block pairStep) .ne) (.block carryUp)

/-- `a_i` into `multOff`: at `ws + a + 4 i`, for `ebp` at word `i` of the accumulator. -/
def loadA : List Instr :=
  [.mov .eax (.reg .ebp), .alu .sub .eax (.reg .edi), .alu .sub .eax (.imm (BitVec.ofNat 32 accOff)),
   .mov .edx (.mem argWs), .alu .add .eax (.reg .edx), .mov .edx (.mem argA), .alu .add .eax (.reg .edx),
   .mov .eax (.mem (at_ .eax 0)), .store (sc multOff) .eax]

/-- `q = [ebp] · -M⁻¹ mod 2³²` into `multOff`. -/
def redDigit : List Instr :=
  ptr .edx argInv .eax ++
    [.mov .edx (.mem (at_ .edx 0)), .mov .eax (.mem (at_ .ebp 0)), .mul .edx, .store (sc multOff) .eax]

/-- `ebp` up a word; ZF at the end of the rows, `8 n` bytes past the accumulator. -/
def rowEnd : List Instr :=
  [.alu .add .ebp (.imm 4)] ++ lenTimes .eax 0 ++
    [.alu .add .eax (.reg .edi), .alu .add .eax (.imm (BitVec.ofNat 32 accOff)), .alu .cmp .ebp (.reg .eax)]

/-- A row: `a_i B`, then `q M`, into the accumulator from word `i`. -/
def row : Prog isa :=
  .seq (.block loadA) <|
  .seq (mulRow argB) <|
  .seq (.block redDigit) <|
  .seq (mulRow argM) (.block rowEnd)

/-- The carry flag from the mask `ecx`. -/
def restore : List Instr := [.mov .edx (.imm 0), .alu .cmp .edx (.reg .ecx)]

end VG.Impl.Mont.X86.Rt

namespace VG.Impl.Mont.X86.Rt.Square
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Rt

/-! The low and high halves of each scalar product enter independent 64-bit sums.
The input square uses symmetry; Montgomery reduction scans the same columns. -/

end VG.Impl.Mont.X86.Rt.Square
