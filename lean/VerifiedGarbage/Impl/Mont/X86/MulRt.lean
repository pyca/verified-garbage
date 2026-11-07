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

/-! ## The code

Everything public is in a register or computed from the arguments, which
are read-only: no public value goes through the working space. -/

/-- One word of a row, with the multiplier at `[edi + mo]`, both pointers up a
word, `esi` down 4; ZF when it reaches zero. -/
def mulStepAt (mo : Nat) : List Instr :=
  [.mov .eax (.mem (sc mo)), .mov .edx (.mem (at_ .ecx 0)), .mul .edx,
   .alu .add .eax (.mem (at_ .ebp 0)), .alu .adc .edx (.imm 0),
   .alu .add .eax (.reg .ebx), .alu .adc .edx (.imm 0),
   .store (at_ .ebp 0) .eax, .mov .ebx (.reg .edx),
   .alu .add .ecx (.imm 4), .alu .add .ebp (.imm 4), .alu .sub .esi (.imm 4)]

/-- The carry flag from the mask `ecx`. -/
def restore : List Instr := [.mov .edx (.imm 0), .alu .cmp .edx (.reg .ecx)]

end VG.Impl.Mont.X86.Rt

namespace VG.Impl.Mont.X86.Rt.Square
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Rt

/-! The low and high halves of each scalar product enter independent 64-bit sums.
The input square uses symmetry; Montgomery reduction scans the same columns. -/

end VG.Impl.Mont.X86.Rt.Square
