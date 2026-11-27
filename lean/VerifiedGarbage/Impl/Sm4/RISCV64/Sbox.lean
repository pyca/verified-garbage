module

public import VerifiedGarbage.Impl.Aes.RISCV64.Sbox

/-!
# The bitsliced SM4 S-box on RISC-V

On the eight planes of the bitsliced state in `q 0 … q 7` (`q j` holding bit
`j` of 64 bytes), in place, with AES's registers (temporaries `t0`–`t6`,
`a6`, `a7` and `s8`–`s11`), spilling to the slots of the scratch buffer at
`a5` (it uses 0–3).

The circuit is `Circuit.sbox` (`Impl/Sm4/Circuit.lean`) with its linear
layers replaced: as `z⁻¹ = (c · (c · z^(2ᵏ))⁻¹)^(2⁻ᵏ)`, the inversion in its
middle may be conjugated by any of the 2040 maps `z ↦ c · z^(2ᵏ)` of SM4's
field. For the map whose layers are smallest (`c = d1`, `k = 1`), found with
Boyar and Peralta's heuristic, the circuit has 110 gates (124 with
`Circuit.sbox`), and six complements, placed where there are fewest (11).
Its order was searched for the fewest spills. The proofs check the code on
all 256 inputs.
-/

@[expose] public section

namespace VG.Impl.Sm4.RISCV64

open VG.RISCV64 VG.Impl.Aes.RISCV64

/-- The S-box on the state in `q 0 … q 7`, in place. -/
def sboxCode : List Instr := [
  notR .s2, notR .s6, xorR .t0 .s2 .s6, notR .s5, xorR .s3 .s3 .s5, xorR .t1 .s0 .s3, notR .t1, xorR
  .s7 .s7 .t0, xorR .t2 .s7 .s3, xorR .t3 .s6 .s3, xorR .t4 .s6 .t2, xorR .s0 .s0 .s4, xorR .s0 .s6
  .s0, xorR .s5 .s5 .s0, xorR .s4 .s5 .t4, andR .t5 .s4 .t4, xorR .t6 .s1 .t0, xorR .a6 .s1 .t1,
  andR .a7 .a6 .t3, xorR .t5 .t5 .a7, xorR .s8 .t0 .s4, xorR .s9 .t6 .s0, xorR .s3 .s9 .s3, andR
  .s10 .t6 .s9, xorR .s11 .s7 .s9, stS 0 .t0, andR .t0 .t0 .s6, xorR .s10 .s10 .t0, xorR .t5 .t5
  .s10, stS 1 .s6, xorR .s6 .s6 .s9, stS 2 .s1, andR .s1 .s1 .s6, xorR .s1 .s1 .t0, xorR .t5 .t5
  .s5, xorR .s5 .t1 .s8, andR .t0 .s8 .t2, stS 3 .s6, andR .s6 .t1 .s3, xorR .t0 .t0 .s6, xorR .t0
  .t0 .s10, xorR .s10 .t6 .s5, xorR .t0 .t0 .s0, andR .s0 .s10 .s7, xorR .s0 .s0 .a7, andR .a7 .s5
  .s11, xorR .a7 .a7 .s6, xorR .a7 .a7 .s1, xorR .s0 .s0 .s1, xorR .a7 .a7 .s2, xorR .s1 .a6 .t3,
  xorR .s0 .s0 .s1, andR .s1 .a7 .s0, xorR .a7 .a7 .t0, xorR .s2 .t0 .s1, xorR .s6 .s0 .t5, andR .s2
  .s2 .s6, xorR .s2 .s2 .t5, xorR .s0 .s0 .s2, xorR .s1 .t5 .s1, xorR .s6 .s1 .s2, andR .t2 .s2 .t2,
  andR .t5 .t5 .s6, xorR .s0 .t5 .s0, xorR .t5 .s1 .t5, andR .s8 .s2 .s8, andR .s1 .a7 .s1, xorR .s1
  .s1 .t0, andR .s4 .s1 .s4, andR .t5 .s1 .t5, xorR .a7 .a7 .t5, xorR .s6 .s1 .a7, xorR .t0 .a7 .s0,
  andR .s11 .s0 .s11, xorR .t5 .s2 .s0, andR .s7 .a7 .s7, andR .t6 .t0 .t6, andR .s9 .t0 .s9, andR
  .t3 .s6 .t3, andR .t1 .t5 .t1, andR .s0 .s0 .s5, andR .t5 .t5 .s3, andR .s6 .s6 .a6, andR .t4 .s1
  .t4, xorR .s1 .s1 .s2, xorR .s6 .s6 .s4, ldS .s2 1, andR .s2 .s1 .s2, xorR .t5 .t5 .t2, xorR .s2
  .s2 .s9, andR .a7 .a7 .s10, xorR .t0 .s1 .t0, ldS .s3 3, andR .s3 .t0 .s3, xorR .s11 .s11 .t2,
  xorR .t3 .t3 .t5, notR .s3, ldS .s5 2, andR .t0 .t0 .s5, xorR .a7 .a7 .s4, xorR .s3 .s3 .s9, xorR
  .s11 .s11 .s3, xorR .s7 .s7 .t3, xorR .s7 .s7 .s3, xorR .s2 .s2 .t5, xorR .a7 .a7 .s7, xorR .t4
  .t4 .t3, xorR .t1 .t1 .s6, xorR .t0 .t0 .a7, xorR .t0 .t0 .t6, ldS .s3 0, andR .s1 .s1 .s3, xorR
  .s0 .s0 .a7, xorR .s2 .s2 .s0, xorR .s1 .s1 .s6, xorR .s3 .s1 .t6, xorR .s4 .s8 .s0, xorR .s0 .s2
  .t1, xorR .s1 .s7 .s3, xorR .s2 .t0 .s0, xorR .s5 .s11 .s4, xorR .s8 .s8 .t1, .logicImm .xor .s7
  .s8 (-1), xorR .s6 .t4 .t0]

end VG.Impl.Sm4.RISCV64
