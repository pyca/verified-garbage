module

public import VerifiedGarbage.Impl.Aes.RISCV64.Sbox
public import VerifiedGarbage.Impl.Sm4.Circuit
import VerifiedGarbage.Impl.Aes.RISCV64.Alloc
meta import VerifiedGarbage.Impl.Aes.RISCV64.Alloc
public meta import VerifiedGarbage.Impl.Aes.RISCV64.Sbox
public meta import VerifiedGarbage.Impl.Sm4.Circuit

/-!
# The bitsliced SM4 S-box on RISC-V

The circuit `Circuit.sbox` (`Impl/Sm4/Circuit.lean`) on the eight planes of
the bitsliced state in `q 0 … q 7` (`q j` holding bit `j` of 64 bytes), in
place: the code that the AES allocator (`Impl/Aes/RISCV64/Alloc.lean`)
produces for it with AES's registers (temporaries `t0`–`t6`, `a6`, `a7` and
`s8`–`s11`), spilling to the slots of the scratch buffer at `a5` (it uses
0–8). It is written out (and `#guard` checks that it is what `compile`
produces) so that the kernel, which evaluates the code in the proofs, does
not have to run the allocator.
-/

@[expose] public section

namespace VG.Impl.Sm4.RISCV64

open VG.RISCV64 VG.Impl.Aes.RISCV64

/-- The circuit's input `xᵢ` and output `sᵢ` are bit `7 - i`. -/
def sboxIns : List (Nat × Reg) := (List.range 8).map fun i => (Sm4.Circuit.x i, q (7 - i))
def sboxOuts : List (Nat × Reg) := (List.range 8).map fun i => (Sm4.Circuit.s i, q (7 - i))

/-- The S-box on the state in `q 0 … q 7`, in place. -/
def sboxCode : List Instr := [
  xorR .t0 .s4 .s2, xorR .t1 .s3 .s0, xorR .t2 .s1 .t1, xorR .t3 .s7 .t0, xorR .t4 .s5 .t2, xorR .t5 .s6
  .s2, xorR .s4 .s7 .s4, xorR .t6 .s5 .t3, xorR .a6 .s6 .t6, xorR .a7 .s7 .s3, xorR .s8 .s6 .s4, xorR
  .s9 .s5 .t0, xorR .t6 .s1 .t6, notR .t6, xorR .s10 .t1 .t3, xorR .s11 .s0 .s8, xorR .s8 .t4 .s8, stS 0
  .s8, xorR .s8 .s1 .t5, xorR .s6 .s6 .s10, xorR .s0 .s0 .t3, notR .s0, xorR .s10 .s1 .a7, xorR .s3 .s3
  .s9, notR .s3, xorR .s4 .t2 .s4, stS 1 .t3, xorR .t3 .t0 .t4, stS 2 .t3, xorR .t3 .t4 .t5, xorR .s2
  .s7 .s2, notR .s2, xorR .s11 .s1 .s11, notR .s11, xorR .t1 .t1 .s9, xorR .s5 .s5 .a7, notR .s5, xorR
  .a7 .s1 .a6, xorR .t0 .t0 .t2, notR .t0, xorR .s7 .s7 .t2, notR .s7, andR .t2 .a7 .t6, andR .s9 .t4
  .s3, xorR .s9 .s9 .t2, stS 3 .t4, andR .t4 .s6 .s10, xorR .t4 .t4 .t2, andR .t2 .s1 .t1, stS 4 .s1,
  andR .s1 .t5 .s5, xorR .s1 .s1 .t2, stS 5 .t5, andR .t5 .s8 .s0, xorR .t5 .t5 .t2, andR .t2 .s4 .t0,
  stS 6 .s4, andR .s4 .a6 .s7, xorR .s4 .s4 .t2, stS 7 .a6, ldS .a6 1, stS 8 .s8, andR .s8 .t3 .a6, xorR
  .s8 .s8 .t2, xorR .s9 .s9 .s4, xorR .t4 .t4 .s8, xorR .s1 .s1 .s4, xorR .t5 .t5 .s8, xorR .s9 .s9 .s2,
  ldS .s2 0, xorR .t4 .t4 .s2, ldS .s2 2, xorR .s1 .s1 .s2, xorR .t5 .t5 .s11, xorR .s11 .s9 .t4, andR
  .s9 .s9 .s1, xorR .s2 .t5 .s9, andR .s8 .s11 .s2, xorR .s8 .s8 .t4, xorR .s4 .s1 .t5, xorR .t4 .t4
  .s9, andR .t4 .t4 .s4, xorR .t4 .t4 .t5, xorR .s1 .s1 .t4, xorR .s4 .s2 .t4, andR .t5 .t5 .s4, xorR
  .s1 .t5 .s1, xorR .s2 .s2 .t5, andR .s2 .s8 .s2, xorR .s11 .s11 .s2, xorR .s2 .s11 .s1, xorR .t5 .s8
  .t4, xorR .s4 .s8 .s11, xorR .s9 .t4 .s1, xorR .t2 .t5 .s2, andR .t6 .s9 .t6, andR .s3 .s1 .s3, andR
  .s10 .t4 .s10, andR .t1 .s4 .t1, andR .s5 .s11 .s5, andR .s0 .s8 .s0, andR .t0 .t5 .t0, andR .s7 .t2
  .s7, andR .a6 .s2 .a6, andR .s9 .s9 .a7, ldS .a7 3, andR .s1 .s1 .a7, andR .t4 .t4 .s6, ldS .s6 4,
  andR .s4 .s4 .s6, ldS .s6 5, andR .s11 .s11 .s6, ldS .s6 8, andR .s8 .s8 .s6, ldS .s6 6, andR .t5 .t5
  .s6, ldS .s6 7, andR .t2 .t2 .s6, andR .s2 .s2 .t3, xorR .s9 .s9 .t5, xorR .t0 .t0 .s1, xorR .s0 .t6
  .s0, xorR .t3 .s11 .t0, xorR .s8 .s8 .t3, xorR .a6 .s3 .a6, xorR .t3 .s7 .s8, xorR .s2 .s2 .s9, xorR
  .s6 .s5 .s0, xorR .a7 .t3 .s2, stS 7 .s5, xorR .s5 .t4 .s6, stS 6 .a7, xorR .a7 .t2 .a6, xorR .s9 .s9
  .a7, xorR .s0 .t1 .s0, xorR .s0 .s9 .s0, xorR .t4 .t4 .s2, xorR .s11 .s11 .t2, xorR .s4 .s4 .t5, xorR
  .t0 .t0 .s6, xorR .a6 .a6 .s5, xorR .s8 .s8 .a6, notR .s8, xorR .s1 .s1 .s0, xorR .s10 .s10 .t3, xorR
  .s0 .s7 .s1, notR .s0, xorR .s7 .s11 .s4, notR .s7, xorR .t6 .t6 .s3, ldS .s3 6, xorR .t1 .t1 .s3,
  xorR .s3 .s3 .t6, xorR .s6 .s5 .s10, notR .s6, ldS .s10 7, xorR .s2 .s10 .t1, xorR .s4 .s9 .t0, notR
  .s4, movR .s5 .s3, movR .s3 .t4, movR .s1 .s8]

#guard sboxCode == compile sb Sm4.Circuit.sbox sboxIns sboxOuts sboxFree spillSlots

end VG.Impl.Sm4.RISCV64
