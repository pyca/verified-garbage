module

public import VerifiedGarbage.Impl.Aes.RISCV64.Sbox
public import VerifiedGarbage.Impl.Camellia.Circuit
import VerifiedGarbage.Impl.Aes.RISCV64.Alloc
meta import VerifiedGarbage.Impl.Aes.RISCV64.Alloc
public meta import VerifiedGarbage.Impl.Aes.RISCV64.Sbox
public meta import VerifiedGarbage.Impl.Camellia.Circuit

/-!
# The bitsliced Camellia S-box on RISC-V

The circuit `Circuit.sbox` (`SBOX1`) on the eight planes of the bitsliced
state in `q 0 … q 7` (`s0`–`s7`, `q j` holding bit `j` of 64 bytes), in
place: the code that the AES allocator (`Impl/Aes/RISCV64/Alloc.lean`)
produces for it with AES's temporaries (`t0`–`t6`, `a6`, `a7`, `s8`–`s11`),
spilling to the first slots of the scratch buffer at `a5` (it uses 0–9).
It is written out (and `#guard` checks that it is what `compile` produces)
so that the kernel, which evaluates the code in the proofs, does not have
to run the allocator.
-/

@[expose] public section

namespace VG.Impl.Camellia.RISCV64

open VG.RISCV64 VG.Impl.Aes.RISCV64

/-- The circuit's input `xᵢ` and output `sᵢ` are bit `7 - i`. -/
def sboxIns : List (Nat × Reg) := (List.range 8).map fun i => (Camellia.Circuit.x i, q (7 - i))
def sboxOuts : List (Nat × Reg) := (List.range 8).map fun i => (Camellia.Circuit.s i, q (7 - i))

/-- `SBOX1` on the state in `q 0 … q 7`, in place. -/
def sboxCode : List Instr := [
  xorR .t0 .s7 .s1, xorR .t1 .s5 .s3, xorR .t2 .s2 .t0, xorR .t3 .s6 .s0, xorR .t4 .s0 .t1, xorR
  .t5 .s4 .s1, xorR .t6 .s4 .t2, xorR .a6 .s6 .t1, xorR .a7 .s2 .t3, xorR .s8 .t2 .t3, xorR .s9
  .s7 .s6, xorR .s10 .s7 .t3, notR .s10, xorR .s11 .s6 .s3, stS 0 .s10, xorR .s10 .s5 .s1, stS 1
  .s7, xorR .s7 .s5 .s0, xorR .s5 .s5 .t2, xorR .t3 .s4 .t3, xorR .s4 .s4 .s9, xorR .s3 .s3 .s0,
  notR .s3, xorR .s0 .s2 .t4, xorR .s2 .s2 .t5, notR .s2, xorR .s9 .s1 .a6, notR .s9, stS 2 .s9,
  xorR .s9 .t0 .t4, xorR .t0 .t0 .a6, xorR .a6 .t1 .t5, stS 3 .s9, xorR .s9 .t1 .t6, xorR .t1 .t1
  .s8, stS 4 .t1, xorR .t1 .t2 .t4, notR .t1, xorR .t2 .t2 .s11, notR .t2, xorR .t4 .t4 .t5, notR
  .t4, xorR .s7 .t6 .s7, notR .s7, xorR .s10 .a7 .s10, notR .s10, xorR .a7 .a7 .a6, notR .a7, ldS
  .a6 1, xorR .t5 .a6 .s6, notR .t5, xorR .t5 .t5 .s6, xorR .a6 .a6 .s1, notR .a6, andR .s1 .s2
  .s4, andR .s6 .t5 .s10, xorR .s6 .s6 .s1, andR .s11 .t6 .s7, xorR .s11 .s11 .s1, andR .s1 .s0
  .t1, stS 1 .s0, andR .s0 .t0 .s5, xorR .s0 .s0 .s1, stS 5 .t0, andR .t0 .s8 .s3, xorR .t0 .t0
  .s1, andR .s1 .t3 .s9, stS 6 .t3, andR .t3 .t4 .a7, xorR .t3 .t3 .s1, stS 7 .t4, ldS .t4 2, stS
  8 .s8, ldS .s8 0, stS 9 .t6, andR .t6 .t4 .s8, xorR .t6 .t6 .s1, xorR .s6 .s6 .t3, xorR .s11
  .s11 .t6, xorR .s0 .s0 .t3, xorR .t0 .t0 .t6, ldS .t6 4, xorR .s6 .s6 .t6, ldS .t6 3, xorR .s11
  .s11 .t6, xorR .s0 .s0 .a6, xorR .t0 .t0 .t2, xorR .t2 .s6 .s11, andR .s6 .s6 .s0, xorR .a6 .t0
  .s6, andR .t6 .t2 .a6, xorR .t6 .t6 .s11, xorR .t3 .s0 .t0, xorR .s11 .s11 .s6, andR .s11 .s11
  .t3, xorR .s11 .s11 .t0, xorR .s0 .s0 .s11, xorR .t3 .a6 .s11, andR .t0 .t0 .t3, xorR .s0 .t0
  .s0, xorR .a6 .a6 .t0, andR .a6 .t6 .a6, xorR .t2 .t2 .a6, xorR .a6 .t2 .s0, xorR .t0 .t6 .s11,
  xorR .t3 .t6 .t2, xorR .s6 .s11 .s0, xorR .s1 .t0 .a6, andR .s4 .s6 .s4, andR .s10 .s0 .s10,
  andR .s7 .s11 .s7, andR .t1 .t3 .t1, andR .s5 .t2 .s5, andR .s3 .t6 .s3, andR .s9 .t0 .s9, andR
  .a7 .s1 .a7, andR .s8 .a6 .s8, andR .s6 .s6 .s2, andR .s0 .s0 .t5, ldS .t5 9, andR .s11 .s11
  .t5, ldS .t5 1, andR .t3 .t3 .t5, ldS .t5 5, andR .t2 .t2 .t5, ldS .t5 8, andR .t6 .t6 .t5, ldS
  .t5 6, andR .t0 .t0 .t5, ldS .t5 7, andR .s1 .s1 .t5, andR .a6 .a6 .t4, xorR .a7 .s10 .a7, xorR
  .t1 .t1 .s3, xorR .t4 .s9 .s8, xorR .t5 .s4 .s1, xorR .s11 .s11 .a7, xorR .s2 .t3 .t1, stS 2
  .t1, xorR .t1 .t0 .t4, xorR .t6 .s7 .t6, xorR .s9 .s9 .a6, xorR .s8 .s8 .s6, xorR .s6 .s6 .s0,
  xorR .t2 .t2 .s2, xorR .s1 .s1 .t1, stS 7 .s1, xorR .s1 .t5 .s11, xorR .s4 .s4 .s7, xorR .s10
  .s10 .s5, xorR .s3 .s3 .t5, xorR .s0 .s0 .s9, xorR .t3 .t3 .s11, xorR .t0 .t0 .a7, xorR .a6 .a6
  .s8, ldS .a7 2, xorR .a7 .a7 .s6, xorR .s4 .t4 .s4, xorR .s2 .s2 .t6, xorR .t1 .t1 .s6, xorR .t6
  .t6 .s8, xorR .s9 .s9 .t0, ldS .t0 7, xorR .s8 .t2 .t0, xorR .t2 .t2 .s1, xorR .s5 .t0 .a7, notR
  .s5, xorR .s1 .s1 .s0, notR .s1, xorR .s10 .s10 .s3, xorR .s3 .t3 .t6, notR .s3, xorR .a6 .a6
  .t2, notR .a6, xorR .s7 .s2 .s9, xorR .s6 .t1 .s10, notR .s6, movR .s2 .s1, movR .s1 .a6, movR
  .s0 .s8]

#guard sboxCode == compile sb Camellia.Circuit.sbox sboxIns sboxOuts sboxFree spillSlots

end VG.Impl.Camellia.RISCV64
