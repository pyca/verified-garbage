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
`s8`–`s11`) and `a0`, `a4` and `ra`, spilling to the slots of the
scratch buffer at `a5` (it uses 0–4). It is written out (and `#guard`
checks that it is what `compile` produces) so that the kernel, which
evaluates the code in the proofs, does not have to run the allocator.
-/

@[expose] public section

namespace VG.Impl.Sm4.RISCV64

open VG.RISCV64 VG.Impl.Aes.RISCV64

/-- The circuit's input `xᵢ` and output `sᵢ` are bit `7 - i`. -/
def sboxIns : List (Nat × Reg) := (List.range 8).map fun i => (Sm4.Circuit.x i, q (7 - i))
def sboxOuts : List (Nat × Reg) := (List.range 8).map fun i => (Sm4.Circuit.s i, q (7 - i))

/-- The registers the S-box may use: AES's, and `a0`, `a4` and `ra`, which
SM4's rounds set again or restore after them (`saveAux`). -/
def sboxFreeX : List Reg := sboxFree ++ [.a0, .a4, .ra]

/-- The S-box on the state in `q 0 … q 7`, in place. -/
def sboxCode : List Instr := [
  xorR .t0 .s4 .s2, xorR .t1 .s3 .s0, xorR .t2 .s1 .t1, xorR .t3 .s7 .t0, xorR .t4 .s5 .t2,
  xorR .t5 .s6 .s2, xorR .s4 .s7 .s4, xorR .t6 .s5 .t3, xorR .a6 .s6 .t6, xorR .a7 .s7 .s3,
  xorR .s8 .s6 .s4, xorR .s9 .s5 .t0, xorR .t6 .s1 .t6, notR .t6, xorR .s10 .t1 .t3,
  xorR .s11 .s0 .s8, xorR .s8 .t4 .s8, xorR .a0 .s1 .t5, xorR .s6 .s6 .s10, xorR .s0 .s0 .t3,
  notR .s0, xorR .s10 .s1 .a7, xorR .s3 .s3 .s9, notR .s3, xorR .s4 .t2 .s4, xorR .a4 .t0 .t4,
  xorR .ra .t4 .t5, xorR .s2 .s7 .s2, notR .s2, xorR .s11 .s1 .s11, notR .s11, xorR .t1 .t1 .s9,
  xorR .s5 .s5 .a7, notR .s5, xorR .a7 .s1 .a6, xorR .t0 .t0 .t2, notR .t0, xorR .s7 .s7 .t2,
  notR .s7, andR .t2 .a7 .t6, andR .s9 .t4 .s3, xorR .s9 .s9 .t2, stS 0 .t4, andR .t4 .s6 .s10,
  xorR .t4 .t4 .t2, andR .t2 .s1 .t1, stS 1 .s1, andR .s1 .t5 .s5, xorR .s1 .s1 .t2, stS 2 .t5,
  andR .t5 .a0 .s0, xorR .t5 .t5 .t2, andR .t2 .s4 .t0, stS 3 .s4, andR .s4 .a6 .s7,
  xorR .s4 .s4 .t2, stS 4 .a6, andR .a6 .ra .t3, xorR .a6 .a6 .t2, xorR .s9 .s9 .s4,
  xorR .t4 .t4 .a6, xorR .s1 .s1 .s4, xorR .t5 .t5 .a6, xorR .s9 .s9 .s2, xorR .t4 .t4 .s8,
  xorR .s1 .s1 .a4, xorR .t5 .t5 .s11, xorR .s11 .s9 .t4, andR .s9 .s9 .s1, xorR .a4 .t5 .s9,
  andR .s8 .s11 .a4, xorR .s8 .s8 .t4, xorR .s2 .s1 .t5, xorR .t4 .t4 .s9, andR .t4 .t4 .s2,
  xorR .t4 .t4 .t5, xorR .s1 .s1 .t4, xorR .s2 .a4 .t4, andR .t5 .t5 .s2, xorR .s1 .t5 .s1,
  xorR .a4 .a4 .t5, andR .a4 .s8 .a4, xorR .s11 .s11 .a4, xorR .a4 .s11 .s1, xorR .t5 .s8 .t4,
  xorR .s2 .s8 .s11, xorR .s9 .t4 .s1, xorR .a6 .t5 .a4, andR .t6 .s9 .t6, andR .s3 .s1 .s3,
  andR .s10 .t4 .s10, andR .t1 .s2 .t1, andR .s5 .s11 .s5, andR .s0 .s8 .s0, andR .t0 .t5 .t0,
  andR .s7 .a6 .s7, andR .t3 .a4 .t3, andR .s9 .s9 .a7, ldS .a7 0, andR .s1 .s1 .a7,
  andR .t4 .t4 .s6, ldS .s6 1, andR .s2 .s2 .s6, ldS .s6 2, andR .s11 .s11 .s6, andR .s8 .s8 .a0,
  ldS .a0 3, andR .t5 .t5 .a0, ldS .a0 4, andR .a6 .a6 .a0, andR .a4 .a4 .ra, xorR .s9 .s9 .t5,
  xorR .t0 .t0 .s1, xorR .s0 .t6 .s0, xorR .ra .s11 .t0, xorR .s8 .s8 .ra, xorR .t3 .s3 .t3,
  xorR .ra .s7 .s8, xorR .a4 .a4 .s9, xorR .a0 .s5 .s0, xorR .s6 .ra .a4, xorR .a7 .t4 .a0,
  xorR .s4 .a6 .t3, xorR .s9 .s9 .s4, xorR .s0 .t1 .s0, xorR .s0 .s9 .s0, xorR .t4 .t4 .a4,
  xorR .s11 .s11 .a6, xorR .s2 .s2 .t5, xorR .t0 .t0 .a0, xorR .t3 .t3 .a7, xorR .s8 .s8 .t3,
  notR .s8, xorR .s1 .s1 .s0, xorR .s10 .s10 .ra, xorR .s0 .s7 .s1, notR .s0, xorR .s7 .s11 .s2,
  notR .s7, xorR .t6 .t6 .s3, xorR .t1 .t1 .s6, xorR .s6 .s6 .t6, xorR .a7 .a7 .s10, notR .a7,
  xorR .s2 .s5 .t1, xorR .s4 .s9 .t0, notR .s4, stS 4 .s6, movR .s6 .a7, ldS .s5 4, movR .s3 .t4,
  movR .s1 .s8]

#guard sboxCode == compile sb Sm4.Circuit.sbox sboxIns sboxOuts sboxFreeX spillSlots

end VG.Impl.Sm4.RISCV64
