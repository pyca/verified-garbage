module

public import VerifiedGarbage.Impl.Aes.Circuit
public import VerifiedGarbage.TCB.RISCV64.Isa
import VerifiedGarbage.Impl.Aes.RISCV64.Alloc
meta import VerifiedGarbage.Impl.Aes.RISCV64.Alloc
public meta import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# The bitsliced AES S-box on RISC-V

The circuit `Circuit.sbox` on the eight words of the bitsliced state
(`q j` holds bit `j` of 64 bytes: four blocks), in place, with the
temporaries in `t0`–`t6`, `a6`, `a7` and `s8`–`s11`, spilling to the first
slots of the scratch buffer at `a5`: the code that `compile` allocates for
it. It is written out (and `#guard` checks that it is what `compile`
produces) so that the kernel, which evaluates the code in the proofs, does
not have to run the allocator.
-/

@[expose] public section

namespace VG.Impl.Aes.RISCV64

open VG.RISCV64 VG.Impl.Aes.Circuit

/-- The registers of the bitsliced state: word `j` is in `q j`. -/
def q : Nat → Reg
  | 0 => .s0 | 1 => .s1 | 2 => .s2 | 3 => .s3
  | 4 => .s4 | 5 => .s5 | 6 => .s6 | _ => .s7

/-- The scratch buffer's base, a multiple of 8. -/
def sb : Reg := .a5

/-- The registers the S-box may use for its temporaries. -/
def sboxFree : List Reg := [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .a6, .a7, .s8, .s9, .s10, .s11]

/-- The slots the S-box may spill to. -/
def spillSlots : List Nat := List.range 40

/-- The circuit's input `xᵢ` and output `sᵢ` are bit `7 - i`. -/
def sboxIns : List (Nat × Reg) := (List.range 8).map fun i => (x i, q (7 - i))
def sboxOuts : List (Nat × Reg) := (List.range 8).map fun i => (s i, q (7 - i))

/-! Short forms of the instructions, on slots of `sb`. -/
def movR (d n : Reg) : Instr := .addi d n 0
def xorR (d n m : Reg) : Instr := .logic .xor d n m
def andR (d n m : Reg) : Instr := .logic .and d n m
def notR (d : Reg) : Instr := .logicImm .xor d d (-1)
def ldS (d : Reg) (k : Nat) : Instr := .load .d d sb (8 * k)
def stS (k : Nat) (r : Reg) : Instr := .store .d r sb (8 * k)

/-- The S-box on the state in `q 0 … q 7`, in place. -/
def sboxCode : List Instr := [
  xorR .t0 .s4 .s2, xorR .t1 .s7 .s1, xorR .t2 .s7 .s4, xorR .t3 .s7 .s2, xorR .s5 .s6 .s5,
  xorR .t4 .s5 .s0, xorR .s4 .t4 .s4, xorR .t5 .t1 .t0, xorR .t6 .t4 .s7, xorR .s1 .t4 .s1,
  xorR .a6 .s1 .t3, xorR .s3 .s3 .t5, xorR .s2 .s3 .s2, xorR .s3 .s3 .s6, xorR .s6 .s2 .s0,
  xorR .a7 .s2 .s5, xorR .s8 .s3 .t2, xorR .s9 .s0 .s8, xorR .s10 .a7 .s8, xorR .s11 .a7 .t3,
  xorR .s5 .s5 .s8, stS 0 .s11, xorR .s11 .t1 .s5, xorR .s7 .s7 .s5, stS 1 .s7, andR .s7 .t5 .s2,
  stS 2 .t5, andR .t5 .a6 .s6, xorR .t5 .t5 .s7, stS 3 .a6, andR .a6 .s4 .s0, xorR .a6 .a6 .s7,
  andR .s7 .t1 .s5, stS 4 .t1, andR .t1 .s1 .t4, xorR .t1 .t1 .s7, stS 5 .s1, andR .s1 .t6 .s9,
  xorR .s1 .s1 .s7, andR .s7 .t2 .s8, stS 6 .t2, andR .t2 .t0 .s10, xorR .t2 .t2 .s7, stS 7 .t0,
  andR .t0 .t3 .a7, xorR .t0 .t0 .s7, xorR .t5 .t5 .t2, xorR .a6 .a6 .t0, xorR .t1 .t1 .t2,
  xorR .s1 .s1 .t0, xorR .t5 .t5 .s3, ldS .s3 0, xorR .a6 .a6 .s3, xorR .t1 .t1 .s11, ldS .s11 1,
  xorR .s1 .s1 .s11, xorR .s11 .t5 .a6, andR .t5 .t5 .t1, xorR .s3 .s1 .t5, andR .t0 .s11 .s3,
  xorR .t0 .t0 .a6, xorR .t2 .t1 .s1, xorR .a6 .a6 .t5, andR .a6 .a6 .t2, xorR .a6 .a6 .s1,
  xorR .t1 .t1 .a6, xorR .t2 .s3 .a6, andR .s1 .s1 .t2, xorR .t1 .s1 .t1, xorR .s3 .s3 .s1,
  andR .s3 .t0 .s3, xorR .s11 .s11 .s3, xorR .s3 .s11 .t1, xorR .s1 .t0 .a6, xorR .t2 .t0 .s11,
  xorR .t5 .a6 .t1, xorR .s7 .s1 .s3, andR .s2 .t5 .s2, andR .s6 .t1 .s6, andR .s0 .a6 .s0,
  andR .s5 .t2 .s5, andR .t4 .s11 .t4, andR .s9 .t0 .s9, andR .s8 .s1 .s8, andR .s10 .s7 .s10,
  andR .a7 .s3 .a7, stS 1 .s6, ldS .s6 2, andR .t5 .t5 .s6, ldS .s6 3, andR .t1 .t1 .s6,
  andR .a6 .a6 .s4, ldS .s4 4, andR .t2 .t2 .s4, ldS .s4 5, andR .s11 .s11 .s4, andR .t0 .t0 .t6,
  ldS .t6 6, andR .s1 .s1 .t6, ldS .t6 7, andR .s7 .s7 .t6, andR .s3 .s3 .t3, xorR .s1 .s1 .s7,
  xorR .a6 .t1 .a6, xorR .s11 .s9 .s11, xorR .t5 .t5 .t1, xorR .t1 .s0 .t2, xorR .s0 .s0 .s9,
  xorR .a7 .s10 .a7, xorR .s2 .s2 .s5, xorR .s8 .s8 .s10, xorR .s7 .s7 .s3, xorR .t2 .t2 .s11,
  xorR .t1 .t1 .s2, xorR .s3 .t4 .s1, xorR .s5 .s5 .s8, xorR .s1 .s1 .t1, xorR .t0 .t0 .t1,
  xorR .a7 .a7 .s3, xorR .t5 .t5 .s3, xorR .t4 .t4 .s5, xorR .t0 .t0 .a7, ldS .s3 1,
  xorR .s3 .s3 .t5, xorR .s5 .s5 .t5, xorR .t2 .t2 .a7, notR .t2, xorR .s11 .s11 .s1, notR .s11,
  xorR .s1 .t4 .t0, xorR .s4 .s2 .s3, xorR .s3 .s0 .s3, xorR .s2 .a6 .t0, xorR .s6 .t4 .s4,
  notR .s6, xorR .s7 .s7 .s1, notR .s7, stS 1 .s7, movR .s7 .s5, ldS .s5 1, movR .s1 .t2,
  movR .s0 .s11]

#guard sboxCode == compile sb sbox sboxIns sboxOuts sboxFree spillSlots

end VG.Impl.Aes.RISCV64
