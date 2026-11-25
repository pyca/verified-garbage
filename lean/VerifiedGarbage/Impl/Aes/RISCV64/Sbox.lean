module

public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# The bitsliced AES S-boxes on RISC-V

The registers of eight bit slices (`q j` holds bit `j` of 64 bytes), short
forms of the instructions on them and on slots of the scratch buffer, and
the S-boxes as circuits on the slices, in place. `sbox0Code` is
`Circuit.sbox` without its constant, and `invSbox0Code` the inverse S-box's
circuit (113 gates) of an input with `{63}` added; both are ordered so that
they need few spills with three-operand instructions in 21 registers (eight
spills and reloads each, to slots 0–3 of the scratch buffer), and the last
gate of every output goes to its own register.
-/

@[expose] public section

namespace VG.Impl.Aes.RISCV64

open VG.RISCV64

/-- The slices: bit `j` is in `q j`. -/
def q : Nat → Reg
  | 0 => .s0 | 1 => .s1 | 2 => .s2 | 3 => .s3
  | 4 => .s4 | 5 => .s5 | 6 => .s6 | _ => .s7

/-- Temporaries. -/
def t0 : Reg := .t0
def t1 : Reg := .t1
def t2 : Reg := .t2

/-- The scratch buffer's base, and the round key. -/
def sb : Reg := .a5
def kp : Reg := .a1

/-- The registers free in a circuit on the slices, and the slots it may spill to. -/
def sboxFree : List Reg :=
  [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .a6, .a7, .s8, .s9, .s10, .s11]
def spillSlots : List Nat := List.range 40

/-! Short forms, on registers and slots of `sb`. -/

def movR (d n : Reg) : Instr := .addi d n 0
def xorR (d n m : Reg) : Instr := .logic .xor d n m
def andR (d n m : Reg) : Instr := .logic .and d n m
def notR (d : Reg) : Instr := .logicImm .xor d d (-1)
def ldS (d : Reg) (k : Nat) : Instr := .load .d d sb (8 * k)
def stS (k : Nat) (r : Reg) : Instr := .store .d r sb (8 * k)
def shrI (d n : Reg) (k : Nat) : Instr := .shift .srl .d d n k
def shlI (d n : Reg) (k : Nat) : Instr := .shift .sll .d d n k

/-- The S-box without its constant. -/
def sbox0Code : List Instr := [
  xorR .s11 .s5 .s2, xorR .t0 .s11 .s1, xorR .s8 .t0 .s6, xorR .t5 .s8 .s3, xorR .a6 .t5 .s7,
  xorR .t4 .t0 .s0, xorR .a7 .a6 .s11, xorR .t1 .a7 .t4, xorR .t6 .t1 .s5, xorR .s5 .t6 .s7,
  xorR .s9 .t1 .s8, xorR .t2 .t1 .s4, andR .s0 .t2 .t1, xorR .t5 .t2 .s5, xorR .s10 .t2 .a6,
  xorR .t3 .a6 .s4, andR .s3 .s5 .s8, andR .a6 .t5 .s9, xorR .s2 .s5 .s6, xorR .s4 .a7 .s4,
  stS 0 .t1, andR .t1 .s4 .s10, xorR .a6 .t1 .a6, stS 1 .t2, andR .t2 .s7 .t0, xorR .t1 .t1 .s3,
  xorR .t2 .s0 .t2, xorR .t2 .t2 .t1, xorR .s3 .t4 .s7, xorR .s1 .s4 .s1, xorR .s2 .t2 .s2,
  andR .t2 .t4 .t3, xorR .t1 .t1 .t2, stS 2 .s10, andR .s10 .s3 .s1, xorR .s10 .a6 .s10,
  xorR .s10 .s10 .s0, xorR .s10 .s10 .s11, andR .s11 .t6 .s6, xorR .s0 .t6 .t0, xorR .t1 .t1 .s11,
  xorR .s11 .t1 .s0, xorR .t1 .s4 .t6, xorR .s0 .s9 .s1, stS 3 .s6, andR .s6 .t1 .s0,
  xorR .a6 .a6 .s6, xorR .t2 .a6 .t2, andR .a6 .s2 .s10, xorR .s6 .t2 .a7, xorR .a7 .s11 .a6,
  xorR .a6 .s6 .a6, xorR .t2 .s10 .s6, andR .a7 .a7 .t2, xorR .t2 .s2 .s11, xorR .a7 .s6 .a7,
  xorR .s10 .s10 .a7, xorR .s2 .a6 .a7, andR .s2 .s6 .s2, xorR .s6 .s2 .s10, andR .t0 .a7 .t0,
  xorR .s10 .a6 .s2, andR .a6 .t2 .a6, xorR .a6 .s11 .a6, andR .s11 .a6 .s10, xorR .s10 .s11 .t2,
  andR .t5 .s10 .t5, andR .s11 .a7 .s7, xorR .t2 .a6 .s10, andR .s0 .t2 .s0, andR .s1 .a6 .s1,
  andR .s2 .a6 .s3, andR .s9 .s10 .s9, xorR .s7 .a6 .a7, xorR .a6 .s0 .s9, andR .t1 .t2 .t1,
  xorR .s9 .s9 .s1, andR .t2 .s7 .t3, xorR .s3 .a7 .s6, xorR .s10 .s10 .s6, andR .a7 .s7 .t4,
  andR .t3 .s6 .s8, xorR .s8 .t3 .t0, xorR .t4 .a7 .t1, xorR .t3 .a6 .t2, xorR .t2 .s7 .s10,
  andR .a7 .s6 .s5, ldS .s6 2, andR .s6 .t2 .s6, xorR .t1 .s11 .t1, andR .s0 .t2 .s4,
  xorR .t2 .a6 .s6, ldS .s5 1, andR .a6 .s10 .s5, xorR .s9 .s9 .s8, xorR .s7 .s0 .t5,
  xorR .a6 .s7 .a6, xorR .t4 .t4 .s7, xorR .s0 .t4 .s9, xorR .t1 .t1 .a6, xorR .s1 .a6 .s2,
  xorR .a6 .s0 .s2, xorR .t0 .t2 .t0, andR .t6 .s3 .t6, xorR .t4 .s1 .s6, xorR .t2 .a6 .a7,
  xorR .s5 .s9 .s1, ldS .a7 3, andR .s9 .s3 .a7, xorR .a7 .t2 .t5, xorR .s8 .t4 .s8,
  xorR .a6 .t0 .s9, ldS .t2 0, andR .s9 .s10 .t2, xorR .s7 .s8 .s9, xorR .s4 .a7 .s11,
  xorR .s2 .t1 .t6, xorR .t1 .t4 .s2, xorR .s3 .a6 .s9, xorR .s6 .t1 .t3]

/-- `{63}` added to the slices. -/
def add63 : List Instr := [notR (q 0), notR (q 1), notR (q 5), notR (q 6)]

/-- The S-box. -/
def sboxCode : List Instr := sbox0Code ++ add63

/-- The inverse S-box of an input with `{63}` added. -/
def invSbox0Code : List Instr := [
  xorR .t0 .s5 .s4, xorR .t6 .t0 .s1, xorR .s1 .t6 .s6, xorR .t5 .s1 .s5, xorR .t4 .t6 .s3,
  xorR .t3 .s7 .s6, xorR .s6 .t4 .t5, xorR .s9 .s4 .s2, xorR .a7 .s9 .s0, xorR .t1 .s6 .s7,
  xorR .s5 .t3 .s0, xorR .s8 .s1 .s5, andR .s11 .t5 .s5, andR .s0 .t4 .s1, xorR .t2 .s5 .s4,
  andR .a6 .s6 .s8, xorR .s10 .t4 .t2, xorR .s3 .t6 .s2, andR .s4 .s10 .t1, xorR .a6 .a6 .s0,
  xorR .s11 .s11 .s0, xorR .s4 .a6 .s4, xorR .t3 .t3 .a7, xorR .s7 .s3 .s7, xorR .s0 .s7 .s10,
  stS 0 .s8, andR .s8 .s0 .t3, xorR .s4 .s4 .s8, stS 1 .s6, xorR .s6 .t1 .s1, xorR .s8 .s11 .s8,
  stS 2 .s5, xorR .s5 .t1 .t3, stS 3 .s1, andR .s1 .s7 .s5, xorR .s8 .s8 .s1, xorR .s1 .s6 .s9,
  xorR .s4 .s4 .s3, xorR .s3 .t1 .s3, xorR .s8 .s8 .s2, andR .s2 .s3 .s1, xorR .s11 .s11 .s2,
  xorR .s2 .s5 .t6, andR .t6 .s2 .s9, xorR .s11 .s11 .t6, xorR .a6 .a6 .t6, andR .t6 .t2 .s6,
  xorR .t6 .a6 .t6, xorR .s11 .s11 .a7, xorR .t0 .t6 .t0, andR .a6 .s11 .s8, xorR .a7 .s8 .s4,
  xorR .t6 .t0 .a6, xorR .s11 .s11 .t0, andR .a7 .t6 .a7, xorR .t6 .s4 .a6, xorR .a6 .s4 .a7,
  xorR .a7 .s8 .a6, xorR .s8 .t6 .a6, andR .s8 .s4 .s8, andR .s4 .a6 .s2, xorR .a7 .s8 .a7,
  xorR .s2 .a7 .a6, xorR .s8 .t6 .s8, andR .s6 .a7 .s6, andR .t6 .s11 .t6, andR .t2 .a7 .t2,
  xorR .t6 .t0 .t6, andR .t0 .s2 .s1, andR .s8 .t6 .s8, andR .t3 .t6 .t3, xorR .s8 .s8 .s11,
  andR .s11 .a6 .s9, andR .s10 .s8 .s10, andR .s9 .s2 .s3, xorR .a6 .a6 .t6, xorR .a7 .a7 .s8,
  andR .s2 .s8 .t1, xorR .t1 .s8 .t6, andR .s8 .t1 .s5, andR .s1 .t6 .s0, andR .t6 .t1 .s7,
  andR .t5 .a6 .t5, xorR .t5 .t5 .s9, xorR .t1 .t3 .s6, xorR .s9 .s9 .t2, xorR .s11 .s11 .s10,
  xorR .s11 .s11 .t1, xorR .t1 .s9 .t6, andR .t6 .a7 .t4, xorR .t5 .t5 .t6, xorR .t4 .s11 .s2,
  xorR .s5 .t4 .s1, xorR .s3 .t5 .s4, ldS .s11 3, andR .s9 .a7 .s11, xorR .a7 .a7 .a6,
  xorR .t2 .s5 .t2, xorR .s11 .t1 .s10, xorR .s0 .t2 .s4, xorR .t2 .s9 .s8, ldS .t5 2,
  andR .a6 .a6 .t5, xorR .s10 .s0 .a6, ldS .s9 1, andR .t5 .a7 .s9, xorR .s9 .t5 .t6, ldS .a6 0,
  andR .a6 .a7 .a6, xorR .s5 .s9 .s5, xorR .a6 .s10 .a6, xorR .t5 .s3 .t0, xorR .a7 .s10 .t3,
  xorR .t3 .a7 .t2, xorR .t6 .a6 .s6, xorR .s9 .a6 .s2, xorR .s2 .t1 .t4, xorR .s7 .s11 .t3,
  xorR .s6 .t6 .t5, xorR .s4 .s9 .s8, xorR .s1 .t3 .s6]

end VG.Impl.Aes.RISCV64
