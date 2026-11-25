module

public import VerifiedGarbage.Impl.Aes.AArch64.Alloc
meta import VerifiedGarbage.Impl.Aes.AArch64.Alloc

/-!
# Bit slices on AArch64: registers, short forms, and the AES S-box

The registers of eight 64-bit slices (`q j`), the scratch buffer's base
(`sb`), short forms of the instructions on them and on slots of the buffer,
and the circuit `Circuit.sbox` on the slices (bit `j` of 64 bytes is in
`q j`), in place, spilling to slots of the scratch buffer: the code
`compile` allocates for it, written out (`#guard` checks that it is that) so
that the kernel need not run the allocator.
-/

@[expose] public section

namespace VG.Impl.Aes.AArch64

open VG.AArch64 VG.Impl.Aes.Circuit

/-- The slices. -/
def q : Nat → Reg
  | 0 => .x6 | 1 => .x7 | 2 => .x8 | 3 => .x9
  | 4 => .x10 | 5 => .x11 | 6 => .x12 | _ => .x13

/-- The scratch buffer's base. -/
def sb : Reg := .x5

/-- Temporaries. -/
def t0 : Reg := .x21
def t1 : Reg := .x22
def t2 : Reg := .x23
def u7 : Reg := .x24

/-- The address of a round key. -/
def kp : Reg := .x1

/-- All ones, while a circuit runs. -/
def ones : Reg := .x28

/-- The registers circuits may use besides the slices. -/
def sboxFree : List Reg :=
  [.x14, .x15, .x16, .x17, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27]

/-- The slots circuits may spill to. -/
def spillSlots : List Nat := List.range 48

def sboxIns : List (Nat × Reg) := (List.range 8).map fun i => (x i, q i)
def sboxOuts : List (Nat × Reg) := (List.range 8).map fun i => (s i, q i)

/-! Short forms. -/

def movR (d n : Reg) : Instr := .addImm .x d n 0
def eorR (d n m : Reg) : Instr := .logic .eor .x d n m
def andR (d n m : Reg) : Instr := .logic .and .x d n m
def orrR (d n m : Reg) : Instr := .logic .orr .x d n m
def rorI (d n : Reg) (k : Nat) : Instr := .ror .x d n k
def lsrI (d n : Reg) (k : Nat) : Instr := .lsr .x d n k
def stS (k : Nat) (r : Reg) : Instr := .str .x r sb (8 * k)
def ldS (r : Reg) (k : Nat) : Instr := .ldr .x r sb (8 * k)

/-- The S-box on the slices in `q 0 … q 7`, in place. -/
def sboxCode : List Instr := [
  .movz .x .x28 0 0, .subImm .x .x28 .x28 1, eorR .x8 .x11 .x8, eorR .x14 .x8 .x7,
  eorR .x15 .x14 .x12, eorR .x6 .x14 .x6, eorR .x9 .x15 .x9, eorR .x9 .x9 .x13,
  eorR .x16 .x9 .x8, eorR .x17 .x16 .x6, eorR .x11 .x17 .x11, eorR .x19 .x6 .x13,
  eorR .x20 .x17 .x10, eorR .x21 .x17 .x15, eorR .x22 .x11 .x13, eorR .x23 .x20 .x22,
  andR .x24 .x20 .x17, eorR .x25 .x16 .x10, eorR .x10 .x9 .x10, eorR .x9 .x20 .x9,
  andR .x26 .x22 .x15, andR .x27 .x25 .x9, eorR .x7 .x25 .x7, eorR .x26 .x27 .x26, stS 0 .x17,
  andR .x17 .x23 .x21, eorR .x27 .x27 .x17, eorR .x17 .x21 .x7, stS 1 .x20, eorR .x20 .x25 .x11,
  stS 2 .x25, andR .x25 .x19 .x7, stS 3 .x19, andR .x19 .x20 .x17, eorR .x25 .x27 .x25,
  eorR .x27 .x27 .x19, andR .x19 .x6 .x10, stS 4 .x7, andR .x7 .x13 .x14, eorR .x25 .x25 .x24,
  eorR .x27 .x27 .x19, eorR .x24 .x24 .x7, eorR .x19 .x26 .x19, eorR .x7 .x22 .x12,
  eorR .x25 .x25 .x8, eorR .x24 .x24 .x26, andR .x26 .x11 .x12, eorR .x24 .x24 .x7,
  eorR .x19 .x19 .x26, eorR .x26 .x11 .x14, eorR .x19 .x19 .x26, eorR .x27 .x27 .x16,
  eorR .x16 .x25 .x27, andR .x26 .x24 .x25, eorR .x7 .x27 .x26, eorR .x26 .x19 .x26,
  andR .x26 .x26 .x16, eorR .x24 .x24 .x19, eorR .x26 .x27 .x26, eorR .x25 .x25 .x26,
  andR .x13 .x26 .x13, eorR .x16 .x7 .x26, andR .x27 .x27 .x16, eorR .x25 .x27 .x25,
  andR .x22 .x25 .x22, eorR .x27 .x7 .x27, andR .x7 .x24 .x7, eorR .x19 .x19 .x7,
  andR .x15 .x25 .x15, andR .x27 .x19 .x27, eorR .x27 .x27 .x24, eorR .x24 .x19 .x27,
  andR .x20 .x24 .x20, eorR .x7 .x19 .x26, andR .x10 .x7 .x10, andR .x24 .x24 .x17,
  andR .x23 .x27 .x23, andR .x6 .x7 .x6, eorR .x6 .x6 .x20, andR .x21 .x27 .x21,
  eorR .x27 .x27 .x25, eorR .x7 .x7 .x27, eorR .x20 .x13 .x20, eorR .x25 .x26 .x25,
  andR .x26 .x26 .x14, eorR .x24 .x24 .x21, eorR .x10 .x24 .x10, andR .x9 .x7 .x9,
  eorR .x24 .x24 .x9, eorR .x24 .x24 .x26, eorR .x15 .x15 .x26, andR .x12 .x25 .x12,
  andR .x25 .x25 .x11, eorR .x24 .x24 .x12, ldS .x12 2, andR .x7 .x7 .x12, ldS .x12 4,
  andR .x12 .x19 .x12, eorR .x7 .x7 .x23, eorR .x21 .x21 .x12, ldS .x12 1, andR .x12 .x27 .x12,
  ldS .x11 3, andR .x19 .x19 .x11, eorR .x12 .x7 .x12, eorR .x21 .x21 .x15, eorR .x20 .x20 .x12,
  eorR .x12 .x12 .x19, eorR .x12 .x12 .x28, ldS .x11 0, andR .x27 .x27 .x11, eorR .x8 .x20 .x25,
  eorR .x24 .x24 .x27, eorR .x6 .x6 .x7, eorR .x6 .x6 .x21, eorR .x6 .x6 .x28,
  eorR .x11 .x21 .x12, eorR .x9 .x12 .x9, eorR .x9 .x9 .x28, eorR .x15 .x9 .x15,
  eorR .x9 .x9 .x8, eorR .x19 .x6 .x19, eorR .x19 .x19 .x28, eorR .x19 .x19 .x22,
  eorR .x9 .x9 .x10, eorR .x9 .x9 .x28, eorR .x15 .x15 .x27, eorR .x19 .x19 .x23,
  eorR .x10 .x19 .x13, movR .x7 .x12, stS 0 .x9, movR .x9 .x24, ldS .x12 0, movR .x13 .x15]

#guard sboxCode == compile sb sbox sboxIns sboxOuts sboxFree ones spillSlots

end VG.Impl.Aes.AArch64
