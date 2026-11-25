module

public import VerifiedGarbage.Impl.Aes.Circuit
public import VerifiedGarbage.TCB.Arm.Isa

/-!
# The bitsliced AES S-box on ARMv7

The registers of eight bit slices, short forms of the instructions on them
and on slots of the scratch buffer, and the S-box's circuit and its inverse's
on the slices (slice `j` holds bit `j` of 32 bytes), from `q 0 … q 7` to
`p 0 … p 7`, the registers MixColumns takes them from.

The circuits are `Circuit.sbox`, less its constant, and a circuit of the
inverse made the same way (113 gates). The code computes one gate an
instruction, in an order found by a search for one with few spills: with the
13 registers there are besides the scratch buffer's base, 13 loads and 12
stores, in slots 0–11. The proofs check it on all 256 inputs.
-/

@[expose] public section

namespace VG.Impl.Aes.Arm

open VG.Arm

/-! ## Registers -/

/-- The slices before SubBytes: bit `j` is in `q j`. -/
def q : Nat → Reg
  | 0 => .r0 | 1 => .r1 | 2 => .r2 | 3 => .r3 | 4 => .r4 | 5 => .r5 | 6 => .r6 | _ => .r7

/-- The slices after SubBytes: bit `j` is in `p j`. -/
def p : Nat → Reg
  | 0 => .r1 | 1 => .r2 | 2 => .r3 | 3 => .r4 | 4 => .r5 | 5 => .r6 | 6 => .r7 | _ => .lr

/-- The scratch buffer's base. -/
def sb : Reg := .r8

/-- The round keys' pointer, between the layers that use the register. -/
def kp : Reg := .r9

def t0 : Reg := .r10
def t1 : Reg := .r11
def t2 : Reg := .r12
/-- `t2`, as the other ciphers' layers call it. -/
def u7 : Reg := .r12

/-! ## Short forms -/

def movR (d s : Reg) : Instr := .mov d (.reg s)
def eorR (d n m : Reg) : Instr := .dp .eor d n (.reg m)
def andR (d n m : Reg) : Instr := .dp .and d n (.reg m)
def rorOp (r : Reg) (n : Nat) : Op2 := .shifted r .ror n
def lsrOp (r : Reg) (n : Nat) : Op2 := .shifted r .lsr n
/-- Slot `k` of the scratch buffer. -/
def ldS (t : Reg) (k : Nat) : Instr := .ldr t sb (4 * k)
def stS (k : Nat) (t : Reg) : Instr := .str t sb (4 * k)
/-- A 32-bit constant. -/
def imm32 (d : Reg) (v : BitVec 32) : List Instr :=
  [.movw d (v.extractLsb' 0 16), .movt d (v.extractLsb' 16 16)]

/-! ## The S-boxes -/

/-- The S-box with `{63}` added to its output, from `q j` to `p j`. -/
def subBytes : List Instr := [
  eorR .r2 .r5 .r2, eorR .lr .r2 .r1, eorR .r10 .lr .r6, eorR .r3 .r10 .r3, eorR .r3 .r3 .r7,
  eorR .r12 .r3 .r2, eorR .r9 .lr .r0, eorR .r0 .r12 .r4, eorR .r1 .r0 .r1, eorR .r11 .r9 .r7,
  stS 0 .r0, andR .r0 .r11 .r1, eorR .r2 .r2 .r0, eorR .r0 .r3 .r4, stS 1 .r11, andR .r11 .r9 .r0,
  stS 2 .r0, eorR .r0 .r11 .r12, eorR .r12 .r12 .r9, eorR .r11 .lr .r11, eorR .r4 .r12 .r4,
  eorR .r5 .r12 .r5, stS 3 .r9, andR .r9 .r7 .lr, stS 4 .lr, eorR .lr .r5 .r7, stS 5 .r7,
  andR .r7 .r4 .r12, eorR .r2 .r2 .r7, eorR .r11 .r11 .r5, eorR .r3 .r4 .r3, eorR .r7 .r7 .r9,
  eorR .r9 .r4 .lr, stS 6 .r4, andR .r4 .r5 .r6, eorR .r7 .r7 .r6, eorR .r4 .r11 .r4,
  eorR .r11 .r12 .r10, stS 7 .r12, ldS .r12 0, stS 8 .r6, andR .r6 .r12 .r3, stS 9 .r3,
  andR .r3 .lr .r10, stS 10 .r10, eorR .r10 .r12 .r5, eorR .r12 .r11 .r1, stS 11 .r1,
  andR .r1 .r9 .r11, eorR .r1 .r6 .r1, eorR .r6 .r6 .r3, andR .r3 .r10 .r12, eorR .r4 .r4 .r6,
  eorR .r2 .r2 .r1, eorR .r6 .r6 .lr, eorR .r6 .r6 .r7, andR .r7 .r6 .r2, eorR .r1 .r1 .r0,
  eorR .r3 .r1 .r3, eorR .r1 .r3 .r7, eorR .r7 .r4 .r7, eorR .r0 .r2 .r3, andR .r7 .r7 .r0,
  eorR .r7 .r3 .r7, eorR .r6 .r6 .r4, eorR .r0 .r1 .r7, andR .r3 .r3 .r0, eorR .r0 .r1 .r3,
  andR .r1 .r6 .r1, eorR .r1 .r4 .r1, andR .r4 .r1 .r0, eorR .r4 .r4 .r6, eorR .r6 .r1 .r4,
  eorR .r3 .r3 .r2, eorR .r3 .r3 .r7, andR .r2 .r6 .r12, ldS .r0 10, andR .r12 .r3 .r0,
  eorR .r0 .r4 .r3, andR .r11 .r4 .r11, andR .r6 .r6 .r10, eorR .r2 .r2 .r11, andR .r4 .r4 .r9,
  eorR .r9 .r7 .r3, ldS .r10 8, andR .r10 .r9 .r10, andR .lr .r3 .lr, andR .r3 .r9 .r5, ldS .r5 4,
  andR .r5 .r7 .r5, ldS .r9 5, andR .r9 .r7 .r9, eorR .r12 .r12 .r5, eorR .r10 .r10 .r2,
  eorR .r5 .r10 .r5, eorR .lr .lr .r9, ldS .r10 11, andR .r10 .r1 .r10, eorR .r7 .r1 .r7,
  eorR .r9 .r6 .r9, eorR .lr .lr .r4, eorR .r3 .r9 .r3, eorR .r10 .r10 .r11, eorR .r9 .r7 .r0,
  eorR .r11 .r10 .r12, ldS .r10 2, andR .r10 .r7 .r10, eorR .r10 .r10 .r2, ldS .r2 0,
  andR .r2 .r9 .r2, eorR .r4 .r2 .r4, ldS .r2 3, andR .r7 .r7 .r2, ldS .r2 1, andR .r2 .r1 .r2,
  ldS .r1 9, andR .r9 .r9 .r1, eorR .r1 .r11 .r4, eorR .r1 .r7 .r1, eorR .r1 .r1 .r6, ldS .r6 6,
  andR .r7 .r0 .r6, eorR .r4 .r4 .r7, eorR .r7 .r1 .r2, ldS .r6 7, andR .r0 .r0 .r6,
  eorR .r6 .r0 .r9, eorR .r3 .r3 .r4, eorR .r2 .r4 .r2, eorR .r9 .r2 .r9, eorR .r4 .r6 .r5,
  eorR .r12 .r12 .r9, eorR .r10 .r10 .r9, eorR .r5 .r7 .lr, eorR .r6 .r11 .r2, eorR .lr .r12 .r0,
  eorR .r7 .r10 .r3]

/-- The inverse S-box of the input with `{63}` added, from `q j` to `p j`. -/
def invSubBytes : List Instr := [
  eorR .lr .r7 .r6, eorR .r12 .r5 .r4, eorR .r9 .lr .r0, eorR .r11 .r9 .r4, eorR .r1 .r12 .r1,
  eorR .r6 .r1 .r6, eorR .r4 .r4 .r2, eorR .r0 .r4 .r0, eorR .r3 .r1 .r3, eorR .r5 .r6 .r5,
  eorR .r10 .r6 .r9, stS 0 .r4, andR .r4 .r5 .r9, stS 1 .r9, eorR .r9 .r3 .r5, stS 2 .r5,
  andR .r5 .r9 .r10, stS 3 .r10, eorR .r10 .r9 .r7, eorR .lr .lr .r0, stS 4 .r9, andR .r9 .r3 .r6,
  eorR .r4 .r4 .r9, eorR .r5 .r5 .r9, eorR .r12 .r12 .r5, eorR .r9 .r1 .r2, eorR .r7 .r9 .r7,
  eorR .r0 .r0 .r4, eorR .r4 .r4 .r2, eorR .r2 .r3 .r11, stS 5 .r3, andR .r3 .r2 .r10,
  eorR .r3 .r3 .r5, eorR .r5 .r7 .r2, stS 6 .r2, andR .r2 .r5 .lr, stS 7 .r5, eorR .r5 .r10 .lr,
  stS 8 .lr, andR .lr .r7 .r5, stS 9 .r7, eorR .r7 .r10 .r6, eorR .r1 .r5 .r1, eorR .r4 .lr .r4,
  eorR .lr .r4 .r2, eorR .r4 .r10 .r9, eorR .r2 .r9 .r2, ldS .r9 0, stS 10 .r6, andR .r6 .r1 .r9,
  eorR .r3 .r2 .r3, eorR .r2 .r12 .r6, eorR .r12 .r7 .r9, andR .r9 .r11 .r7, stS 11 .r11,
  andR .r11 .r4 .r12, eorR .r6 .r0 .r6, eorR .r0 .lr .r3, eorR .r2 .r2 .r9, eorR .r6 .r6 .r11,
  andR .r9 .r6 .lr, eorR .r11 .r3 .r9, eorR .r9 .r2 .r9, andR .r0 .r9 .r0, eorR .r0 .r3 .r0,
  eorR .r9 .r11 .r0, andR .r1 .r0 .r1, eorR .r6 .r6 .r2, andR .r3 .r3 .r9, andR .r9 .r6 .r11,
  eorR .r2 .r2 .r9, eorR .r9 .r11 .r3, andR .r9 .r2 .r9, eorR .r3 .r0 .r3, eorR .r3 .r3 .lr,
  eorR .lr .r3 .r0, eorR .r6 .r9 .r6, andR .r7 .r3 .r7, andR .r4 .lr .r4, andR .r10 .r6 .r10,
  eorR .r11 .r6 .r2, andR .lr .lr .r12, ldS .r12 9, andR .r12 .r11 .r12, andR .r5 .r11 .r5,
  eorR .lr .lr .r7, eorR .r9 .r12 .r4, ldS .r11 0, andR .r12 .r0 .r11, eorR .r4 .r4 .r1,
  eorR .r0 .r0 .r2, ldS .r11 2, andR .r11 .r0 .r11, eorR .r4 .r4 .r11, ldS .r11 11,
  andR .r11 .r3 .r11, eorR .r9 .r9 .r11, eorR .r1 .r1 .r11, eorR .r7 .r12 .r7, eorR .r11 .r3 .r6,
  ldS .r3 8, andR .r3 .r2 .r3, ldS .r12 6, andR .r6 .r6 .r12, ldS .r12 10, andR .r12 .r11 .r12,
  eorR .r12 .r12 .r3, eorR .r7 .r7 .r6, eorR .r3 .r7 .r3, ldS .r7 7, andR .r7 .r2 .r7,
  eorR .r3 .r3 .r10, eorR .r2 .r9 .r6, eorR .r7 .r3 .r7, eorR .r3 .r9 .r3, ldS .r6 5,
  andR .r6 .r11 .r6, eorR .r9 .r11 .r0, eorR .r4 .r4 .r6, ldS .r11 1, andR .r11 .r0 .r11,
  eorR .r1 .r1 .r7, eorR .r0 .r1 .r11, eorR .r12 .r0 .r12, eorR .r11 .lr .r4, ldS .lr 3,
  andR .lr .r9 .lr, eorR .r0 .r0 .lr, eorR .r12 .r12 .r5, ldS .lr 4, andR .lr .r9 .lr,
  eorR .lr .lr .r7, eorR .r6 .lr .r6, eorR .lr .r2 .r12, eorR .r7 .r11 .r0, eorR .r10 .r10 .r0,
  eorR .r2 .r12 .r7, eorR .r5 .r10 .r5]

/-- As `subBytes`, in place in `q j`, keeping `kp`: for the key expansion
and SEED, which have their own uses for it. -/
def subBytesQ : List Instr := [
  eorR .r2 .r5 .r2, eorR .lr .r2 .r1, eorR .r10 .lr .r6, eorR .r3 .r3 .r10, eorR .r3 .r3 .r7,
  eorR .r12 .r3 .r2, eorR .r11 .r12 .r4, eorR .r0 .lr .r0, eorR .r1 .r11 .r1, stS 0 .r6,
  eorR .r6 .r0 .r7, stS 1 .r11, andR .r11 .r6 .r1, eorR .r2 .r11 .r2, eorR .r11 .r3 .r4,
  stS 2 .r6, andR .r6 .r7 .lr, stS 3 .r1, andR .r1 .r0 .r11, stS 4 .r11, eorR .r11 .r12 .r0,
  eorR .r4 .r11 .r4, stS 5 .r0, andR .r0 .r4 .r11, eorR .r5 .r11 .r5, eorR .r2 .r2 .r0,
  eorR .r3 .r4 .r3, eorR .r0 .r0 .r6, eorR .r6 .r11 .r10, stS 6 .r11, eorR .r11 .r5 .r7,
  eorR .r0 .r0 .r11, stS 7 .r7, eorR .r7 .r4 .r11, stS 8 .r4, andR .r4 .r11 .r10, stS 9 .r11,
  ldS .r11 1, stS 10 .r10, andR .r10 .r11 .r3, stS 11 .r3, andR .r3 .r7 .r6, eorR .r4 .r10 .r4,
  stS 12 .r7, eorR .r7 .r11 .r5, eorR .r3 .r10 .r3, ldS .r10 0, eorR .r0 .r0 .r10,
  andR .r11 .r5 .r10, eorR .r2 .r2 .r3, eorR .r3 .r1 .r3, eorR .r0 .r0 .r4, eorR .r1 .r5 .r1,
  eorR .r1 .r1 .lr, eorR .r4 .r1 .r4, andR .r1 .r0 .r2, eorR .r4 .r4 .r11, ldS .r11 3,
  eorR .r10 .r6 .r11, andR .r11 .r7 .r10, eorR .r3 .r3 .r11, eorR .r11 .r4 .r1, eorR .r3 .r3 .r12,
  eorR .r12 .r2 .r3, andR .r11 .r11 .r12, eorR .r12 .r3 .r11, eorR .r1 .r3 .r1,
  eorR .r11 .r1 .r12, andR .r3 .r3 .r11, eorR .r2 .r2 .r3, eorR .r0 .r0 .r4, eorR .r2 .r2 .r12,
  andR .r11 .r0 .r1, eorR .r4 .r4 .r11, eorR .r3 .r1 .r3, andR .r3 .r4 .r3, ldS .r1 10,
  andR .r1 .r2 .r1, eorR .r0 .r3 .r0, eorR .r3 .r12 .r2, eorR .r11 .r4 .r0, andR .lr .r12 .lr,
  andR .r5 .r3 .r5, andR .r7 .r11 .r7, andR .r11 .r11 .r10, ldS .r10 0, andR .r3 .r3 .r10,
  andR .r6 .r0 .r6, eorR .r11 .r11 .r6, eorR .r1 .r1 .lr, eorR .r3 .r3 .lr, eorR .lr .r4 .r12,
  ldS .r10 7, andR .r12 .r12 .r10, eorR .r5 .r12 .r5, eorR .r5 .r5 .r7, ldS .r10 9,
  andR .r10 .r2 .r10, eorR .r10 .r10 .r12, ldS .r12 3, andR .r12 .r4 .r12, eorR .r3 .r3 .r11,
  eorR .r6 .r12 .r6, ldS .r12 4, andR .r12 .lr .r12, eorR .r12 .r12 .r11, eorR .r6 .r6 .r1,
  ldS .r11 5, andR .r11 .lr .r11, eorR .r2 .r0 .r2, eorR .lr .lr .r2, eorR .r7 .r7 .r11,
  eorR .r7 .r7 .r6, ldS .r11 12, andR .r0 .r0 .r11, ldS .r11 2, andR .r4 .r4 .r11,
  eorR .r11 .r0 .r10, ldS .r10 1, andR .r10 .lr .r10, eorR .r10 .r10 .r0, ldS .r0 11,
  andR .lr .lr .r0, eorR .r0 .r7 .r10, ldS .r7 8, andR .r7 .r2 .r7, eorR .r7 .r10 .r7, ldS .r10 6,
  andR .r2 .r2 .r10, eorR .r10 .r2 .r1, eorR .r3 .r3 .lr, eorR .r3 .r3 .r2, eorR .r11 .r4 .r11,
  eorR .r1 .r7 .r4, eorR .r2 .r5 .r7, eorR .r7 .r1 .lr, eorR .r5 .r6 .r1, eorR .r4 .r11 .r0,
  eorR .r6 .r12 .r7, eorR .r6 .r6 .r2, eorR .r7 .r10 .r7]

/-- `{63}` added to the bytes. -/
def add63 : List Instr := ([0, 1, 5, 6] : List Nat).map fun j => .mvn (q j) (.reg (q j))

/-- The S-box on the slices in `q 0 … q 7`, in place. -/
def sboxCode : List Instr := subBytesQ ++ add63

/-! ## What the other ciphers' S-boxes are allocated with -/

/-- The registers and slots besides the slices'. -/
def sboxFree : List Reg := [.r10, .r11, .r12, .lr]
def onesSlot : Nat := 0
def spillSlots : List Nat := List.range' 1 31

end VG.Impl.Aes.Arm
