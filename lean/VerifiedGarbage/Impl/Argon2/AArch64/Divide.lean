module

public import VerifiedGarbage.TCB.AArch64.Isa

/-! # Fixed-time division for ARM64 Argon2 reference indices

The positive divisor in x1 and numerator in x0 fit in 32 bits. The
quotient is returned in x5, remainder in x4. Borrow selects the remainder
through a mask, without variable-latency hardware division or branches on the
numerator. `loopCode`, for code that divides once per derivation, runs one
step per bit in a loop counted down in x15, taking bit 31 of x0 and doubling
x0 after each step, so it consumes x0. The reference lane of every block
needs only a remainder, which `Remainder` computes with a shorter step.
-/

@[expose] public section

namespace VG.Impl.Argon2.AArch64.Divide
open VG.AArch64

def subtract (j : Nat) : List Instr :=
  [.lsr .x .x3 .x0 j, .movz .x .x9 1 0, .logic .and .x .x3 .x3 .x9,
    .add .x .x4 .x4 .x4, .add .x .x4 .x4 .x3,
    .addImm .x .x6 .x4 0, .sub .x .x4 .x4 .x1, .lsr .x .x8 .x4 63,
    .movz .x .x9 0 0, .sub .x .x8 .x9 .x8]

def select : List Instr :=
  [.logic .eor .x .x6 .x6 .x4, .logic .and .x .x6 .x6 .x8,
    .logic .eor .x .x4 .x4 .x6, .addImm .x .x8 .x8 1,
    .add .x .x5 .x5 .x5, .add .x .x5 .x5 .x8]

def bit (j : Nat) : List Instr := subtract j ++ select

def setup : List Instr := [.movz .x .x4 0 0, .movz .x .x5 0 0]

def loopSetup : List Instr := setup ++ [.movz .x .x15 32 0]

def loopAdvance : List Instr := [.add .x .x0 .x0 .x0, .subImm .x .x15 .x15 1]

def loopBody : Prog isa := .seq (.block (bit 31)) (.block loopAdvance)

def loopCode : Prog isa := .seq (.block loopSetup) (.loop loopBody (.nonzero .x .x15))
end VG.Impl.Argon2.AArch64.Divide
