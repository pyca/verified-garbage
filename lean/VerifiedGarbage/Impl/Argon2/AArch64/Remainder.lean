module

public import VerifiedGarbage.TCB.AArch64.Isa

/-! # Fixed-time remainder for ARM64 Argon2 reference lanes

The numerator in x0 fits in 32 bits and the positive divisor in x1 is below
2³². The remainder is returned in x4; x0 and x9 are clobbered. Each of the 32
unrolled steps shifts the next numerator bit into the partial remainder with
EXTR and subtracts the divisor when SUBS reports no borrow, with CSEL: there
are no branches and no variable-latency instructions, so a secret numerator
does not affect the trace. Three instructions of each step depend on the
previous one, against eight in the shift-and-subtract division (`Divide`).
-/

@[expose] public section

namespace VG.Impl.Argon2.AArch64.Remainder
open VG.AArch64

/-- Zero the remainder and move the numerator's bit 31 to bit 63. -/
def setup : List Instr := [.movz .x .x4 0 0, .lsl .x .x0 .x0 32]

/-- Shift the next numerator bit into the remainder and reduce it once. -/
def step : List Instr :=
  [.extr .x .x4 .x4 .x0 63, .lsl .x .x0 .x0 1, .subs .x .x9 .x4 .x1,
    .cselc .x .x4 .x9 .x4 .hs]

def steps (n : Nat) : List Instr := (List.replicate n step).flatten

def code : Prog isa := .block (setup ++ steps 32)

end VG.Impl.Argon2.AArch64.Remainder
