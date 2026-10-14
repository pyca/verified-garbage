module

public import VerifiedGarbage.TCB.Arm.Isa

/-! # A 128-bit big-endian counter increment on ARMv7 -/

@[expose] public section

namespace VG.Impl.Modes.Arm

open VG.Arm

/-- Increment the counter at `base + off`, using `r9`, `r10` and the flags.
The carries propagate through all four words without conditional branches. -/
def incAt (base : Reg) (off : Nat) : List Instr :=
  [.ldr .r9 base (off + 12), .rev .r9 .r9, .adds .r9 .r9 (.imm 1),
   .rev .r9 .r9, .str .r9 base (off + 12),
   .mov .r10 (.imm 0), .adc .r10 .r10 (.imm 0),
   .ldr .r9 base (off + 8), .rev .r9 .r9, .adds .r9 .r9 (.reg .r10),
   .rev .r9 .r9, .str .r9 base (off + 8),
   .mov .r10 (.imm 0), .adc .r10 .r10 (.imm 0),
   .ldr .r9 base (off + 4), .rev .r9 .r9, .adds .r9 .r9 (.reg .r10),
   .rev .r9 .r9, .str .r9 base (off + 4),
   .ldr .r9 base off, .rev .r9 .r9, .adc .r9 .r9 (.imm 0),
   .rev .r9 .r9, .str .r9 base off]

end VG.Impl.Modes.Arm
