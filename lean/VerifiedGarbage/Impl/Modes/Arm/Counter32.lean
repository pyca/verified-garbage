module

public import VerifiedGarbage.TCB.Arm.Isa

/-! # GCM's 32-bit counter increment on ARMv7 -/

@[expose] public section

namespace VG.Impl.Modes.Arm

open VG.Arm

/-- GCM's `inc₃₂` (NIST SP 800-38D §6.2) of the counter block at
`base + off`: its last word, big-endian, plus 1 modulo 2³², using `r9`; the
first 96 bits are left as they are, and the flags too. -/
def inc32At (base : Reg) (off : Nat) : List Instr :=
  [.ldr .r9 base (off + 12), .rev .r9 .r9, .dp .add .r9 .r9 (.imm 1), .rev .r9 .r9, .str .r9 base (off + 12)]

end VG.Impl.Modes.Arm
