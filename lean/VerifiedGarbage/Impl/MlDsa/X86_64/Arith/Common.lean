module

public import VerifiedGarbage.TCB.X86_64.Isa

/-!
# ML-DSA on x86-64: arithmetic modulo `q`

What the ML-DSA arithmetic functions share: memory operands (`at_`) and
`q = 8380417 < 2²³` as an immediate (`qImm`).
-/

@[expose] public section

namespace VG.Impl.MlDsa.X86_64.Arith

open VG.X86_64

/-- `[b + d]`. -/
def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-- `q = 8380417`, as an immediate. -/
def qImm : BitVec 32 := 8380417

end VG.Impl.MlDsa.X86_64.Arith
