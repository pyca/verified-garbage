module

public import VerifiedGarbage.Impl.Mont.X86.Context

/-! # Reduce a full-width CRT operand modulo a secret factor -/

@[expose] public section
namespace VG.Impl.Bignum.X86
open VG VG.X86 VG.Impl.Mont.X86.Dynamic

def reduceOperand (n operand : Nat) : Prog isa :=
  .seq (mul (contextMod n) 0 (slot n 2) (slot n operand) (slot n operand) (slot n 4))
    (mul (contextMod n) 0 (slot n 2) (slot n operand) (slot n operand) (slot n 3))

end VG.Impl.Bignum.X86
