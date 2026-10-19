module

public import VerifiedGarbage.Impl.Bignum.X86.PublicContext
public import VerifiedGarbage.Impl.Mont.X86.Words

/-! # Accept exactly those RSA representatives below the modulus -/

@[expose] public section
namespace VG.Impl.Bignum.X86.PublicContext
open VG VG.X86 VG.Impl.Mont.X86.Dynamic

/-- ECX receives an all-ones acceptance mask; the subtraction uses array one. -/
def inputCompare (n : Nat) : Prog isa :=
  chainW .sbb (2 * n) (slot n 1) (slot n 6) (slot n 0)

end VG.Impl.Bignum.X86.PublicContext
