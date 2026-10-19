module

public import VerifiedGarbage.Impl.Bignum.X86.PrecomputedSetup
public import VerifiedGarbage.Impl.Bignum.X86.PublicExponent

/-! # Public exponentiation that reuses the caller's stored Montgomery power -/

@[expose] public section
namespace VG.Impl.Bignum.X86.PublicContext
open VG VG.X86

def precomputedPower (n : Nat) : Prog isa := .seq (precomputedSetup n) (exponentiate n)

end VG.Impl.Bignum.X86.PublicContext
