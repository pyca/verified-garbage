module

public import VerifiedGarbage.Impl.Bignum.X86.SanitizeModulus
public import VerifiedGarbage.Impl.Mont.X86.Context

/-! # Safe Montgomery preparation for a secret RSA factor -/

@[expose] public section
namespace VG.Impl.Bignum.X86
open VG VG.X86 VG.Impl.Mont.X86.Dynamic

def preparePrime (n : Nat) : Prog isa :=
  .seq (sanitizeModulus n (slot n 0) (slot n 7)) (contextSetup n)

end VG.Impl.Bignum.X86
