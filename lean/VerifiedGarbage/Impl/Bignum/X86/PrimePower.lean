module

public import VerifiedGarbage.Impl.Bignum.X86.PreparePrime

/-! # Fixed-schedule exponentiation with a validated secret RSA factor -/

@[expose] public section
namespace VG.Impl.Bignum.X86
open VG VG.X86 VG.Impl.Mont.X86.Dynamic

def primePower (n : Nat) : Prog isa :=
  .seq (preparePrime n) (exponentiate n (2 * n))

end VG.Impl.Bignum.X86
