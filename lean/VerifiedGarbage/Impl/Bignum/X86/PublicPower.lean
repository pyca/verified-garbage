module

public import VerifiedGarbage.Impl.Bignum.X86.SparseExponent

/-! # Public RSA modular exponentiation in the contract-sized workspace -/

@[expose] public section
namespace VG.Impl.Bignum.X86.PublicContext
open VG VG.X86

def publicPower (n : Nat) : Prog isa := .seq (setup n) (sparseExponentiate n)

end VG.Impl.Bignum.X86.PublicContext
