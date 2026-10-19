module

public import VerifiedGarbage.Impl.Bignum.X86.PrimeMask
public import VerifiedGarbage.Impl.Bignum.X86.PrimePower

/-! # Factor exponentiation with branch-free validation and safe rejection arithmetic -/

@[expose] public section
namespace VG.Impl.Bignum.X86
open VG VG.X86

def checkedPrimePower (n : Nat) : Prog isa := .seq (primeMask n) (primePower n)

end VG.Impl.Bignum.X86
