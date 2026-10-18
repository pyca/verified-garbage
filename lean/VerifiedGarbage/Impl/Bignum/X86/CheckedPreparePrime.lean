module

public import VerifiedGarbage.Impl.Bignum.X86.PrimeMask
public import VerifiedGarbage.Impl.Bignum.X86.PreparePrime

/-! # Validate and prepare a secret factor without branches on its value -/

@[expose] public section
namespace VG.Impl.Bignum.X86
open VG VG.X86

def checkedPreparePrime (n : Nat) : Prog isa := .seq (primeMask n) (preparePrime n)

end VG.Impl.Bignum.X86
