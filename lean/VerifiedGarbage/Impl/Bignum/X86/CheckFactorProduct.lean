module

public import VerifiedGarbage.Impl.Bignum.X86.WideProduct
public import VerifiedGarbage.Impl.Dsa.X86.Checks

/-! # Validate the full factor product under a mask -/

@[expose] public section
namespace VG.Impl.Bignum.X86
open VG VG.X86

/-- `modulus` holds `2*n` zero-extended 64-bit words. The acceptance mask is in `edx`. -/
def checkFactorProduct (n product p q modulus mult : Nat) : Prog isa :=
  .seq (wideProduct (2 * n) product p q mult) (VG.Impl.Dsa.X86.equal (2 * n) product modulus)

end VG.Impl.Bignum.X86
