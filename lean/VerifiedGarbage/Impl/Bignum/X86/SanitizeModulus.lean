module

public import VerifiedGarbage.Impl.Bignum.X86.SmallConstant

/-! # Replace a rejected secret modulus with three under a mask -/

@[expose] public section
namespace VG.Impl.Bignum.X86
open VG VG.X86 VG.Impl.Mont.X86

/-- `ecx` is all ones for an accepted modulus and zero otherwise. -/
def sanitizeModulus (n modulus temporary : Nat) : Prog isa :=
  .seq (smallConstant n temporary 3) (Dynamic.selectsW (2 * n) temporary modulus modulus)

end VG.Impl.Bignum.X86
