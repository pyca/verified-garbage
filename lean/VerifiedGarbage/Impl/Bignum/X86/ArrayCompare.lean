module
public import VerifiedGarbage.Impl.Bignum.X86.PublicContext


/-! # Compare two public workspace arrays without data-dependent branches -/

@[expose] public section
namespace VG.Impl.Bignum.X86.PublicContext
open VG VG.X86 VG.Impl.Mont.X86.Dynamic

/-- ECX receives an all-ones mask exactly when array `a` is less than array `b`. -/
def arrayCompare (n a b : Nat) : Prog isa :=
  chainW .sbb (2 * n) (slot n 1) (slot n a) (slot n b)

end VG.Impl.Bignum.X86.PublicContext
