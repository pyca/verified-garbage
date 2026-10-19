module

public import VerifiedGarbage.Impl.Bignum.X86.PublicContext

/-! # Prepare Montgomery arithmetic using a stored R² value -/

@[expose] public section
namespace VG.Impl.Bignum.X86.PublicContext
open VG VG.X86 VG.Impl.Mont.X86

def precomputedSetup (n : Nat) : Prog isa :=
  .seq (.block (Dynamic.setupInverse (slot n 0) inverseOffset)) (Dynamic.one n (slot n 4))

end VG.Impl.Bignum.X86.PublicContext
