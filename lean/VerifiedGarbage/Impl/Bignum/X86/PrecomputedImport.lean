module

public import VerifiedGarbage.Impl.Bignum.X86.ImportArray
public import VerifiedGarbage.Impl.Bignum.X86.PublicContext

/-! # Import the two packed public-key arrays -/

@[expose] public section
namespace VG.Impl.Bignum.X86.PublicContext
open VG VG.X86

def precomputedImport (n : Nat) : Prog isa :=
  .seq (importArray n (slot n 0)) (importArray n (slot n 5))

end VG.Impl.Bignum.X86.PublicContext
