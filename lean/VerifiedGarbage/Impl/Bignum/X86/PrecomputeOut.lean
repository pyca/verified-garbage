module

public import VerifiedGarbage.Impl.Bignum.X86.ExportArray
public import VerifiedGarbage.Impl.Bignum.X86.PublicContext

/-! # Serialize the modulus and Montgomery R-squared precomputation -/

@[expose] public section
namespace VG.Impl.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86.PublicContext

def precomputeOut (n : Nat) : Prog isa :=
  .seq (exportArray n (slot n 0))
    (.seq (exportArray n (slot n 5)) (.block [.mov .eax (.imm 1)]))

end VG.Impl.Bignum.X86
