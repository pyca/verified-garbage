module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Difference
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Near

/-! # Compare two secret RSA prime candidates for required separation -/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.Close
open VG VG.X86

def code (n out tmp a b : Nat) : Prog isa :=
  .seq (Difference.code n out tmp a b) (Near.code n out)

end VG.Impl.RsaKeyGen.X86.Close
