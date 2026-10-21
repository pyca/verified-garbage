module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateSave
public import VerifiedGarbage.Impl.RsaKeyGen.X86.ExponentImport
public import VerifiedGarbage.Impl.RsaKeyGen.X86.ExponentFilter

/-! # Save candidate minus one and check the complete public exponent -/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.CandidateExponent
open VG VG.X86 VG.Impl.Bignum.X86.PublicContext

def prepare (w : Nat) : Prog isa :=
  .seq (CandidateSave.save (2 * w) (slot w 0) (slot w 5))
    ExponentImport.code

def code (w : Nat) : Prog isa :=
  .seq (CandidateSave.save (2 * w) (slot w 0) (slot w 5))
    (.seq ExponentImport.code (ExponentFilter.code w))

end VG.Impl.RsaKeyGen.X86.CandidateExponent
