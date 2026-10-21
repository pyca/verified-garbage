module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.ImportEntry
public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateBits

/-! # Construct an RSA prime candidate from its random bytes -/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.CandidateImport
open VG VG.X86

def code (w out : Nat) : Prog isa :=
  .seq (Import.load (2 * w) out) (.block (CandidateBits.code w out))

end VG.Impl.RsaKeyGen.X86.CandidateImport
