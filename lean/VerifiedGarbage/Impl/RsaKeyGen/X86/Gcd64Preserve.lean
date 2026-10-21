module

import VerifiedGarbage.Impl.RsaKeyGen.X86.Gcd64Check
public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateSave
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Gcd64
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Gcd64Result
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Gcd64Setup

/-! # Restore the candidate after the general exponent's native GCD -/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.Gcd64
open VG VG.X86

def preserving (n dst saved offset : Nat) : Prog isa :=
  .seq (.block (setup offset)) (.seq code
    (.seq (CandidateSave.restore n saved dst) (.block result)))

end VG.Impl.RsaKeyGen.X86.Gcd64
