module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Header
public import VerifiedGarbage.Impl.RsaKeyGen.X86.MontInverse

/-! # Prepare the shared header and full-width inverse once per candidate -/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.PrepareHeader
open VG VG.X86

def code (w : Nat) : Prog isa :=
  .seq (.block (Header.code w)) (MontInverse.code (VG.Impl.Bignum.X86.PublicContext.slot w 0) 56)

end VG.Impl.RsaKeyGen.X86.PrepareHeader
