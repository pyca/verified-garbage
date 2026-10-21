module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.PrepareHeader
public import VerifiedGarbage.Impl.RsaKeyGen.X86.PreparedR2
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Constants
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Exponent

/-! # Prepare a candidate's Montgomery arithmetic and exponent once for every witness -/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.Prepare
open VG VG.X86 VG.Impl.Bignum.X86.PublicContext

def code (w : Nat) (montName : String) (montCode : Prog isa) : Prog isa :=
  .seq (PrepareHeader.code w) (.seq (PreparedR2.code w montName montCode)
    (.seq (Constants.code w montName montCode) (Exponent.code w (slot w 5) (slot w 0) (slot w 27))))

end VG.Impl.RsaKeyGen.X86.Prepare
