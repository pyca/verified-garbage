module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.PrepareHeader
public import VerifiedGarbage.Impl.RsaKeyGen.X86.PreparedR2
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Constants
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Exponent

/-! # Prepare a candidate's Montgomery arithmetic and exponent once for every witness -/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.Prepare
open VG VG.X86 VG.Impl.Bignum.X86.PublicContext

/-- Preparation for a candidate of at least `e + 1` bits (`FastR2.codeAt`). -/
def codeAt (e w : Nat) (montName : String) (montCode : Prog isa) : Prog isa :=
  .seq (PrepareHeader.code w) (.seq (PreparedR2.codeAt e w montName montCode)
    (.seq (Constants.code w montName montCode) (Exponent.code w (slot w 5) (slot w 0) (slot w 27))))

def code (w : Nat) (montName : String) (montCode : Prog isa) : Prog isa := codeAt (64 * w - 1) w montName montCode

end VG.Impl.RsaKeyGen.X86.Prepare
