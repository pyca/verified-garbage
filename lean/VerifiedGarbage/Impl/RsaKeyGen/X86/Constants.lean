module

public import VerifiedGarbage.Impl.Bignum.X86.PublicContext
public import VerifiedGarbage.Impl.MillerRabin.X86.Round

/-! # Prepare Montgomery one and minus one once for every candidate -/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.Constants
open VG VG.X86 VG.Impl.Bignum.X86.PublicContext VG.Impl.Mont.X86.Dynamic

def subtract (w : Nat) : Prog isa := chainW .sbb (2 * w) (slot w 10) (slot w 0) (slot w 9)

def code (w : Nat) (montName : String) (montCode : Prog isa) : Prog isa :=
  .seq (one w (slot w 6)) (.seq (VG.Impl.MillerRabin.X86.mulY montName montCode 4)
    (.seq (VG.Impl.MillerRabin.X86.copy 9 6) (subtract w)))

end VG.Impl.RsaKeyGen.X86.Constants
