module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.FastR2
public import VerifiedGarbage.Impl.Bignum.X86.PublicContext
public import VerifiedGarbage.Impl.MillerRabin.X86.Round

/-! # Fast R² setup calls the prepared multiplier used by Miller–Rabin -/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.PreparedR2
open VG VG.X86 VG.Impl.Bignum.X86.PublicContext

/-- Array six is the multiplier's in-place operand; retain R² in array four
before Miller–Rabin uses array six for its running result. -/
def codeAt (e w : Nat) (montName : String) (montCode : Prog isa) : Prog isa :=
  .seq (FastR2.codeAt (modulus w) e (slot w 2) (slot w 6)
    (VG.Impl.MillerRabin.X86.mulY montName montCode 6)) (VG.Impl.MillerRabin.X86.copy 4 6)

def code (w : Nat) (montName : String) (montCode : Prog isa) : Prog isa := codeAt (64 * w - 1) w montName montCode

end VG.Impl.RsaKeyGen.X86.PreparedR2
