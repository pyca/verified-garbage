module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.ImportEntry
public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessSample
public import VerifiedGarbage.Impl.Bignum.X86.PublicContext

/-! # Read a fresh entropy block and sample a witness directly in its conversion operand -/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.WitnessLoad
open VG VG.X86 VG.Impl.Bignum.X86.PublicContext

def code (w : Nat) : Prog isa :=
  .seq (Import.load (2 * w) (slot w 6))
    (WitnessSample.code w (slot w 6) (slot w 0))

end VG.Impl.RsaKeyGen.X86.WitnessLoad
