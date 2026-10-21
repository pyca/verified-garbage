module

public import VerifiedGarbage.Impl.MillerRabin.X86.Round

/-! # Convert each sampled witness with the candidate's cached R² -/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.WitnessMont
open VG VG.X86

def code (montName : String) (montCode : Prog isa) : Prog isa :=
  .seq (VG.Impl.MillerRabin.X86.mulY montName montCode 4)
    (VG.Impl.MillerRabin.X86.copy 5 6)

end VG.Impl.RsaKeyGen.X86.WitnessMont
