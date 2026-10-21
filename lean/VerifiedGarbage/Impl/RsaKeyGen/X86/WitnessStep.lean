module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessAdvance
public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessRound
public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessCount

/-! # Consume, test and count one candidate-width witness -/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.WitnessStep
open VG VG.X86

def code (w : Nat) (montName : String) (montCode : Prog isa) (roundName : String) (roundCode : Prog isa) : Prog isa :=
  .seq (.block (WitnessAdvance.code w))
    (.seq (WitnessRound.code w montName montCode roundName roundCode) WitnessCount.code)

end VG.Impl.RsaKeyGen.X86.WitnessStep
