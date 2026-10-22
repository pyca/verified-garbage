module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateFrame
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Prepare
public import VerifiedGarbage.Impl.RsaKeyGen.X86.MillerRabinLoop

/-! # One prepared candidate and one private frame serve all blinded witnesses -/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.CandidateTest
open VG VG.X86

/-- Preparation and the loop with `checks` uniform tests required. -/
def coreOf (checks w : Nat) (montName : String) (montCode : Prog isa) (roundName : String) (roundCode : Prog isa) :
    Prog isa :=
  .seq (Prepare.code w montName montCode) (MillerRabinLoop.codeOf checks w montName montCode roundName roundCode)

def codeOf (checks w : Nat) (montName : String) (montCode : Prog isa) (roundName : String) (roundCode : Prog isa) :
    Prog isa :=
  CandidateFrame.code (coreOf checks w montName montCode roundName roundCode)

def core (w : Nat) (montName : String) (montCode : Prog isa) (roundName : String) (roundCode : Prog isa) : Prog isa :=
  coreOf (WitnessChecks.checks w) w montName montCode roundName roundCode

def code (w : Nat) (montName : String) (montCode : Prog isa) (roundName : String) (roundCode : Prog isa) : Prog isa :=
  codeOf (WitnessChecks.checks w) w montName montCode roundName roundCode

end VG.Impl.RsaKeyGen.X86.CandidateTest
