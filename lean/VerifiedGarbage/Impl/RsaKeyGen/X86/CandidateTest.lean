module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateFrame
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Prepare
public import VerifiedGarbage.Impl.RsaKeyGen.X86.MillerRabinLoop

/-! # One prepared candidate and one private frame serve all blinded witnesses -/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.CandidateTest
open VG VG.X86

/-- Preparation for a candidate of at least `e + 1` bits, and the loop with
`checks` uniform tests required and witnesses of `D` octets cut to `k`
native words. -/
def coreWith (e checks D k w : Nat) (montName : String) (montCode : Prog isa) (roundName : String)
    (roundCode : Prog isa) : Prog isa :=
  .seq (Prepare.codeAt e w montName montCode) (MillerRabinLoop.codeWith checks D k w montName montCode roundName roundCode)

def codeWith (e checks D k w : Nat) (montName : String) (montCode : Prog isa) (roundName : String)
    (roundCode : Prog isa) : Prog isa :=
  CandidateFrame.code (coreWith e checks D k w montName montCode roundName roundCode)

/-- Preparation and the loop with `checks` uniform tests required. -/
def coreOf (checks w : Nat) (montName : String) (montCode : Prog isa) (roundName : String) (roundCode : Prog isa) :
    Prog isa :=
  coreWith (64 * w - 1) checks (8 * w) (2 * w) w montName montCode roundName roundCode

def codeOf (checks w : Nat) (montName : String) (montCode : Prog isa) (roundName : String) (roundCode : Prog isa) :
    Prog isa :=
  codeWith (64 * w - 1) checks (8 * w) (2 * w) w montName montCode roundName roundCode

def core (w : Nat) (montName : String) (montCode : Prog isa) (roundName : String) (roundCode : Prog isa) : Prog isa :=
  coreOf (WitnessChecks.checks w) w montName montCode roundName roundCode

def code (w : Nat) (montName : String) (montCode : Prog isa) (roundName : String) (roundCode : Prog isa) : Prog isa :=
  codeOf (WitnessChecks.checks w) w montName montCode roundName roundCode

end VG.Impl.RsaKeyGen.X86.CandidateTest
