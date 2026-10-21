module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateFrame
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Prepare
public import VerifiedGarbage.Impl.RsaKeyGen.X86.MillerRabinLoop

/-! # One prepared candidate and one private frame serve all blinded witnesses -/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.CandidateTest
open VG VG.X86

def core (w : Nat) (montName : String) (montCode : Prog isa) (roundName : String) (roundCode : Prog isa) : Prog isa :=
  .seq (Prepare.code w montName montCode) (MillerRabinLoop.code w montName montCode roundName roundCode)

def code (w : Nat) (montName : String) (montCode : Prog isa) (roundName : String) (roundCode : Prog isa) : Prog isa :=
  CandidateFrame.code (core w montName montCode roundName roundCode)

end VG.Impl.RsaKeyGen.X86.CandidateTest
