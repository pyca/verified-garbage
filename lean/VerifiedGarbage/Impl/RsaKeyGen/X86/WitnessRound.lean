module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessLoad
public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessMont
public import VerifiedGarbage.Impl.RsaKeyGen.X86.RoundCall

/-! # A complete witness iteration reuses candidate preparation -/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.WitnessRound
open VG VG.X86 VG.Impl.Mont.X86

def uniformOffset : Nat := 144

def codeAt (D k w : Nat) (montName : String) (montCode : Prog isa) (roundName : String) (roundCode : Prog isa) :
    Prog isa :=
  .seq (WitnessLoad.codeAt D k w) (.seq (.block [.store (sc uniformOffset) .eax])
    (.seq (WitnessMont.code montName montCode) (RoundCall.code roundName roundCode)))

def code (w : Nat) (montName : String) (montCode : Prog isa) (roundName : String) (roundCode : Prog isa) : Prog isa :=
  codeAt (8 * w) (2 * w) w montName montCode roundName roundCode

end VG.Impl.RsaKeyGen.X86.WitnessRound
