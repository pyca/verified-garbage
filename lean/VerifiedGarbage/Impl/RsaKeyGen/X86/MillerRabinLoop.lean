module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessStep
public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessAvailable
public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessChecks

/-! # Repeated blinded witness tests with checked entropy exhaustion -/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.MillerRabinLoop
open VG VG.X86 VG.Impl.Mont.X86

def exhausted : List Instr := [.mov .eax (.imm 0), .store (sc 168) .eax]
def again : List Instr := [.mov .eax (.mem (sc 168)), .alu .cmp .eax (.imm 4)]

def step (w : Nat) (montName : String) (montCode : Prog isa) (roundName : String) (roundCode : Prog isa) : Prog isa :=
  .seq (.block (WitnessAvailable.code w))
    (.seq (.ite .b (.block exhausted) (WitnessStep.code w montName montCode roundName roundCode)) (.block again))

def code (w : Nat) (montName : String) (montCode : Prog isa) (roundName : String) (roundCode : Prog isa) : Prog isa :=
  .seq (.block (WitnessChecks.code w)) (.loop (step w montName montCode roundName roundCode) .e)

end VG.Impl.RsaKeyGen.X86.MillerRabinLoop
