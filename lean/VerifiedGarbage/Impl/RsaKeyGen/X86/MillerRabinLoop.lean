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

/-- One witness of `D` octets, cut to `k` native words. -/
def stepAt (D k w : Nat) (montName : String) (montCode : Prog isa) (roundName : String) (roundCode : Prog isa) :
    Prog isa :=
  .seq (.block (WitnessAvailable.codeAt D))
    (.seq (.ite .b (.block exhausted) (WitnessStep.codeAt D k w montName montCode roundName roundCode)) (.block again))

def step (w : Nat) (montName : String) (montCode : Prog isa) (roundName : String) (roundCode : Prog isa) : Prog isa :=
  stepAt (8 * w) (2 * w) w montName montCode roundName roundCode

/-- The loop with `checks` uniform tests required, and witnesses of `D`
octets cut to `k` native words. -/
def codeWith (checks D k w : Nat) (montName : String) (montCode : Prog isa) (roundName : String)
    (roundCode : Prog isa) : Prog isa :=
  .seq (.block (WitnessChecks.codeOf checks)) (.loop (stepAt D k w montName montCode roundName roundCode) .e)

/-- The loop with `checks` uniform tests required. -/
def codeOf (checks w : Nat) (montName : String) (montCode : Prog isa) (roundName : String) (roundCode : Prog isa) :
    Prog isa :=
  codeWith checks (8 * w) (2 * w) w montName montCode roundName roundCode

def code (w : Nat) (montName : String) (montCode : Prog isa) (roundName : String) (roundCode : Prog isa) : Prog isa :=
  codeOf (WitnessChecks.checks w) w montName montCode roundName roundCode

end VG.Impl.RsaKeyGen.X86.MillerRabinLoop
