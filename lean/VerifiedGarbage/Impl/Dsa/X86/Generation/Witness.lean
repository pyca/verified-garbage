module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.MontgomeryConstants
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Transfer
public import VerifiedGarbage.Impl.Dsa.X86.Checks
public import VerifiedGarbage.Impl.Dsa.X86.Core
public import VerifiedGarbage.Impl.Dsa.X86.Generation.ForceWitness

/-! RSA-compatible witness range checks share the existing DSA comparisons. -/

@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic

def witnessUniform : Nat := Dsa.Generation.Layout.control + 256

/-- Retain c-1 in an otherwise unused parent temporary for all witness checks. -/
def witnessInit (n : Nat) : Prog isa := parentDifference n 1 3

def loadWitness (n len : Nat) : Prog isa :=
  Dsa.X86.Core.load n len (slot n 5) (.local Dsa.Generation.Layout.witness)

def witnessRangeFinish : List Instr :=
  [.alu .and .eax (.mem (sc witnessUniform)), .shift .shr .eax 31,
    .store (sc witnessUniform) .eax, .alu .cmp .eax (.imm 0)]

def witnessRange (n : Nat) : Prog isa :=
  .seq (Dsa.X86.lessThan n (slot n 3) (slot n 5))
    (.seq (.block [.store (sc witnessUniform) .eax])
      (.seq (Dsa.X86.lessThan n (slot n 5) (slot n 1))
        (.block witnessRangeFinish)))

def encodeWitness (n : Nat) : Prog isa :=
  .seq (montgomery n 5 5 4) (compactNumberTransfer n 5 5).code

def sampleWitness (n len : Nat) : Prog isa :=
  .seq (loadWitness n len) (.seq (witnessRange n)
    (.ite .e (.seq (forceStoredWitness len) (loadWitness n len)) (.block [])))

end VG.Impl.Dsa.X86.Generation
