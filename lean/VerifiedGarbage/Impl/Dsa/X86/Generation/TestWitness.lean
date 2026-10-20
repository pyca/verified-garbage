module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.PrimeLayout
public import VerifiedGarbage.Impl.Dsa.X86.Width
public import VerifiedGarbage.Impl.Mont.X86.Context

/-! # Classify a witness without changing it

Slot five holds the draw cut to the candidate width; slot eight holds
candidate minus one. A full mask records a uniform draw in [2, w - 1).
The zero flag selects the forced-witness path.
-/
@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86

def testWitnessFinish : List Instr :=
  [.alu .xor .eax (.imm (BitVec.allOnes 32)), .alu .and .eax (.reg .ebx),
   .store (sc primeIsUniform) .eax, .alu .cmp .eax (.imm 0)]

def testWitness (n : Nat) : Prog isa :=
  .seq (lessThan n (slot n 5) (slot n 8))
    (.seq (.block [.mov .ebx (.reg .eax)])
      (.seq (lessThanConstant n (slot n 5) (slot n 7) 2) (.block testWitnessFinish)))
end VG.Impl.Dsa.X86.Generation
