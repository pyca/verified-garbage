module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.PrimeLayout
public import VerifiedGarbage.Impl.Dsa.X86.Generate

/-! # Consume a complete witness draw, copying only its significant bytes

For a 160-bit candidate, consume 24 bytes and copy the final 20. The
immutable random tape and writable witness buffer are separate regions.
-/
@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Mont.X86

def drawWitnessArgs (len drawBytes : Nat) : List Instr :=
  [.mov .esi (.mem (sc primeTape)), .mov .eax (.mem (sc primeUsed)),
   .alu .add .esi (.reg .eax), .alu .add .esi (.imm (BitVec.ofNat 32 (drawBytes - len))),
   .alu .add .eax (.imm (BitVec.ofNat 32 drawBytes)), .store (sc primeUsed) .eax,
   .mov .edx (.mem (sc primeWitness)), .mov .ecx (.imm (BitVec.ofNat 32 len)),
   .mov .ebx (.imm (BitVec.allOnes 32))]

def drawWitness (len drawBytes : Nat) : Prog isa :=
  .seq (.block (drawWitnessArgs len drawBytes))
    (.seq VG.Impl.Dsa.X86.Generate.copyMasked (.block [.mov .esi (.mem (sc primeWitness))]))
end VG.Impl.Dsa.X86.Generation
