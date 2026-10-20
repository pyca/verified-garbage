module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.BufferArgs
public import VerifiedGarbage.Impl.Dsa.X86.Generation.CandidateCompute
public import VerifiedGarbage.Impl.Dsa.X86.Generation.CandidateStore

/-! # Address the shared candidate workspace and persist its two results -/
@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86

def candidateArgs : List Instr :=
  bufferPointer .esi VG.Impl.Dsa.Generation.Layout.shaped ++
  bufferPointer .ecx VG.Impl.Dsa.Generation.Layout.q ++
  bufferPointer .edi VG.Impl.Dsa.Generation.Layout.arithmetic

def candidateComputeFromFrame (plen qlen n : Nat) : Prog isa :=
  .seq (.block candidateArgs) (candidateCompute plen qlen n)

def candidateStores (plen : Nat) : Prog isa :=
  .seq (.block (bufferPointer .esi VG.Impl.Dsa.Generation.Layout.p))
    (.seq (storePublic plen candidateP)
      (.seq (.block (bufferPointer .esi VG.Impl.Dsa.Generation.Layout.exponent))
        (storePublic plen candidateQuotient)))
end VG.Impl.Dsa.X86.Generation
