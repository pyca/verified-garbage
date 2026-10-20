module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.GeneratorEvaluate
public import VerifiedGarbage.Impl.Dsa.X86.Generation.SampleWitness
public import VerifiedGarbage.Impl.Dsa.X86.Generation.TapeLoop
public import VerifiedGarbage.Impl.Dsa.X86.Generation.BufferArgs
public import VerifiedGarbage.Impl.Dsa.X86.Generation.CandidateStore

/-! # Search h candidates while reusing the accepted p's prepared context -/
@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Mont.X86.Dynamic

def generatorStore (plen : Nat) : Prog isa :=
  .seq (.block (bufferPointer .esi VG.Impl.Dsa.Generation.Layout.g))
    (storePublic plen (slot ((plen + 7) / 8) 6))

def generatorCandidate (plen : Nat) : Prog isa :=
  .seq (sampleHead plen)
    (.ite .e (.block (frameStatus 3))
      (.seq (.block (bufferPointer .esi VG.Impl.Dsa.Generation.Layout.exponent))
        (.seq (generatorEvaluate plen)
          (.seq (.block [.store (frameSlot 19) .eax]) (onSuccess (generatorStore plen))))))

def generatorBody (plen : Nat) : Prog isa :=
  .seq (.block (workspaceBase ++ [.mov .esi (.mem (frameSlot 21))])) (generatorCandidate plen)

def nativeGenerator (plen : Nat) : Prog isa := tapeLoop generatorTape plen (generatorBody plen)
end VG.Impl.Dsa.X86.Generation
