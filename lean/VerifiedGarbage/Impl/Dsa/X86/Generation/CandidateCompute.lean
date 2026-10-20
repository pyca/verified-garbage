module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.CandidateLoad

/-! # Construct p and the generator exponent from the two persistent inputs -/
@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86

/-- ESI points to the shaped hash; ECX points to q; EDI is the arithmetic workspace. -/
def candidateCompute (plen qlen n : Nat) : Prog isa :=
  .seq (loadCandidate plen n)
    (.seq (.block [.mov .esi (.reg .ecx)])
      (.seq (loadDivisor qlen n) (reduceCandidate (2 * n))))
end VG.Impl.Dsa.X86.Generation
