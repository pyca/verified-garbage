module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Sample
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.RoundTail

/-! # A DSA witness, the shared windowed round, and the completion policy -/

@[expose] public section
namespace VG.Impl.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64

def sampleRound (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa) : Prog isa :=
  .seq sampleWitness (.seq (Ffdh.X86_64.ParameterCandidate.witnessRound mul round) roundTail)

end VG.Impl.Dsa.X86_64.Generation
