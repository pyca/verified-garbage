module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.ProbablePrime

/-! # Test a candidate directly from its preserved big-endian byte buffer -/

@[expose] public section
namespace VG.Impl.Dsa.X86_64.Generation
open VG VG.X86_64

def primeBytes (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa) : Prog isa :=
  .seq (loadPadded 0 20 18) (probablePrime mul round)

end VG.Impl.Dsa.X86_64.Generation
