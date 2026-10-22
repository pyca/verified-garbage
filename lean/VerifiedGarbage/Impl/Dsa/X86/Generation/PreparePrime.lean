module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.PrimePreparation
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Witness

/-! Prepare reusable candidate data and the shared sampler's upper bound. -/

@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86

def preparePrime (n bits : Nat) : Prog isa := .seq (primePreparation n bits) (witnessInit n)

end VG.Impl.Dsa.X86.Generation
