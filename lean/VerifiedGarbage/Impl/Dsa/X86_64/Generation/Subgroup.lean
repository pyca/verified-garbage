module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PrimeCall
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.QCandidate

/-! # Hash, shape and test a subgroup-prime candidate in native code -/

@[expose] public section
namespace VG.Impl.Dsa.X86_64.Generation
open VG VG.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)

def subgroup (G1 G256 : Stream) (prime : Prog isa) (len : Nat) : Prog isa :=
  .seq (qCandidate G1 G256 len) (primeCall prime (8 * len))

end VG.Impl.Dsa.X86_64.Generation
