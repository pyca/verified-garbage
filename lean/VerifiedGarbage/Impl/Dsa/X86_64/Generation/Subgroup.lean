module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Arguments
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PrimeCall
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.QCandidate

/-! # Hash, shape and test a subgroup-prime candidate in native code -/

@[expose] public section
namespace VG.Impl.Dsa.X86_64.Generation
open VG VG.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)
open VG.Impl.Bignum.X86_64 (seqs)

def subgroup (G1 G256 : Stream) (prime : Nat → Prog isa) (len : Nat) : Prog isa :=
  seqs [qCandidate G1 G256 len, .block workspaceBase, primeCall prime (8 * len)]

end VG.Impl.Dsa.X86_64.Generation
