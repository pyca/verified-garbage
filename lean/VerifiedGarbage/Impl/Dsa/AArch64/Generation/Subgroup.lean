module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PrimeCall
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.QCandidate

/-! Hash and shape q, then test it with the probable-prime function of its size. -/
@[expose] public section
namespace VG.Impl.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)

def subgroup (G1 G256 : Hash) (prime : Nat → Prog isa) (len : Nat) : Prog isa :=
  .seq (qCandidate G1 G256) (primeCall prime (8 * len))

end VG.Impl.Dsa.AArch64.Generation
