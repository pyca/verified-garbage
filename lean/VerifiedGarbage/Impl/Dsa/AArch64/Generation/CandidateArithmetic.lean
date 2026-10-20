module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Reduce

/-! Load the hashed candidate and subgroup, then preserve p and its generator exponent. -/
@[expose] public section
namespace VG.Impl.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys

def candidateArithmetic : Prog isa :=
  .seq (seqs (loadA 0 16 17)) (.seq (seqs (loadA 2 18 19))
    (.seq (doubleArray 2) (.seq reduceCandidate (doubleArray 0))))

def candidateStores : Prog isa :=
  .seq (seqs (storeA 5 20 17 sMask)) (seqs (storeA 0 21 17 sMask))

def candidateBuild : Prog isa := .seq candidateArithmetic candidateStores

end VG.Impl.Dsa.AArch64.Generation
