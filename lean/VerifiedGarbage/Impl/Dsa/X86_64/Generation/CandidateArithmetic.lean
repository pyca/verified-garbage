module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Reduce

/-! # Load and reduce the hashed p candidate entirely in native code

Header words 16/17 identify X and its byte length; words 18/19 identify q.
The resulting p is in array 5 and (p-1)/q is in array 0.
-/

@[expose] public section
namespace VG.Impl.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys

def candidateArithmetic : Prog isa := seqs [
  seqs (loadA 0 16 17), seqs (loadA 2 18 19), doubleArray 2,
  reduceCandidate, doubleArray 0]

/-- Save p and its generator exponent before primality testing reuses the
arithmetic arrays. Header words 20 and 21 contain the output pointers. -/
def candidateStores : Prog isa :=
  .seq (seqs (storeA 5 20 17 Public.sMask)) (seqs (storeA 0 21 17 Public.sMask))

def candidateBuild : Prog isa := .seq candidateArithmetic candidateStores

end VG.Impl.Dsa.X86_64.Generation
