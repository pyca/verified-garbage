module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.TestWitness
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.StoredWitness

/-! # RSA-compatible witness selection for DSA's primality test -/

@[expose] public section
namespace VG.Impl.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate

def sampleWitness : Prog isa := .seq testWitness
  (.ite .e (.seq (forceStoredWitness kOut kUsedP) (loadPadded aXm kOut kUsedP)) (.block []))

end VG.Impl.Dsa.X86_64.Generation
