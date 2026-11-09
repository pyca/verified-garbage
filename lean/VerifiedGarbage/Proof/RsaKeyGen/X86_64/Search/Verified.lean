module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Search.Correct
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Search.CT
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Search.Implies

/-! # The verified search, for every arithmetic backend -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64.Search


open VG VG.X86_64 VG.Proof.MillerRabin.X86_64

theorem search_verified (v : RoundImpl) :
    Verified target (searchCode v) (Proof.RsaKeyGen.primeSearchContract abi stackUse) :=
  Verified.of_correct (search_correct v) (search_constantTime v) search_implies

end VG.Proof.RsaKeyGen.X86_64.Search
