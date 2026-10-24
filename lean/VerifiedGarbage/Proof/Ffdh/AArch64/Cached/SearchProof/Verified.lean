module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SearchProof.Contract
public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Search
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SearchProof.CT
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SearchProof.Implies
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SearchProof.Correct

/-! The complete cached rejection search satisfies the reviewed public API. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached.SearchProof
open VG VG.AArch64

theorem key_verified (a : Attempt) :
 Verified target (Impl.Ffdh.AArch64.Cached.Search.code a.call) (Spec.Ffdh.cachedKeySearchContract abi stackUse) :=
 Verified.of_correct (key_correct a) (key_constantTime a) key_implies

end VG.Proof.Ffdh.AArch64.Cached.SearchProof
