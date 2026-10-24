module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.AttemptVerified
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeVerified
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SearchProof.Verified
public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMont

/-! The public cached APIs share the existing eight-limb product and dedicated square backend. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Proof.Bignum.AArch64

def cachedAttempt : SearchProof.Attempt :=⟨Mont.productEight,by decide +kernel⟩

def cachedSearch : Prog isa :=Impl.Ffdh.AArch64.Cached.Search.code cachedAttempt.call

theorem cachedSearch_verified : Verified target cachedSearch (Spec.Ffdh.cachedKeySearchContract abi 64) :=
 SearchProof.key_verified cachedAttempt

end VG.Proof.Ffdh.AArch64.Cached
