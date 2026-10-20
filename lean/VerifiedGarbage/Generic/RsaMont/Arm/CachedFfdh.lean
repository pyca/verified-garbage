module

public import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Contract
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyBackend
public import VerifiedGarbage.Impl.Ffdh.Arm.KeySearch
public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
public import VerifiedGarbage.Proof.Ffdh.Arm.VettedBoundInstance
public import VerifiedGarbage.Impl.Ffdh.Arm.VettedGroups
public import VerifiedGarbage.Impl.Bignum.Arm.MontCall
public import VerifiedGarbage.Proof.Ffdh.Arm.CachedKeyInstances
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeVerified
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! Cached key generation and its native controller share one RSA arithmetic helper. -/

@[expose] public section
namespace VG.Generic.RsaMont.Arm.CachedFfdh
open VG

def artifacts (v : Proof.Bignum.Arm.MontBackend) : List Artifact :=
  [Spec.Ffdh.generationPrecomputeApi.artifact VG.Arm.target {
    suffix := v.suffix
    features := v.features
    stack := 176
    consts := Impl.Ffdh.Arm.VettedGroups.tableConsts
    code := Proof.Ffdh.Arm.combPrecomputeCalledCode v
    verified := Proof.Ffdh.Arm.combPrecomputeCalled_verified v
    notes := ["ARMv7: build the canonical immutable five-tooth comb context once per domain. \
      Modulus and Montgomery constants reuse the RSA precomputation layout. \
      The exact vetted-group table selects the reviewed scalar width."] },
  Spec.Ffdh.cachedGenerateKeyApi.artifact VG.Arm.target {
    suffix := v.suffix
    features := v.features
    stack := 176
    code := (Proof.Ffdh.Arm.CachedKeyGenerate.backend v).generateKey
    verified := (Proof.Ffdh.Arm.CachedKeyGenerate.backend v).generateKey_verified
    notes := ["ARMv7: import cached modulus and Montgomery constants, mask the full-size \
      entropy draw to the reviewed width, and use a fixed five-tooth comb schedule. \
      Every secret digit scans all 32 table entries. Product and square operations \
      call the same shared RSA Montgomery helper."] },
  Spec.Ffdh.cachedKeySearchApi.artifact VG.Arm.target {
    suffix := v.suffix
    features := v.features
    stack := Proof.Ffdh.Arm.KeySearch.stackUse .cached
    code := Proof.Ffdh.Arm.KeySearch.calledCode
      (Proof.Ffdh.Arm.CachedKeyGenerate.backend v)
    verified := Proof.Ffdh.Arm.KeySearch.verified (Proof.Ffdh.Arm.CachedKeyGenerate.backend v)
    notes := ["ARMv7: the shared native retry controller calls the cached attempt, \
      retaining both rejection budgets, full-size entropy requests, and refill behavior. \
      The immutable comb context remains read-only across every attempt."] }]

end VG.Generic.RsaMont.Arm.CachedFfdh
