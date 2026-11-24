module

public import VerifiedGarbage.Impl.Dsa.X86_64.Fn
public import VerifiedGarbage.Proof.Dsa.X86_64.ParameterSearchInitScrub
public import VerifiedGarbage.Proof.Dsa.X86_64.BackendScrub
public import VerifiedGarbage.Proof.Dsa.X86_64.Slots
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchScrub
public import VerifiedGarbage.Proof.Variants.DsaArithmetic.X86_64
public import VerifiedGarbage.Proof.Variants.MillerRabin.X86_64
public import VerifiedGarbage.Proof.Framework.QualifiedName
public import VerifiedGarbage.TCB.X86_64.Target

/-! # DSA (FIPS 186-4) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Dsa.X86_64

def direct : List (Artifact X86_64.target) := [
  Spec.Dsa.parameterInitApi.artifact X86_64.target { code := Impl.Dsa.X86_64.Fn.parameterInit, verified := Proof.Dsa.X86_64.ParameterSearchInit.init_scrubbed, spSafe := Proof.Dsa.X86_64.ParameterSearchInit.init_spSafe }]

end VG.Artifacts.Dsa.X86_64

namespace VG.Artifacts.Dsa.X86_64

open VG.Proof.Dsa.X86_64

def artifacts : List (Artifact X86_64.target) :=
  direct ++
  (VG.Proof.Variants.DsaArithmetic.X86_64.variants.flatMap fun (a : Proof.Dsa.X86_64.Slots.SlotBackend) => [
    Spec.Dsa.randomSignPrevalidatedApi.artifact X86_64.target {
      suffix := a.backend.suffix
      code := Impl.Dsa.X86_64.Fn.randomSignPrevalidatedS a.backend.level (prevalidatedSignerName a.backend) a.nm a.ns
        a.bm a.bs
      verified := Proof.Dsa.X86_64.BackendScrub.randomSign_scrubbed a
      spSafe := Proof.Dsa.X86_64.BackendScrub.randomSign_spSafe a },
    Spec.Dsa.validatePrivateKeyApi.artifact X86_64.target {
      suffix := a.backend.suffix
      code := Impl.Dsa.X86_64.Fn.validatePrivateKeyS a.backend.level a.nm a.ns a.bm a.bs
      verified := Proof.Dsa.X86_64.Slots.validatePrivate_scrubbed a
      spSafe := Proof.Dsa.X86_64.Slots.validatePrivate_spSafe a },
    Spec.Dsa.validatePublicKeyApi.artifact X86_64.target {
      suffix := a.backend.suffix
      code := Impl.Dsa.X86_64.Fn.validatePublicKeyS a.backend.level a.nm a.ns a.bm a.bs
      verified := Proof.Dsa.X86_64.Slots.validatePublic_scrubbed a
      spSafe := Proof.Dsa.X86_64.Slots.validatePublic_spSafe a },
    Spec.Dsa.verifyPrevalidatedApi.artifact X86_64.target {
      suffix := a.backend.suffix
      code := Impl.Dsa.X86_64.Fn.verifyPrevalidatedS a.backend.level a.nm a.ns a.bm a.bs
      verified := Proof.Dsa.X86_64.Slots.verify_scrubbed a
      spSafe := Proof.Dsa.X86_64.Slots.verify_spSafe a },
    Spec.Dsa.generateKeyApi.artifact X86_64.target {
      suffix := a.backend.suffix
      code := Impl.Dsa.X86_64.Fn.generateKeyS a.backend.level (keygenCheckName a.backend) (keygenDeriveName a.backend)
        a.nm a.ns a.bm a.bs
      verified := Proof.Dsa.X86_64.BackendScrub.generateKey_scrubbed a
      spSafe := Proof.Dsa.X86_64.BackendScrub.generateKey_spSafe a },
    Spec.Dsa.deriveKeyApi.artifact X86_64.target {
      suffix := a.backend.suffix
      code := Impl.Dsa.X86_64.Fn.deriveKeyS a.backend.level a.nm a.ns a.bm a.bs
      verified := Proof.Dsa.X86_64.Slots.deriveKey_scrubbed a
      spSafe := Proof.Dsa.X86_64.Slots.deriveKey_spSafe a }]) ++
  (Generation.RefillBackend.hashPairs.flatMap fun (p : Generation.RefillBackend.Hashes) =>
    VG.Proof.Variants.MillerRabin.X86_64.variants.map fun (v : Proof.MillerRabin.X86_64.RoundImpl) =>
    Spec.Dsa.parameterSearchApi.artifact X86_64.target {
      suffix := qualifiedName "" [("sha1", p.sha1.suffix), ("sha256", p.sha256.suffix), ("mr", v.suffix)]
      code := Impl.Dsa.X86_64.Fn.parameterSearch (Proof.Dsa.X86_64.Generation.SearchScrub.level p v)
        (Generation.RefillBackend.addrs p.sha1 v) (Generation.RefillBackend.addrs p.sha256 v)
        (Generation.RefillBackend.addrs p.sha256 v) (Generation.RefillBackend.name 128)
        (Generation.RefillBackend.name 256) (Generation.RefillBackend.name 384) (Generation.RefillBackend.body p.sha1 v 128)
        (Generation.RefillBackend.body p.sha256 v 256) (Generation.RefillBackend.body p.sha256 v 384)
      verified := Proof.Dsa.X86_64.Generation.SearchScrub.search_scrubbed p v
      spSafe := Proof.Dsa.X86_64.Generation.SearchScrub.search_spSafe p v })

end VG.Artifacts.Dsa.X86_64
