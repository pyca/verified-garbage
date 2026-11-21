module

public import VerifiedGarbage.Proof.MlKem.AArch64.Scrub
public import VerifiedGarbage.Proof.MlKem.AArch64.Residue
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Inst
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.QualifiedName
public import VerifiedGarbage.TCB.AArch64.Print

/-! # ML-KEM (FIPS 203) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.MlKem.AArch64

open VG.Proof.MlKem.AArch64.FixedHash.Inst (parts)

/-- ML-KEM-768 and ML-KEM-1024, for each pair of Keccak implementations
(`FixedHash.Inst.variants`): paired sampling and fused arithmetic, calling
the two- and three-state functions of `x2` and the single-state permutation
of `v`. -/
def artifacts : List Artifact :=
  [Spec.MlKem.checkEkApi.artifact AArch64.target {
    code := Impl.MlKem.AArch64.Fn.checkEk
    verified := Proof.MlKem.AArch64.Residue.checkEk_scrubbed }] ++
  (VG.Proof.MlKem.AArch64.FixedHash.Inst.variants.flatMap fun (x2, v) => [
    Spec.MlKem.keyGenApi.artifact AArch64.target {
      suffix := qualifiedName "" (parts x2 v)
      vendor := v.vendor
      code := Impl.MlKem.AArch64.Fn.keyGen (qualifiedName "" (parts x2 v)) x2.sha3 v.callee
      verified := Proof.MlKem.AArch64.Scrub.keyGen_scrubbed x2 v },
    Spec.MlKem.encapsApi.artifact AArch64.target {
      suffix := qualifiedName "" (parts x2 v)
      vendor := v.vendor
      code := Impl.MlKem.AArch64.Fn.encaps (qualifiedName "" (parts x2 v)) x2.sha3 v.callee
      verified := Proof.MlKem.AArch64.Scrub.encaps_scrubbed x2 v },
    Spec.MlKem.encapsHApi.artifact AArch64.target {
      suffix := qualifiedName "" (parts x2 v)
      vendor := v.vendor
      code := Impl.MlKem.AArch64.Fn.encapsH (qualifiedName "" (parts x2 v)) x2.sha3 v.callee
      verified := Proof.MlKem.AArch64.Scrub.encapsH_scrubbed x2 v },
    Spec.MlKem.decapsApi.artifact AArch64.target {
      suffix := qualifiedName "" (parts x2 v)
      vendor := v.vendor
      code := Impl.MlKem.AArch64.Fn.decaps (qualifiedName "" (parts x2 v)) x2.sha3 v.callee
      verified := Proof.MlKem.AArch64.Scrub.decaps_scrubbed x2 v },
    Spec.MlKem1024.keyGenApi.artifact AArch64.target {
      suffix := qualifiedName "" (parts x2 v)
      vendor := v.vendor
      code := Impl.MlKem.AArch64.Fn.keyGen1024 (qualifiedName "" (parts x2 v)) x2.sha3 v.callee
      verified := Proof.MlKem.AArch64.Scrub.keyGen1024_scrubbed x2 v },
    Spec.MlKem1024.encapsApi.artifact AArch64.target {
      suffix := qualifiedName "" (parts x2 v)
      vendor := v.vendor
      code := Impl.MlKem.AArch64.Fn.encaps1024 (qualifiedName "" (parts x2 v)) x2.sha3 v.callee
      verified := Proof.MlKem.AArch64.Scrub.encaps1024_scrubbed x2 v },
    Spec.MlKem1024.encapsHApi.artifact AArch64.target {
      suffix := qualifiedName "" (parts x2 v)
      vendor := v.vendor
      code := Impl.MlKem.AArch64.Fn.encapsH1024 (qualifiedName "" (parts x2 v)) x2.sha3 v.callee
      verified := Proof.MlKem.AArch64.Scrub.encapsH1024_scrubbed x2 v },
    Spec.MlKem1024.decapsApi.artifact AArch64.target {
      suffix := qualifiedName "" (parts x2 v)
      vendor := v.vendor
      code := Impl.MlKem.AArch64.Fn.decaps1024 (qualifiedName "" (parts x2 v)) x2.sha3 v.callee
      verified := Proof.MlKem.AArch64.Scrub.decaps1024_scrubbed x2 v }]) ++
  [Spec.MlKem1024.checkEkApi.artifact AArch64.target {
    code := Impl.MlKem.AArch64.Fn.checkEk1024
    verified := Proof.MlKem.AArch64.Residue.checkEk1024_scrubbed }]

end VG.Artifacts.MlKem.AArch64
