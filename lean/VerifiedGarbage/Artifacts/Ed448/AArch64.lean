module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Impl.Ed448.AArch64.PublicKey
import VerifiedGarbage.Impl.Ed448.AArch64.SignCached
import VerifiedGarbage.Impl.Ed448.AArch64.Verify
import VerifiedGarbage.Proof.Ed448.AArch64.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Variants.Keccak.AArch64
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Ed448 (RFC 8032) on AArch64 -/

namespace VG.Artifacts.Ed448.AArch64

public def artifacts : List (Artifact AArch64.target) :=
  (VG.Proof.Variants.Keccak.AArch64.variants.map fun v =>
    Spec.Ed448.publicKeyApi.artifact AArch64.target {
      suffix := v.callee.suffix
      vendor := v.vendor
      code := Impl.Ed448.AArch64.Fn.publicKey v.callee
      verified := Proof.Ed448.AArch64.Fn.publicKey v }) ++
  (VG.Proof.Variants.Keccak.AArch64.variants.map fun v =>
    Spec.Ed448.signCachedApi.artifact AArch64.target {
      suffix := v.callee.suffix
      vendor := v.vendor
      code := Impl.Ed448.AArch64.Fn.signCached v.callee
      verified := Proof.Ed448.AArch64.Fn.signCached v }) ++
  (VG.Proof.Variants.Keccak.AArch64.variants.map fun v =>
    Spec.Ed448.verifyApi.artifact AArch64.target {
      suffix := v.callee.suffix
      vendor := v.vendor
      code := Impl.Ed448.AArch64.Fn.verify v.callee
      verified := Proof.Ed448.AArch64.Fn.verify v })

spec_apis artifacts

end VG.Artifacts.Ed448.AArch64
