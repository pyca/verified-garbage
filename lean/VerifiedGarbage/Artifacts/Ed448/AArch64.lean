module

public import VerifiedGarbage.Impl.Ed448.AArch64.PublicKey
public import VerifiedGarbage.Impl.Ed448.AArch64.SignCached
public import VerifiedGarbage.Impl.Ed448.AArch64.Verify
public import VerifiedGarbage.Proof.Ed448.AArch64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Variants.Keccak.AArch64
public import VerifiedGarbage.Spec.Ed448.Contract
public import VerifiedGarbage.TCB.AArch64.Print

/-! # Ed448 (RFC 8032) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Ed448.AArch64

def artifacts : List Artifact :=
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

end VG.Artifacts.Ed448.AArch64
