module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.X25519.Contract
import VerifiedGarbage.Proof.X25519.Arm.Verified
import VerifiedGarbage.Proof.X25519.Arm.Base
import VerifiedGarbage.Proof.X25519.Arm.Exchange
import VerifiedGarbage.Impl.X25519.Arm.Exchange
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Variants.Ed25519Field.Arm
import VerifiedGarbage.Proof.X25519.Arm.Lit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # X25519 (RFC 7748) on ARMv7 -/

namespace VG.Artifacts.X25519.Arm

public def artifacts : List (Artifact Arm.target) := [
  Spec.X25519.exchangeApi.artifact Arm.target {
    code := Impl.X25519.Arm.Fn.exchange
    verified := Proof.X25519.Arm.Fn.exchange },
  Spec.X25519.exchangeApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.X25519.Arm.Fn.exchangeUmaal
    verified := Proof.X25519.Arm.Fn.exchangeUmaal }] ++
  VG.Proof.Variants.Ed25519Field.Arm.variants.map fun (v : Proof.Variants.Ed25519Field.Arm.Variant) =>
    Spec.X25519.x25519BaseApi.artifact Arm.target {
      suffix := v.suffix
      code := Impl.X25519.Arm.Fn.x25519Base v.umaal
      verified := Proof.X25519.Arm.Fn.x25519Base v.umaal }

spec_apis artifacts

end VG.Artifacts.X25519.Arm
