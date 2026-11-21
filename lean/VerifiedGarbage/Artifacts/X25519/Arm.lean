module

public import VerifiedGarbage.Proof.X25519.Arm.Verified
public import VerifiedGarbage.Proof.X25519.Arm.Base
public import VerifiedGarbage.Proof.X25519.Arm.Exchange
public import VerifiedGarbage.Impl.X25519.Arm.Exchange
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.Variants.Ed25519Field.Arm
import VerifiedGarbage.Proof.X25519.Arm.Lit

/-! # X25519 (RFC 7748) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.X25519.Arm

def artifacts : List Artifact := [
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

end VG.Artifacts.X25519.Arm
