module

public import VerifiedGarbage.Proof.X25519.Arm.Verified
public import VerifiedGarbage.Proof.X25519.Arm.Base
public import VerifiedGarbage.Proof.X25519.Arm.Exchange
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.Variants.Ed25519Field.Arm
import VerifiedGarbage.Proof.X25519.Arm.Lit

/-! # X25519 (RFC 7748) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.X25519.Arm

def artifacts : List Artifact := [
  Spec.X25519.exchangeApi.artifact Arm.target {
    code := Impl.Xdh.Arm.exchange "vg_x25519" Impl.X25519.Arm.x25519 32
    verified := .unscrubbed Proof.X25519.Arm.Exchange.exchange_baseline },
  Spec.X25519.exchangeApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.Xdh.Arm.exchange "vg_x25519_umaal" Impl.X25519.Arm.Words.x25519Umaal 32
    verified := .unscrubbed Proof.X25519.Arm.Exchange.exchange_umaal }] ++
  VG.Proof.Variants.Ed25519Field.Arm.variants.map fun (v : Proof.Variants.Ed25519Field.Arm.Variant) =>
    Spec.X25519.x25519BaseApi.artifact Arm.target (Proof.X25519.Arm.Base.x25519BaseReg v.umaal v.suffix)

end VG.Artifacts.X25519.Arm
