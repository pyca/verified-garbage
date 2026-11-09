module

public import VerifiedGarbage.Proof.Ed25519.Arm.KeyPair
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.Ed25519.Arm.SignCached.Expanded
public import VerifiedGarbage.Proof.Ed25519.Arm.VerifyMessage.Verified

/-! # Ed25519 (RFC 8032) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Ed25519.Arm

def artifacts : List Artifact := [
  Spec.Ed25519.keyPairApi.artifact Arm.target {
    code := Impl.Ed25519.Arm.KeyPair.keyPair Spec.Sha512.digest512Api.name
      Proof.Ed25519.Arm.KeyPair.dgCode "vg_ed25519_public_key_expanded"
      Impl.Ed25519.Arm.PublicKey.codeExpanded
    stack := 600
    verified := Proof.Ed25519.Arm.KeyPair.verified },
  Spec.Ed25519.signExpandedApi.artifact Arm.target {
    code := Impl.Ed25519.Arm.SignCached.codeExpanded
    stack := 280
    verified := Proof.Ed25519.Arm.SignCached.signExpanded_verified },
  Spec.Ed25519.verifyApi.artifact Arm.target {
    code := Impl.Ed25519.Arm.VerifyMessage.code
    stack := 280
    verified := Proof.Ed25519.Arm.VerifyMessage.verifyMessage_verified }]

end VG.Artifacts.Ed25519.Arm
