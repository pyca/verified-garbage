module

public import VerifiedGarbage.Proof.Ed25519.Arm.KeyPair
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # Ed25519 key-pair derivation from the seed on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Ed25519KeyPair.Arm

def artifacts : List Artifact := [
  Spec.Ed25519.keyPairApi.artifact Arm.target {
    consts := Impl.Ed25519.Arm.combConsts
    code := Impl.Ed25519.Arm.KeyPair.keyPair Spec.Sha512.digest512Api.name
      Proof.Ed25519.Arm.KeyPair.dgCode "vg_ed25519_public_key_expanded"
      Impl.Ed25519.Arm.PublicKey.codeExpanded
    stack := 600
    verified := Proof.Ed25519.Arm.KeyPair.verified }]

end VG.Artifacts.Ed25519KeyPair.Arm
