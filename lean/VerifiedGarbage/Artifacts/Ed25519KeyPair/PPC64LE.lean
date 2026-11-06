module

public import VerifiedGarbage.Proof.Ed25519.PPC64LE.KeyPair
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # Ed25519 key-pair derivation from the seed on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Ed25519KeyPair.PPC64LE

def artifacts : List Artifact := [
  Spec.Ed25519.keyPairApi.artifact PPC64LE.target {
    consts := Impl.Ed25519.PPC64LE.combConsts
    code := Impl.Ed25519.PPC64LE.KeyPair.keyPair Spec.Sha512.digest512Api.name
      Proof.Ed25519.PPC64LE.KeyPair.dgCode "vg_ed25519_public_key_expanded"
      Impl.Ed25519.PPC64LE.Whole.publicKeyExpandedCode
    stack := 768
    verified := Proof.Ed25519.PPC64LE.KeyPair.verified }]

end VG.Artifacts.Ed25519KeyPair.PPC64LE
