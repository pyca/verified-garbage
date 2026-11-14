module

public import VerifiedGarbage.Proof.Ed25519.PPC64LE.KeyPair
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.SignVerified
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.VerifyMsgVerified

/-! # Ed25519 (RFC 8032) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Ed25519.PPC64LE

def artifacts : List Artifact := [
  Spec.Ed25519.keyPairApi.artifact PPC64LE.target {
    code := Impl.Ed25519.PPC64LE.KeyPair.keyPair Spec.Sha512.digest512Api.name
      Proof.Ed25519.PPC64LE.KeyPair.dgCode "vg_ed25519_public_key_expanded"
      Impl.Ed25519.PPC64LE.Whole.publicKeyExpandedCode
    stack := 768
    verified := Proof.Ed25519.PPC64LE.KeyPair.verified },
  Spec.Ed25519.signExpandedApi.artifact PPC64LE.target {
    code := Impl.Ed25519.PPC64LE.Whole.signExpandedCode
    stack := 368
    verified := Proof.Ed25519.PPC64LE.Whole.signExpanded_framed },
  Spec.Ed25519.verifyApi.artifact PPC64LE.target {
    code := Impl.Ed25519.PPC64LE.Whole.verifyCode
    stack := 272
    verified := Proof.Ed25519.PPC64LE.Whole.verify_framed }]

end VG.Artifacts.Ed25519.PPC64LE
