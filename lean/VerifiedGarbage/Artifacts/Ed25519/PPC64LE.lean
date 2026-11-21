module

public import VerifiedGarbage.Proof.Ed25519.PPC64LE.KeyPair
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.SignVerified
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.VerifyMsgVerified

/-! # Ed25519 (RFC 8032) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Ed25519.PPC64LE

def artifacts : List Artifact := [
  Spec.Ed25519.keyPairApi.artifact PPC64LE.target {
    code := Impl.Ed25519.PPC64LE.Fn.keyPair
    verified := Proof.Ed25519.PPC64LE.Scrub.keyPair_scrubbed },
  Spec.Ed25519.signExpandedApi.artifact PPC64LE.target {
    code := Impl.Ed25519.PPC64LE.Fn.signExpanded
    verified := Proof.Ed25519.PPC64LE.Scrub.signExpanded_scrubbed },
  Spec.Ed25519.verifyApi.artifact PPC64LE.target {
    code := Impl.Ed25519.PPC64LE.Fn.verify
    verified := Proof.Ed25519.PPC64LE.Scrub.verify_scrubbed }]

end VG.Artifacts.Ed25519.PPC64LE
