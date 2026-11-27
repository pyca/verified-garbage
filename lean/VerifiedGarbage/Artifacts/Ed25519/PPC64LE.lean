module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ed25519.KeyPair
public import VerifiedGarbage.Spec.Ed25519.ExpandedSign
public import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Proof.Ed25519.PPC64LE.KeyPair
import VerifiedGarbage.Proof.Ed25519.PPC64LE.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.SignVerified
import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.VerifyMsgVerified
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Ed25519 (RFC 8032) on PPC64LE -/

namespace VG.Artifacts.Ed25519.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Ed25519.keyPairApi.artifact PPC64LE.target {
    code := Impl.Ed25519.PPC64LE.Fn.keyPair
    verified := Proof.Ed25519.PPC64LE.Scrub.keyPair_scrubbed },
  Spec.Ed25519.signExpandedApi.artifact PPC64LE.target {
    code := Impl.Ed25519.PPC64LE.Fn.signExpanded
    verified := Proof.Ed25519.PPC64LE.Scrub.signExpanded_scrubbed },
  Spec.Ed25519.verifyApi.artifact PPC64LE.target {
    code := Impl.Ed25519.PPC64LE.Fn.verify
    verified := Proof.Ed25519.PPC64LE.Scrub.verify_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Ed25519.PPC64LE
