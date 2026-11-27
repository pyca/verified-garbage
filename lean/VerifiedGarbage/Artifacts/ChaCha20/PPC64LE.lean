module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.ChaCha20.Contract
import VerifiedGarbage.Proof.ChaCha20.PPC64LE.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ChaCha20 (RFC 8439) on PPC64LE -/

namespace VG.Artifacts.ChaCha20.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.ChaCha20.initApi.artifact PPC64LE.target {
    code := Impl.ChaCha20.PPC64LE.Fn.init
    verified := Proof.ChaCha20.PPC64LE.Scrub.init_scrubbed },
  Spec.ChaCha20.setNonceApi.artifact PPC64LE.target {
    code := Impl.ChaCha20.PPC64LE.Fn.setNonce
    verified := Proof.ChaCha20.PPC64LE.Scrub.setNonce_scrubbed },
  Spec.ChaCha20.applyApi.artifact PPC64LE.target {
    code := Impl.ChaCha20.PPC64LE.Fn.apply
    verified := Proof.ChaCha20.PPC64LE.Scrub.apply_scrubbed }]

spec_apis artifacts

end VG.Artifacts.ChaCha20.PPC64LE
