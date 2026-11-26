module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.ChaCha20Poly1305.Contract
public import VerifiedGarbage.Spec.ChaCha20Poly1305.OutOfPlace
import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ChaCha20-Poly1305 (RFC 8439 §2.8) on PPC64LE -/

namespace VG.Artifacts.ChaCha20Poly1305.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.ChaCha20Poly1305.sealApi.artifact PPC64LE.target {
    code := Impl.ChaCha20Poly1305.PPC64LE.Fn.seal
    verified := Proof.ChaCha20Poly1305.PPC64LE.Scrub.seal_scrubbed },
  Spec.ChaCha20Poly1305.openZeroApi.artifact PPC64LE.target {
    code := Impl.ChaCha20Poly1305.PPC64LE.Fn.open
    verified := Proof.ChaCha20Poly1305.PPC64LE.Scrub.open_scrubbed },
  Spec.ChaCha20Poly1305.openToApi.artifact PPC64LE.target {
    code := Impl.ChaCha20Poly1305.PPC64LE.Fn.openTo
    verified := Proof.ChaCha20Poly1305.PPC64LE.Scrub.openTo_scrubbed },
  Spec.ChaCha20Poly1305.sealGatherApi.artifact PPC64LE.target {
    code := Impl.ChaCha20Poly1305.PPC64LE.Fn.sealGather
    verified := Proof.ChaCha20Poly1305.PPC64LE.Scrub.sealGather_scrubbed }]

spec_apis artifacts

end VG.Artifacts.ChaCha20Poly1305.PPC64LE
