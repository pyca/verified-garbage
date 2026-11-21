module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Spec.ChaCha20Poly1305.OutOfPlace

/-! # ChaCha20-Poly1305 (RFC 8439 §2.8) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.ChaCha20Poly1305.PPC64LE

def artifacts : List Artifact := [
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

end VG.Artifacts.ChaCha20Poly1305.PPC64LE
