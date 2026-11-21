module

public import VerifiedGarbage.Proof.ChaCha20.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # ChaCha20 (RFC 8439) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.ChaCha20.PPC64LE

def artifacts : List Artifact := [
  Spec.ChaCha20.initApi.artifact PPC64LE.target {
    code := Impl.ChaCha20.PPC64LE.Fn.init
    verified := Proof.ChaCha20.PPC64LE.Scrub.init_scrubbed },
  Spec.ChaCha20.setNonceApi.artifact PPC64LE.target {
    code := Impl.ChaCha20.PPC64LE.Fn.setNonce
    verified := Proof.ChaCha20.PPC64LE.Scrub.setNonce_scrubbed },
  Spec.ChaCha20.applyApi.artifact PPC64LE.target {
    code := Impl.ChaCha20.PPC64LE.Fn.apply
    verified := Proof.ChaCha20.PPC64LE.Scrub.apply_scrubbed }]

end VG.Artifacts.ChaCha20.PPC64LE
