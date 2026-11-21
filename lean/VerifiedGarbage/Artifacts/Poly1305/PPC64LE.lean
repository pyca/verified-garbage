module

public import VerifiedGarbage.Proof.Poly1305.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # Poly1305 (RFC 8439 §2.5) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Poly1305.PPC64LE

def artifacts : List Artifact := [
  Spec.Poly1305.initApi.artifact PPC64LE.target {
    code := Impl.Poly1305.PPC64LE.Fn.init
    verified := Proof.Poly1305.PPC64LE.Scrub.init_scrubbed },
  Spec.Poly1305.updateApi.artifact PPC64LE.target {
    code := Impl.Poly1305.PPC64LE.Fn.update
    verified := Proof.Poly1305.PPC64LE.Scrub.update_scrubbed },
  Spec.Poly1305.finalizeApi.artifact PPC64LE.target {
    code := Impl.Poly1305.PPC64LE.Fn.finalize
    verified := Proof.Poly1305.PPC64LE.Scrub.finalize_scrubbed }]

end VG.Artifacts.Poly1305.PPC64LE
