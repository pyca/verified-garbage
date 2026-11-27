module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Poly1305.Contract
import VerifiedGarbage.Proof.Poly1305.PPC64LE.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Poly1305 (RFC 8439 §2.5) on PPC64LE -/

namespace VG.Artifacts.Poly1305.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Poly1305.initApi.artifact PPC64LE.target {
    code := Impl.Poly1305.PPC64LE.Fn.init
    verified := Proof.Poly1305.PPC64LE.Scrub.init_scrubbed },
  Spec.Poly1305.updateApi.artifact PPC64LE.target {
    code := Impl.Poly1305.PPC64LE.Fn.update
    verified := Proof.Poly1305.PPC64LE.Scrub.update_scrubbed },
  Spec.Poly1305.finalizeApi.artifact PPC64LE.target {
    code := Impl.Poly1305.PPC64LE.Fn.finalize
    verified := Proof.Poly1305.PPC64LE.Scrub.finalize_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Poly1305.PPC64LE
