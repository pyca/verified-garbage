module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Poly1305.Contract
import VerifiedGarbage.Proof.Poly1305.X86.Scrub
import VerifiedGarbage.Impl.Poly1305.X86
import VerifiedGarbage.Proof.Poly1305.X86.Lit
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Poly1305 (RFC 8439 §2.5) on x86 -/

namespace VG.Artifacts.Poly1305.X86

public def artifacts : List (Artifact X86.target) := [
  Spec.Poly1305.initApi.artifact X86.target {
    code := Impl.Poly1305.X86.Fn.init
    verified := Proof.Poly1305.X86.Scrub.init_scrubbed },
  Spec.Poly1305.updateApi.artifact X86.target {
    code := Impl.Poly1305.X86.Fn.update
    verified := Proof.Poly1305.X86.Scrub.update_scrubbed },
  Spec.Poly1305.finalizeApi.artifact X86.target {
    code := Impl.Poly1305.X86.Fn.finalize
    verified := Proof.Poly1305.X86.Scrub.finalize_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Poly1305.X86
