module

public import VerifiedGarbage.Proof.Poly1305.X86.Init
import VerifiedGarbage.Proof.Poly1305.X86.Lit
public import VerifiedGarbage.Proof.Poly1305.X86.Frame
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Poly1305 (RFC 8439 §2.5) on x86 -/

@[expose] public section

namespace VG.Artifacts.Poly1305.X86

def artifacts : List Artifact := [
  Spec.Poly1305.initApi.artifact X86.target {
    code := Impl.Poly1305.X86.init
    verified := Proof.Poly1305.X86.init_verified },
  Spec.Poly1305.updateApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratch 156 5 Impl.Poly1305.X86.update
    stack := 156
    verified := Proof.Poly1305.X86.update_framed },
  Spec.Poly1305.finalizeApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratch 152 4 Impl.Poly1305.X86.finalize
    stack := 152
    verified := Proof.Poly1305.X86.finalize_framed }]

end VG.Artifacts.Poly1305.X86
