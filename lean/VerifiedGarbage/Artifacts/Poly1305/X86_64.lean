module

public import VerifiedGarbage.Proof.Poly1305.X86_64.Init
import VerifiedGarbage.Proof.Poly1305.X86_64.Lit
public import VerifiedGarbage.Proof.Poly1305.X86_64.Ifma.Blocks
public import VerifiedGarbage.Proof.Poly1305.X86_64.Frame
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Lit
import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Lit
import VerifiedGarbage.Proof.Poly1305.X86_64.Ifma.Lit

/-! # Poly1305 (RFC 8439 §2.5) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Poly1305.X86_64

def artifacts : List Artifact := [
  Spec.Poly1305.initApi.artifact X86_64.target {
    code := Impl.Poly1305.X86_64.init
    verified := Proof.Poly1305.X86_64.init_verified },
  Spec.Poly1305.finalizeApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratch 136 .rcx Impl.Poly1305.X86_64.finalize
    stack := 136
    verified := Proof.Poly1305.X86_64.finalize_framed }]

end VG.Artifacts.Poly1305.X86_64
