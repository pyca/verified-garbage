module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SharedChecker
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Domain validation shared by every x86-64 parameter generation -/

@[expose] public section
namespace VG.Artifacts.DsaGenerationCheck.X86_64
open VG VG.Proof.Dsa.X86_64.Generation

def artifacts : List Artifact :=
  [(Spec.Dsa.generationCheckApi).artifact X86_64.target {
    code := SharedChecker.code
    verified := SharedChecker.verified
    spSafe := SharedChecker.safe.sp }]

end VG.Artifacts.DsaGenerationCheck.X86_64
