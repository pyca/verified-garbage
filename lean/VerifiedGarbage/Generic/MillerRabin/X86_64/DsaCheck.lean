module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SharedChecker
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Domain validation shared by generation widths and hash backends -/

@[expose] public section
namespace VG.Generic.MillerRabin.X86_64.DsaCheck
open VG VG.Proof.Dsa.X86_64.Generation

def artifacts (v : Proof.MillerRabin.X86_64.RoundImpl) : List Artifact :=
  [(Spec.Dsa.generationCheckApi).artifact X86_64.target {
    suffix := SharedChecker.suffix v
    code := SharedChecker.code v
    verified := SharedChecker.verified v
    spSafe := (SharedChecker.safe v).sp
    features := v.features }]

end VG.Generic.MillerRabin.X86_64.DsaCheck
