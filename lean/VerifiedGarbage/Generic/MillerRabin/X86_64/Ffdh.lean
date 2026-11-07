module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print

/-! # Emit FFDH parameter search for every shared arithmetic backend -/

@[expose] public section

namespace VG.Generic.MillerRabin.X86_64.Ffdh

def artifacts (v : Proof.MillerRabin.X86_64.RoundImpl) : List Artifact := [
  Spec.Ffdh.sievedParameterSearchApi.artifact X86_64.target {
    suffix := v.suffix
    stack := 160
    code := Proof.Ffdh.X86_64.Generation.searchCode v
    verified := Proof.Ffdh.X86_64.Generation.search_verified v
    spSafe := Proof.Ffdh.X86_64.Generation.searchCode_sp v
    features := v.features }]

end VG.Generic.MillerRabin.X86_64.Ffdh
