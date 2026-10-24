module

public import VerifiedGarbage.Spec.Dsa.Derive

/-! # A shared domain-check entry point for parameter generation

This helper has exactly the existing domain check's signature, contract,
outputs, scratch requirements and permitted leakage. A separate name lets
generation share its validation body independently of public-check backends.
-/

@[expose] public section
namespace VG.Spec.Dsa

def generationCheckApi : Api :=
  { checkParametersApi with name := "vg_dsa_generation_check_parameters" }

end VG.Spec.Dsa
