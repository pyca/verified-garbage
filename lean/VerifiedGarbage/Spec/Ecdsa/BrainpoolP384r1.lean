module

public import VerifiedGarbage.Spec.Ecdsa.Generic
public import VerifiedGarbage.Spec.BrainpoolP384r1

/-!
# ECDSA over brainpoolP384r1: its instance

**Trusted** (as every file in `Spec/`). The `Instance` of brainpoolP384r1
(`Spec/BrainpoolP384r1.lean`), for the functions of the module `ecdsa_brainpoolp384r1`.
-/

@[expose] public section

namespace VG.Spec.Ecdsa.BrainpoolP384r1

/-- brainpoolP384r1. -/
def inst : Instance where
  curve := Spec.BrainpoolP384r1.curve
  name := "brainpoolp384r1"
  title := "brainpoolP384r1"

end VG.Spec.Ecdsa.BrainpoolP384r1
