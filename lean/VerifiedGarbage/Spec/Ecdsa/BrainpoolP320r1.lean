module

public import VerifiedGarbage.Spec.Ecdsa.Generic
public import VerifiedGarbage.Spec.BrainpoolP320r1

/-!
# ECDSA over brainpoolP320r1: its instance

**Trusted** (as every file in `Spec/`). The `Instance` of brainpoolP320r1
(`Spec/BrainpoolP320r1.lean`), for the functions of the module `ecdsa_brainpoolp320r1`.
-/

@[expose] public section

namespace VG.Spec.Ecdsa.BrainpoolP320r1

/-- brainpoolP320r1. -/
def inst : Instance where
  curve := Spec.BrainpoolP320r1.curve
  name := "brainpoolp320r1"
  title := "brainpoolP320r1"

end VG.Spec.Ecdsa.BrainpoolP320r1
