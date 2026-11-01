module

public import VerifiedGarbage.Spec.Ecdsa.Generic
public import VerifiedGarbage.Spec.BrainpoolP512r1

/-!
# ECDSA over brainpoolP512r1: its instance

**Trusted** (as every file in `Spec/`). The `Instance` of brainpoolP512r1
(`Spec/BrainpoolP512r1.lean`), for the functions of the module `ecdsa_brainpoolp512r1`.
-/

@[expose] public section

namespace VG.Spec.Ecdsa.BrainpoolP512r1

/-- brainpoolP512r1. -/
def inst : Instance where
  curve := Spec.BrainpoolP512r1.curve
  name := "brainpoolp512r1"
  title := "brainpoolP512r1"

end VG.Spec.Ecdsa.BrainpoolP512r1
