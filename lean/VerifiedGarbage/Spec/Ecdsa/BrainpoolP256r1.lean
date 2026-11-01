module

public import VerifiedGarbage.Spec.Ecdsa.Generic
public import VerifiedGarbage.Spec.BrainpoolP256r1

/-!
# ECDSA over brainpoolP256r1: its instance

**Trusted** (as every file in `Spec/`). The `Instance` of brainpoolP256r1
(`Spec/BrainpoolP256r1.lean`), for the functions of the module `ecdsa_brainpoolp256r1`.
-/

@[expose] public section

namespace VG.Spec.Ecdsa.BrainpoolP256r1

/-- brainpoolP256r1. -/
def inst : Instance where
  curve := Spec.BrainpoolP256r1.curve
  name := "brainpoolp256r1"
  title := "brainpoolP256r1"

end VG.Spec.Ecdsa.BrainpoolP256r1
