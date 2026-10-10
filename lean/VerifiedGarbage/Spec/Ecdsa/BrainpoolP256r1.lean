module

public import VerifiedGarbage.Spec.Ecdsa.Generic
public import VerifiedGarbage.Spec.BrainpoolP256r1

/-!
# ECDSA over brainpoolP256r1: the contracts, on every target

**Trusted** (as every file in `Spec/`). The `Instance` of brainpoolP256r1
(`Spec/BrainpoolP256r1.lean`): `vg_ecdsa_brainpoolp256r1_sign`, in the module `ecdsa_brainpoolp256r1`.
-/

@[expose] public section

namespace VG.Spec.Ecdsa.BrainpoolP256r1

/-- brainpoolP256r1. -/
def inst : Instance where
  curve := Spec.BrainpoolP256r1.curve
  name := "brainpoolp256r1"
  title := "brainpoolP256r1"

/-- `vg_ecdsa_brainpoolp256r1_sign` on every target. -/
def signApi : Api := inst.signApi

end VG.Spec.Ecdsa.BrainpoolP256r1
