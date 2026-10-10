module

public import VerifiedGarbage.Spec.Ecdsa.Generic
public import VerifiedGarbage.Spec.BrainpoolP512r1

/-!
# ECDSA over brainpoolP512r1: the contracts, on every target

**Trusted** (as every file in `Spec/`). The `Instance` of brainpoolP512r1
(`Spec/BrainpoolP512r1.lean`): `vg_ecdsa_brainpoolp512r1_sign`, in the module `ecdsa_brainpoolp512r1`.
-/

@[expose] public section

namespace VG.Spec.Ecdsa.BrainpoolP512r1

/-- brainpoolP512r1. -/
def inst : Instance where
  curve := Spec.BrainpoolP512r1.curve
  name := "brainpoolp512r1"
  title := "brainpoolP512r1"

/-- `vg_ecdsa_brainpoolp512r1_sign` on every target. -/
def signApi : Api := inst.signApi

end VG.Spec.Ecdsa.BrainpoolP512r1
