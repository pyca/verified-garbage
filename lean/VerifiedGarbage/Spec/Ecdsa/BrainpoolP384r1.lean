module

public import VerifiedGarbage.Spec.Ecdsa.Generic
public import VerifiedGarbage.Spec.BrainpoolP384r1

/-!
# ECDSA over brainpoolP384r1: the contracts, on every target

**Trusted** (as every file in `Spec/`). The `Instance` of brainpoolP384r1
(`Spec/BrainpoolP384r1.lean`): `vg_ecdsa_brainpoolp384r1_sign`, in the module `ecdsa_brainpoolp384r1`.
-/

@[expose] public section

namespace VG.Spec.Ecdsa.BrainpoolP384r1

/-- brainpoolP384r1. -/
def inst : Instance where
  curve := Spec.BrainpoolP384r1.curve
  name := "brainpoolp384r1"
  title := "brainpoolP384r1"

/-- `vg_ecdsa_brainpoolp384r1_sign` on every target. -/
def signApi : Api := inst.signApi

end VG.Spec.Ecdsa.BrainpoolP384r1
