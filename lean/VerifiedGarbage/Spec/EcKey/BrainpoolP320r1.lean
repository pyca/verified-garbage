module

public import VerifiedGarbage.Spec.EcKey.Generic
public import VerifiedGarbage.Spec.BrainpoolP320r1

/-!
# brainpoolP320r1 keys: the contracts, on every target

**Trusted** (as every file in `Spec/`). The `Instance` of brainpoolP320r1
(`Spec/BrainpoolP320r1.lean`): `vg_ec_brainpoolp320r1_public_key`, in the module `ec_brainpoolp320r1`.
-/

@[expose] public section

namespace VG.Spec.EcKey.BrainpoolP320r1

/-- brainpoolP320r1. -/
def inst : Instance where
  curve := Spec.BrainpoolP320r1.curve
  name := "brainpoolp320r1"
  title := "brainpoolP320r1"

/-- `vg_ec_brainpoolp320r1_public_key` on every target. -/
def publicKeyApi : Api := inst.publicKeyApi

end VG.Spec.EcKey.BrainpoolP320r1
