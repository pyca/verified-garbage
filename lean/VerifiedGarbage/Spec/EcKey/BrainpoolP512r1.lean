import VerifiedGarbage.Spec.EcKey.Generic
import VerifiedGarbage.Spec.BrainpoolP512r1

/-!
# brainpoolP512r1 keys: the contracts, on every target

**Trusted** (as every file in `Spec/`). The `Instance` of brainpoolP512r1
(`Spec/BrainpoolP512r1.lean`): `vg_ec_brainpoolp512r1_public_key`, in the module `ec_brainpoolp512r1`.
-/

namespace VG.Spec.EcKey.BrainpoolP512r1

/-- brainpoolP512r1. -/
def inst : Instance where
  curve := Spec.BrainpoolP512r1.curve
  name := "brainpoolp512r1"
  title := "brainpoolP512r1"

/-- `vg_ec_brainpoolp512r1_public_key` on every target. -/
def publicKeyApi : Api := inst.publicKeyApi

end VG.Spec.EcKey.BrainpoolP512r1
