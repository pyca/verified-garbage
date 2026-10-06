import VerifiedGarbage.Spec.EcKey.Generic
import VerifiedGarbage.Spec.BrainpoolP384r1

/-!
# brainpoolP384r1 keys: the contracts, on every target

**Trusted** (as every file in `Spec/`). The `Instance` of brainpoolP384r1
(`Spec/BrainpoolP384r1.lean`): `vg_ec_brainpoolp384r1_public_key`, in the module `ec_brainpoolp384r1`.
-/

namespace VG.Spec.EcKey.BrainpoolP384r1

/-- brainpoolP384r1. -/
def inst : Instance where
  curve := Spec.BrainpoolP384r1.curve
  name := "brainpoolp384r1"
  title := "brainpoolP384r1"

/-- `vg_ec_brainpoolp384r1_public_key` on every target. -/
def publicKeyApi : Api := inst.publicKeyApi

end VG.Spec.EcKey.BrainpoolP384r1
