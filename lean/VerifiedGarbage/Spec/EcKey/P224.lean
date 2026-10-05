import VerifiedGarbage.Spec.EcKey.Generic
import VerifiedGarbage.Spec.P224

/-!
# P-224 keys: the contracts, on every target

**Trusted** (as every file in `Spec/`). The `Instance` of P-224
(`Spec/P224.lean`): `vg_ec_p224_public_key`, in the module `ec_p224`.
-/

namespace VG.Spec.EcKey.P224

/-- P-224. -/
def inst : Instance where
  curve := Spec.P224.curve
  name := "p224"
  title := "P-224"

/-- `vg_ec_p224_public_key` on every target. -/
def publicKeyApi : Api := inst.publicKeyApi

end VG.Spec.EcKey.P224
