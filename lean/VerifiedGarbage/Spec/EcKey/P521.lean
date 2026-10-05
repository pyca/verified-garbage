import VerifiedGarbage.Spec.EcKey.Generic
import VerifiedGarbage.Spec.P521

/-!
# P-521 keys: the contracts, on every target

**Trusted** (as every file in `Spec/`). The `Instance` of P-521
(`Spec/P521.lean`): `vg_ec_p521_public_key`, in the module `ec_p521`.
-/

namespace VG.Spec.EcKey.P521

/-- P-521. -/
def inst : Instance where
  curve := Spec.P521.curve
  name := "p521"
  title := "P-521"

/-- `vg_ec_p521_public_key` on every target. -/
def publicKeyApi : Api := inst.publicKeyApi

end VG.Spec.EcKey.P521
