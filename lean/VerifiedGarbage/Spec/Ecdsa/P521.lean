import VerifiedGarbage.Spec.Ecdsa.Generic
import VerifiedGarbage.Spec.P521

/-!
# ECDSA over P-521: the contracts, on every target

**Trusted** (as every file in `Spec/`). The `Instance` of P-521
(`Spec/P521.lean`): `vg_ecdsa_p521_sign`, in the module `ecdsa_p521`.
-/

namespace VG.Spec.Ecdsa.P521

/-- P-521. -/
def inst : Instance where
  curve := Spec.P521.curve
  name := "p521"
  title := "P-521"

/-- `vg_ecdsa_p521_sign` on every target. -/
def signApi : Api := inst.signApi

end VG.Spec.Ecdsa.P521
