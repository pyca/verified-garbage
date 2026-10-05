import VerifiedGarbage.Spec.Ecdsa.Generic
import VerifiedGarbage.Spec.P224

/-!
# ECDSA over P-224: the contracts, on every target

**Trusted** (as every file in `Spec/`). The `Instance` of P-224
(`Spec/P224.lean`): `vg_ecdsa_p224_sign`, in the module `ecdsa_p224`.
-/

namespace VG.Spec.Ecdsa.P224

/-- P-224. -/
def inst : Instance where
  curve := Spec.P224.curve
  name := "p224"
  title := "P-224"

/-- `vg_ecdsa_p224_sign` on every target. -/
def signApi : Api := inst.signApi

end VG.Spec.Ecdsa.P224
