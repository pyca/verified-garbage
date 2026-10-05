import VerifiedGarbage.Spec.Ecdsa.Generic
import VerifiedGarbage.Spec.P192

/-!
# ECDSA over P-192: the contracts, on every target

**Trusted** (as every file in `Spec/`). The `Instance` of P-192
(`Spec/P192.lean`): `vg_ecdsa_p192_sign`, in the module `ecdsa_p192`.
-/

namespace VG.Spec.Ecdsa.P192

/-- P-192. -/
def inst : Instance where
  curve := Spec.P192.curve
  name := "p192"
  title := "P-192"

/-- `vg_ecdsa_p192_sign` on every target. -/
def signApi : Api := inst.signApi

end VG.Spec.Ecdsa.P192
