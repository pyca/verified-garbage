module

public import VerifiedGarbage.Spec.Ecdsa.Generic
public import VerifiedGarbage.Spec.P384

/-!
# ECDSA over P-384: the contracts, on every target

**Trusted** (as every file in `Spec/`). The `Instance` of P-384
(`Spec/P384.lean`): `vg_ecdsa_p384_sign`, in the module `ecdsa_p384`.
-/

@[expose] public section

namespace VG.Spec.Ecdsa.P384

/-- P-384. -/
def inst : Instance where
  curve := Spec.P384.curve
  name := "p384"
  title := "P-384"

/-- `vg_ecdsa_p384_sign` on every target. -/
def signApi : Api := inst.signApi

end VG.Spec.Ecdsa.P384
