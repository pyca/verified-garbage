module

public import VerifiedGarbage.Spec.EcKey.Generic
public import VerifiedGarbage.Spec.P192

/-!
# P-192 keys: the contracts, on every target

**Trusted** (as every file in `Spec/`). The `Instance` of P-192
(`Spec/P192.lean`): `vg_ec_p192_public_key`, in the module `ec_p192`.
-/

@[expose] public section

namespace VG.Spec.EcKey.P192

/-- P-192. -/
def inst : Instance where
  curve := Spec.P192.curve
  name := "p192"
  title := "P-192"

/-- `vg_ec_p192_public_key` on every target. -/
def publicKeyApi : Api := inst.publicKeyApi

end VG.Spec.EcKey.P192
