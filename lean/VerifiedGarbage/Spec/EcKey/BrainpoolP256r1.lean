module

public import VerifiedGarbage.Spec.EcKey.Generic
public import VerifiedGarbage.Spec.BrainpoolP256r1

/-!
# brainpoolP256r1 keys: the contracts, on every target

**Trusted** (as every file in `Spec/`). The `Instance` of brainpoolP256r1
(`Spec/BrainpoolP256r1.lean`): `vg_ec_brainpoolp256r1_public_key`, in the module `ec_brainpoolp256r1`.
-/

@[expose] public section

namespace VG.Spec.EcKey.BrainpoolP256r1

/-- brainpoolP256r1. -/
def inst : Instance where
  curve := Spec.BrainpoolP256r1.curve
  name := "brainpoolp256r1"
  title := "brainpoolP256r1"

/-- `vg_ec_brainpoolp256r1_public_key` on every target. -/
def publicKeyApi : Api := inst.publicKeyApi

end VG.Spec.EcKey.BrainpoolP256r1
