import VerifiedGarbage.Spec.EcKey.Generic
import VerifiedGarbage.Spec.Secp256k1

/-!
# secp256k1 keys: the contracts, on every target

**Trusted** (as every file in `Spec/`). The `Instance` of secp256k1
(`Spec/Secp256k1.lean`): `vg_ec_secp256k1_public_key`, in the module
`ec_secp256k1`.
-/

namespace VG.Spec.EcKey.Secp256k1

/-- secp256k1. -/
def inst : Instance where
  curve := Spec.Secp256k1.curve
  name := "secp256k1"
  title := "secp256k1"

/-- `vg_ec_secp256k1_public_key` on every target. -/
def publicKeyApi : Api := inst.publicKeyApi

end VG.Spec.EcKey.Secp256k1
