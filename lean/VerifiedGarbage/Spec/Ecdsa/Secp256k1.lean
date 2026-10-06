import VerifiedGarbage.Spec.Ecdsa.Generic
import VerifiedGarbage.Spec.Secp256k1

/-!
# ECDSA over secp256k1: the contracts, on every target

**Trusted** (as every file in `Spec/`). The `Instance` of secp256k1
(`Spec/Secp256k1.lean`): `vg_ecdsa_secp256k1_sign`, in the module
`ecdsa_secp256k1`.
-/

namespace VG.Spec.Ecdsa.Secp256k1

/-- secp256k1. -/
def inst : Instance where
  curve := Spec.Secp256k1.curve
  name := "secp256k1"
  title := "secp256k1"

/-- `vg_ecdsa_secp256k1_sign` on every target. -/
def signApi : Api := inst.signApi

end VG.Spec.Ecdsa.Secp256k1
