import VerifiedGarbage.Spec.Ecdsa.Verify.Generic
import VerifiedGarbage.Spec.Ecdsa.Secp256k1

/-!
# ECDSA signature verification over secp256k1: the contracts, on every target

**Trusted** (as every file in `Spec/`). `vg_ecdsa_secp256k1_verify`, in the
module `ecdsa_secp256k1`, for secp256k1's `Ecdsa.Instance`.
-/

namespace VG.Spec.Ecdsa.Secp256k1

/-- `vg_ecdsa_secp256k1_verify` on every target. -/
def verifyApi : Api := inst.verifyApi

end VG.Spec.Ecdsa.Secp256k1
