import VerifiedGarbage.Spec.Ecdsa.Verify.Generic
import VerifiedGarbage.Spec.Ecdsa.BrainpoolP256r1

/-!
# ECDSA signature verification over brainpoolP256r1: the contracts, on every target

**Trusted** (as every file in `Spec/`). `vg_ecdsa_brainpoolp256r1_verify`, in the
module `ecdsa_brainpoolp256r1`, for brainpoolP256r1's `Ecdsa.Instance`.
-/

namespace VG.Spec.Ecdsa.BrainpoolP256r1

/-- `vg_ecdsa_brainpoolp256r1_verify` on every target. -/
def verifyApi : Api := inst.verifyApi

end VG.Spec.Ecdsa.BrainpoolP256r1
