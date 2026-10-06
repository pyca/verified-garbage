import VerifiedGarbage.Spec.Ecdh.Generic
import VerifiedGarbage.Spec.EcKey.BrainpoolP256r1

/-!
# ECDH over brainpoolP256r1: the contracts, on every target

**Trusted** (as every file in `Spec/`). `vg_ecdh_brainpoolp256r1`, in the module
`ecdh_brainpoolp256r1`, for brainpoolP256r1's `EcKey.Instance`.
-/

namespace VG.Spec.Ecdh.BrainpoolP256r1

/-- `vg_ecdh_brainpoolp256r1` on every target. -/
def exchangeApi : Api := Instance.exchangeApi EcKey.BrainpoolP256r1.inst

end VG.Spec.Ecdh.BrainpoolP256r1
