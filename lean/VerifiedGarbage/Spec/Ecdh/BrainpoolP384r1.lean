import VerifiedGarbage.Spec.Ecdh.Generic
import VerifiedGarbage.Spec.EcKey.BrainpoolP384r1

/-!
# ECDH over brainpoolP384r1: the contracts, on every target

**Trusted** (as every file in `Spec/`). `vg_ecdh_brainpoolp384r1`, in the module
`ecdh_brainpoolp384r1`, for brainpoolP384r1's `EcKey.Instance`.
-/

namespace VG.Spec.Ecdh.BrainpoolP384r1

/-- `vg_ecdh_brainpoolp384r1` on every target. -/
def exchangeApi : Api := Instance.exchangeApi EcKey.BrainpoolP384r1.inst

end VG.Spec.Ecdh.BrainpoolP384r1
