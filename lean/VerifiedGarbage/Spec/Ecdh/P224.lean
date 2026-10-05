import VerifiedGarbage.Spec.Ecdh.Generic
import VerifiedGarbage.Spec.EcKey.P224

/-!
# ECDH over P-224: the contracts, on every target

**Trusted** (as every file in `Spec/`). `vg_ecdh_p224`, in the module
`ecdh_p224`, for P-224's `EcKey.Instance`.
-/

namespace VG.Spec.Ecdh.P224

/-- `vg_ecdh_p224` on every target. -/
def exchangeApi : Api := Instance.exchangeApi EcKey.P224.inst

end VG.Spec.Ecdh.P224
