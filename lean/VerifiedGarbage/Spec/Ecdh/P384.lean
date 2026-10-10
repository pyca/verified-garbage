module

public import VerifiedGarbage.Spec.Ecdh.Generic
public import VerifiedGarbage.Spec.EcKey.P384

/-!
# ECDH over P-384: the contracts, on every target

**Trusted** (as every file in `Spec/`). `vg_ecdh_p384`, in the module
`ecdh_p384`, for P-384's `EcKey.Instance`.
-/

@[expose] public section

namespace VG.Spec.Ecdh.P384

/-- `vg_ecdh_p384` on every target. -/
def exchangeApi : Api := Instance.exchangeApi EcKey.P384.inst

end VG.Spec.Ecdh.P384
