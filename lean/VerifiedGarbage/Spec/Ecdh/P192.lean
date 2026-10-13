module

public import VerifiedGarbage.Spec.Ecdh.Generic
public import VerifiedGarbage.Spec.EcKey.P192

/-!
# ECDH over P-192: the contracts, on every target

**Trusted** (as every file in `Spec/`). `vg_ecdh_p192`, in the module
`ecdh_p192`, for P-192's `EcKey.Instance`.
-/

@[expose] public section

namespace VG.Spec.Ecdh.P192

/-- `vg_ecdh_p192` on every target. -/
def exchangeApi : Api := Instance.exchangeApi EcKey.P192.inst

end VG.Spec.Ecdh.P192
