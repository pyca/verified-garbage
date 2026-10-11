module

public import VerifiedGarbage.Spec.Ecdh.Generic
public import VerifiedGarbage.Spec.EcKey.P521

/-!
# ECDH over P-521: the contracts, on every target

**Trusted** (as every file in `Spec/`). `vg_ecdh_p521`, in the module
`ecdh_p521`, for P-521's `EcKey.Instance`.
-/

@[expose] public section

namespace VG.Spec.Ecdh.P521

/-- `vg_ecdh_p521` on every target. -/
def exchangeApi : Api := Instance.exchangeApi EcKey.P521.inst

end VG.Spec.Ecdh.P521
