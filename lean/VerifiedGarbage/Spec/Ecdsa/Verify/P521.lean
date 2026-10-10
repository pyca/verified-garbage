module

public import VerifiedGarbage.Spec.Ecdsa.Verify.Generic
public import VerifiedGarbage.Spec.Ecdsa.P521

/-!
# ECDSA signature verification over P-521: the contracts, on every target

**Trusted** (as every file in `Spec/`). `vg_ecdsa_p521_verify`, in the
module `ecdsa_p521`, for P-521's `Ecdsa.Instance`.
-/

@[expose] public section

namespace VG.Spec.Ecdsa.P521

/-- `vg_ecdsa_p521_verify` on every target. -/
def verifyApi : Api := inst.verifyApi

end VG.Spec.Ecdsa.P521
