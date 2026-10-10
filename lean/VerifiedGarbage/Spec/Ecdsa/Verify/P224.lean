module

public import VerifiedGarbage.Spec.Ecdsa.Verify.Generic
public import VerifiedGarbage.Spec.Ecdsa.P224

/-!
# ECDSA signature verification over P-224: the contracts, on every target

**Trusted** (as every file in `Spec/`). `vg_ecdsa_p224_verify`, in the
module `ecdsa_p224`, for P-224's `Ecdsa.Instance`.
-/

@[expose] public section

namespace VG.Spec.Ecdsa.P224

/-- `vg_ecdsa_p224_verify` on every target. -/
def verifyApi : Api := inst.verifyApi

end VG.Spec.Ecdsa.P224
