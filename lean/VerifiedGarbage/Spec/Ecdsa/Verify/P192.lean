module

public import VerifiedGarbage.Spec.Ecdsa.Verify.Generic
public import VerifiedGarbage.Spec.Ecdsa.P192

/-!
# ECDSA signature verification over P-192: the contracts, on every target

**Trusted** (as every file in `Spec/`). `vg_ecdsa_p192_verify`, in the
module `ecdsa_p192`, for P-192's `Ecdsa.Instance`.
-/

@[expose] public section

namespace VG.Spec.Ecdsa.P192

/-- `vg_ecdsa_p192_verify` on every target. -/
def verifyApi : Api := inst.verifyApi

end VG.Spec.Ecdsa.P192
