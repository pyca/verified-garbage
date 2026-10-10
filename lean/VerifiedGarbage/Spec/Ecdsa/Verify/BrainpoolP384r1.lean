module

public import VerifiedGarbage.Spec.Ecdsa.Verify.Generic
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP384r1

/-!
# ECDSA signature verification over brainpoolP384r1: the contracts, on every target

**Trusted** (as every file in `Spec/`). `vg_ecdsa_brainpoolp384r1_verify`, in the
module `ecdsa_brainpoolp384r1`, for brainpoolP384r1's `Ecdsa.Instance`.
-/

@[expose] public section

namespace VG.Spec.Ecdsa.BrainpoolP384r1

/-- `vg_ecdsa_brainpoolp384r1_verify` on every target. -/
def verifyApi : Api := inst.verifyApi

end VG.Spec.Ecdsa.BrainpoolP384r1
