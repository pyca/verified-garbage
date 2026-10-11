module

public import VerifiedGarbage.Spec.Ecdh.Generic
public import VerifiedGarbage.Spec.EcKey.BrainpoolP512r1

/-!
# ECDH over brainpoolP512r1: the contracts, on every target

**Trusted** (as every file in `Spec/`). `vg_ecdh_brainpoolp512r1`, in the module
`ecdh_brainpoolp512r1`, for brainpoolP512r1's `EcKey.Instance`.
-/

@[expose] public section

namespace VG.Spec.Ecdh.BrainpoolP512r1

/-- `vg_ecdh_brainpoolp512r1` on every target. -/
def exchangeApi : Api := Instance.exchangeApi EcKey.BrainpoolP512r1.inst

end VG.Spec.Ecdh.BrainpoolP512r1
