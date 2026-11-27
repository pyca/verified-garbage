module

public import VerifiedGarbage.Spec.Ecdh.Generic
public import VerifiedGarbage.Spec.EcKey.BrainpoolP320r1

/-!
# ECDH over brainpoolP320r1: the contracts, on every target

**Trusted** (as every file in `Spec/`). `vg_ecdh_brainpoolp320r1`, in the module
`ecdh_brainpoolp320r1`, for brainpoolP320r1's `EcKey.Instance`.
-/

@[expose] public section

namespace VG.Spec.Ecdh.BrainpoolP320r1

/-- `vg_ecdh_brainpoolp320r1` on every target. -/
def exchangeApi : Api := Instance.exchangeApi EcKey.BrainpoolP320r1.inst

end VG.Spec.Ecdh.BrainpoolP320r1
