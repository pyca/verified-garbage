module

public import VerifiedGarbage.Spec.Ecdh.Generic
public import VerifiedGarbage.Spec.EcKey.Secp256k1

/-!
# ECDH over secp256k1: the contracts, on every target

**Trusted** (as every file in `Spec/`). `vg_ecdh_secp256k1`, in the module
`ecdh_secp256k1`, for secp256k1's `EcKey.Instance`.
-/

@[expose] public section

namespace VG.Spec.Ecdh.Secp256k1

/-- `vg_ecdh_secp256k1` on every target. -/
def exchangeApi : Api := Instance.exchangeApi EcKey.Secp256k1.inst

end VG.Spec.Ecdh.Secp256k1
