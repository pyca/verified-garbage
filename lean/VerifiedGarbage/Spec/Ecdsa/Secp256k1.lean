module

public import VerifiedGarbage.Spec.Ecdsa.Generic
public import VerifiedGarbage.Spec.Secp256k1

/-!
# ECDSA over secp256k1: its instance

**Trusted** (as every file in `Spec/`). The `Instance` of secp256k1
(`Spec/Secp256k1.lean`), for the functions of the module `ecdsa_secp256k1`.
-/

@[expose] public section

namespace VG.Spec.Ecdsa.Secp256k1

/-- secp256k1. -/
def inst : Instance where
  curve := Spec.Secp256k1.curve
  name := "secp256k1"
  title := "secp256k1"

end VG.Spec.Ecdsa.Secp256k1
