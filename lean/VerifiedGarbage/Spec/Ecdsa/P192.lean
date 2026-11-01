module

public import VerifiedGarbage.Spec.Ecdsa.Generic
public import VerifiedGarbage.Spec.P192

/-!
# ECDSA over P-192: its instance

**Trusted** (as every file in `Spec/`). The `Instance` of P-192
(`Spec/P192.lean`), for the functions of the module `ecdsa_p192`.
-/

@[expose] public section

namespace VG.Spec.Ecdsa.P192

/-- P-192. -/
def inst : Instance where
  curve := Spec.P192.curve
  name := "p192"
  title := "P-192"

end VG.Spec.Ecdsa.P192
