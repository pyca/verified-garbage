module

public import VerifiedGarbage.Spec.Ecdsa.Generic
public import VerifiedGarbage.Spec.P224

/-!
# ECDSA over P-224: its instance

**Trusted** (as every file in `Spec/`). The `Instance` of P-224
(`Spec/P224.lean`), for the functions of the module `ecdsa_p224`.
-/

@[expose] public section

namespace VG.Spec.Ecdsa.P224

/-- P-224. -/
def inst : Instance where
  curve := Spec.P224.curve
  name := "p224"
  title := "P-224"

end VG.Spec.Ecdsa.P224
