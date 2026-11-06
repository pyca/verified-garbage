module

public import VerifiedGarbage.Spec.Sha3

/-!
# SHA-3 and SHAKE: the rates

**Trusted** (as every file in `Spec/`). The rates of the six functions of
FIPS 202, which the instances' contracts (`Spec/Sha3/Instances.lean`) and
the sponge's (`Proof/Sha3/Contract.lean`, untrusted: only verified code calls
the sponge's functions) are stated over.
-/

@[expose] public section

namespace VG.Spec.Sha3

/-- The rates, in bytes, of the six functions of FIPS 202 (§6). -/
def rates : List Nat := [72, 104, 136, 144, 168]

end VG.Spec.Sha3
