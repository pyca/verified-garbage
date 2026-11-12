module

public import VerifiedGarbage.Impl.Rsa.AArch64.Keys
public import VerifiedGarbage.Impl.Rsa.AArch64.RecoverDet
meta import VerifiedGarbage.Impl.Rsa.AArch64.Keys
meta import VerifiedGarbage.Impl.Rsa.AArch64.RecoverDet
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-!
# RSA keys on AArch64: the functions' bodies as literals

`vg_rsa_crt_values`' and `vg_rsa_recover_primes_det`'s proofs check
properties of every instruction of their bodies (`main`): what they write
(`writesOnly`), the registers they keep through vector lanes
(`KeepLanes.keeps`) and the vector registers they keep (`keepsV`). The
literals of the bodies (`materialize_code`, `Proof/Framework/Lit.lean`) are
checked once here, so that those checks (`lit_decide`) do not build the
instructions again.
-/

@[expose] public section

namespace VG.Impl.Rsa.AArch64

materialize_code Keys.CrtValues.main

materialize_code RecoverDet.main

end VG.Impl.Rsa.AArch64
