module

public import VerifiedGarbage.Impl.Ecdsa.P256.PPC64LEComb
public import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Ecdsa.P256.PPC64LEComb
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# ECDSA signatures over P-256 by the comb on PPC64LE: the code as a literal

`vg_ecdsa_p256_sign` with `[k]G` by the comb as a literal
(`materialize_code`, `Proof/Framework/Lit.lean`), which its constant time
and its stack depth evaluate.
-/

@[expose] public section

namespace VG

materialize_code Impl.Ecdsa.PPC64LE.signP256Comb

end VG
