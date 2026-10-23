module

public import VerifiedGarbage.Impl.Ecdsa.Verify.P256.PPC64LE
public import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Ecdsa.Verify.P256.PPC64LE
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# ECDSA verification over P-256 on PPC64LE: the code as a literal

`vg_ecdsa_p256_verify` as a literal (`materialize_code`,
`Proof/Framework/Lit.lean`), which its constant time and `spSafe` evaluate.
-/

@[expose] public section

namespace VG

materialize_code Impl.Ecdsa.Verify.PPC64LE.verifyP256

end VG
