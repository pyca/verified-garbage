module

public import VerifiedGarbage.Impl.Ecdh.BrainpoolP256r1.PPC64LE
public import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Ecdh.BrainpoolP256r1.PPC64LE
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# ECDH over brainpoolP256r1 on PPC64LE: the code as a literal

`vg_ecdh_brainpoolp256r1` as a literal (`materialize_code`, `Proof/Framework/Lit.lean`),
which its constant time and `spSafe` evaluate.
-/

@[expose] public section

namespace VG

materialize_code Impl.Ecdh.PPC64LE.exchangeBrainpoolP256r1

end VG
