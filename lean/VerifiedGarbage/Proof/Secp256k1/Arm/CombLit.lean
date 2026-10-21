module

public import VerifiedGarbage.Impl.Weierstrass.Arm.TCombSecp256k1
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Weierstrass.Arm.TCombSecp256k1
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

/-! Check the configured comb's instruction literal once for subsequent audits. -/

@[expose] public section
namespace VG

materialize_code Impl.Weierstrass.Arm.mulGeneratorSecp256k1

end VG
