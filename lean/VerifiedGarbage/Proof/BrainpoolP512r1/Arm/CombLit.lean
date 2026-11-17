module

public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.ArmComb
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.ArmComb
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

/-! Check the configured comb's instruction literal once for subsequent audits. -/

@[expose] public section
namespace VG

materialize_code Impl.Weierstrass.Arm.mulGeneratorBrainpoolP512r1

end VG
