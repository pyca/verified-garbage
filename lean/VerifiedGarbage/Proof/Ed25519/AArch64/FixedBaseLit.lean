module

public import VerifiedGarbage.Impl.Ed25519.AArch64.FixedBase
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Ed25519.AArch64.FixedBase
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-!
# Ed25519 on AArch64: the base-point multiplication's and the scalar reduction's code as literals

The comb's parts are literals of their own, so that X25519's base-point multiplication, which is
made of them too, shares them.
-/

@[expose] public section

namespace VG

materialize_code Impl.Ed25519.AArch64.scalarBase
materialize_code Impl.Ed25519.AArch64.scalarReduce

end VG
