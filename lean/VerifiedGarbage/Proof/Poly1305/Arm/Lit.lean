module

public import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
public import VerifiedGarbage.Impl.Poly1305.Arm
meta import VerifiedGarbage.Impl.Poly1305.Arm
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs

/-!
# Poly1305 on Arm: the code as literals
-/

@[expose] public section

namespace VG

materialize_code Impl.Poly1305.Arm.init
materialize_code Impl.Poly1305.Arm.blocks
materialize_code Impl.Poly1305.Arm.update
materialize_code Impl.Poly1305.Arm.finalize

end VG
