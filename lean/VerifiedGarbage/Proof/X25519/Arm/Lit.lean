module

public import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
public import VerifiedGarbage.Impl.X25519.Arm
meta import VerifiedGarbage.Impl.X25519.Arm
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs

/-!
# X25519 on 32-bit ARM: the code as a literal

The code of `vg_x25519` as a literal (`materialize_code`,
`Proof/Framework/Lit.lean`).
-/

@[expose] public section

namespace VG

materialize_code Impl.X25519.Arm.x25519

end VG
