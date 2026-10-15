module

public import VerifiedGarbage.Proof.Sm4.Arm.LayersLit
meta import VerifiedGarbage.Proof.Sm4.Arm.LayersLit
public import VerifiedGarbage.Impl.Sm4.Arm.Ecb
meta import VerifiedGarbage.Impl.Sm4.Arm.Ecb
public import VerifiedGarbage.Impl.Sm4.Arm.ExpandKey
meta import VerifiedGarbage.Impl.Sm4.Arm.ExpandKey
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs

/-!
# SM4 on Arm: the code as literals

The code of the key expansion and of ECB in both directions as literals
(`materialize_code`, `Proof/Framework/Lit.lean`), which the checks of the
whole functions (`taint_decide`, `lit_decide`) read rather than build the
code again in each of them.
-/

@[expose] public section

namespace VG.Proof.Sm4.Arm

materialize_flat_code expandKeyCode := Impl.Sm4.Arm.expandKey
materialize_flat_code ecbAnyCode := Impl.Sm4.Arm.ecbAny

end VG.Proof.Sm4.Arm
