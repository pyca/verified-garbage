module

public import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
public import VerifiedGarbage.Impl.ChaCha20.Arm.Xor
meta import VerifiedGarbage.Impl.ChaCha20.Arm.Xor
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs

/-!
# ChaCha20 on Arm: the code as literals
-/

@[expose] public section

namespace VG

materialize_code Impl.ChaCha20.Arm.block
materialize_code Impl.ChaCha20.Arm.Xor.xor

end VG
