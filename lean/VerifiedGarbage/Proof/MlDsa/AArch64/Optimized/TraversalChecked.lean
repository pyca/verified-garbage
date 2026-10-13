module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Traversal
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Spec.MlKem
import VerifiedGarbage.TCB.Artifact

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Traversal

theorem outer_checked :
    Schedule.check key mask ((List.range 8).map outerSlice) = some standardOuter := by
  decide +kernel

theorem inner_checked :
    Schedule.check key mask ((List.range 8).map innerSlice) = some standardInner := by
  decide +kernel

end VG.Proof.MlDsa.AArch64.Optimized.Traversal
