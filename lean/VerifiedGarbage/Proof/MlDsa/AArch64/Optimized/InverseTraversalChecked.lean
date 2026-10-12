module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTraversal
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.InverseTraversal

theorem local_checked :
    Schedule.check key mask ((List.range 8).map localSlice) = some standardLocal := by
  decide +kernel

theorem strided_checked :
    Schedule.check key mask ((List.range 8).map stridedSlice) = some standardStrided := by
  decide +kernel

end VG.Proof.MlDsa.AArch64.Optimized.InverseTraversal
