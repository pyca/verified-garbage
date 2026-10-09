import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Inverse

namespace VG.Impl.MlDsa.AArch64.Optimized.Inverse

/-- Static root/reciprocal data used by the selected folded inverse. -/
def inverseConsts : List (String × List (BitVec 64)) :=
  [("VG_MLDSA_INV_FOLDED",expandedWords)]

end VG.Impl.MlDsa.AArch64.Optimized.Inverse
