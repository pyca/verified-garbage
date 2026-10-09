import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.PairedTable

namespace VG.Impl.MlDsa.AArch64.Optimized.Paired
open VG

def pairedConsts : List (String × List (BitVec 64)) := [("VG_MLDSA_INV_PAIR",expandedWords)]

end VG.Impl.MlDsa.AArch64.Optimized.Paired
