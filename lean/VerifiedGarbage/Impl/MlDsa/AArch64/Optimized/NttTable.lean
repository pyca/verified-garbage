import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Ntt

namespace VG.Impl.MlDsa.AArch64.Optimized.Ntt

def nttConsts : List (String × List (BitVec 64)) :=
  [("VG_MLDSA_NTT_EXPANDED",staticNttWords)]

end VG.Impl.MlDsa.AArch64.Optimized.Ntt
