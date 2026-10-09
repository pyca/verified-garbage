import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Product
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Inverse

namespace VG.Impl.MlDsa.AArch64.Optimized
open VG.AArch64

/-- The exact eight resident products starting one fused inverse slice. -/
def inverseProductLoads : List Instr :=
  (List.range 8).flatMap fun j => productLoad (Inverse.vr j) (16*j)

end VG.Impl.MlDsa.AArch64.Optimized
