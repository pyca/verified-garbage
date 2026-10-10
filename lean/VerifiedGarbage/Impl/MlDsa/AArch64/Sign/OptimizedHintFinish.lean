import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.Sign

namespace VG.Impl.MlDsa.AArch64.Sign.Optimized
open VG VG.AArch64

/-- Add the low-word hint count before consuming the high-word norm result. -/
def hintFinish : List Instr := onesAdd ++ ([.lsr .x .x0 .x0 32,.logic .and .w .x24 .x24 .x0] : List Instr)

end VG.Impl.MlDsa.AArch64.Sign.Optimized
