module

public import VerifiedGarbage.Impl.Sm4.AArch64.Ecb
public import VerifiedGarbage.Proof.Framework.AArch64.TaintMono
import VerifiedGarbage.Proof.Sm4.AArch64.LayersLit
meta import VerifiedGarbage.Impl.Sm4.AArch64.Ecb
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintMono
meta import VerifiedGarbage.Proof.Sm4.AArch64.LayersLit
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.RegSet
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.RegSet

/-!
# A summary of the sixteen-block encryption

Every mode runs the same sixteen-block encryption (`crypt16`); its
constant-time analysis is done once here (`taint_summary`), and the modes'
checks use it (`taint_decide_sum`).
-/

@[expose] public section

namespace VG.Proof.Sm4.AArch64

open VG VG.AArch64

/-- The registers public at `crypt16` in every mode: the arguments and the
pointers and counters the modes keep. -/
def τCrypt : VectorTaint.T :=
  VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5, .x14, .x15, .x16, .x17, .x19, .x20]

/- `crypt16` keeps `v31`, in which the feedback modes keep `x19`
(`Core.viaV`). -/
taint_summary cryptSum : VectorTaint.taint τCrypt Impl.Sm4.AArch64.crypt16
  keeping (RegSet.ofList [], RegSet.ofList [.v31])

end VG.Proof.Sm4.AArch64
