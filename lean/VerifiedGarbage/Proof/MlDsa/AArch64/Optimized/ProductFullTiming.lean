module

public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.MultiplyInverse
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.MultiplyInverse
public import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Neon.Ntt
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Neon.Ntt
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.TCB.AArch64.Target

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64

theorem productStatic_ct (raw : Bool) : ConstantTime isa (fun _ => True)
    (Taint.AgreeS ["VG_MLDSA_INV_FOLDED"] (Taint.ofRegs [.x0,.x1,.x2]))
    (VG.Impl.MlDsa.AArch64.Optimized.MultiplyInverse.staticCode raw) := by
  cases raw <;>
    exact VG.Taint.constantTime (A := taintS ["VG_MLDSA_INV_FOLDED"]) (Taint.ofRegs [.x0,.x1,.x2])
      (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
