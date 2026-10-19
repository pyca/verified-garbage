module

public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.DotInverse
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.DotInverse
public import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Neon.Ntt
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Neon.Ntt
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.TCB.AArch64.Target

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.DotInverse

/-- Dot accumulation and both inverse passes depend only on public addresses. -/
theorem dot4Inverse_ct : ConstantTime isa (fun _ => True)
    (Taint.AgreeS ["VG_MLDSA_INV_FOLDED"] (Taint.ofRegs [.x0,.x1,.x2])) (staticCode 4) :=
  VG.Taint.constantTime (A:=taintS ["VG_MLDSA_INV_FOLDED"]) (Taint.ofRegs [.x0,.x1,.x2])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem dot5Inverse_ct : ConstantTime isa (fun _ => True)
    (Taint.AgreeS ["VG_MLDSA_INV_FOLDED"] (Taint.ofRegs [.x0,.x1,.x2])) (staticCode 5) :=
  VG.Taint.constantTime (A:=taintS ["VG_MLDSA_INV_FOLDED"]) (Taint.ofRegs [.x0,.x1,.x2])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem dot7Inverse_ct : ConstantTime isa (fun _ => True)
    (Taint.AgreeS ["VG_MLDSA_INV_FOLDED"] (Taint.ofRegs [.x0,.x1,.x2])) (staticCode 7) :=
  VG.Taint.constantTime (A:=taintS ["VG_MLDSA_INV_FOLDED"]) (Taint.ofRegs [.x0,.x1,.x2])
    (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.MlDsa.AArch64.Optimized
