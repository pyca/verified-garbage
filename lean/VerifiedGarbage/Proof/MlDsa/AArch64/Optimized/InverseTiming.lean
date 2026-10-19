module

public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Inverse
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Inverse
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
open VG.Impl.MlDsa.AArch64.Optimized.Inverse

/-- The inverse core reveals only its input/output and table addresses.
Polynomial coefficients and all intermediate arithmetic remain secret. -/
theorem core_ct : ConstantTime isa (fun _ => True)
    (Taint.AgreeS [] (Taint.ofRegs [.x0,.x1])) core :=
  VG.Taint.constantTime (A := taintS []) (Taint.ofRegs [.x0,.x1])
    (fun _ _ _ _ h => h) (by taint_decide)

/-- The static wrapper overwrites x1 with the public immutable table address;
its unused scratch argument has no influence on the trace. -/
theorem staticCode_ct : ConstantTime isa (fun _ => True)
    (Taint.AgreeS ["VG_MLDSA_INV_FOLDED"] (Taint.ofRegs [.x0])) staticCode :=
  VG.Taint.constantTime (A := taintS ["VG_MLDSA_INV_FOLDED"]) (Taint.ofRegs [.x0])
    (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
