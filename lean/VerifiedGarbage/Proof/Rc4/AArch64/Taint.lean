module

public import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Rc4.AArch64.Lit
public import VerifiedGarbage.Impl.Rc4.AArch64
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Rc4.AArch64.Lit
meta import VerifiedGarbage.Impl.Rc4.AArch64

@[expose] public section

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.Impl.Rc4.AArch64

/-- Key scheduling has no secret-dependent control flow or memory address:
the key bytes, `j` and the table indices stay in vector registers. -/
theorem init_ct : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [.x0, .x1, .x2])) init := by
  exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2])
    (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.Rc4.AArch64
