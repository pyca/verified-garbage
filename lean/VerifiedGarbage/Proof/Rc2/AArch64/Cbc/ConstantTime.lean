module

public import VerifiedGarbage.Proof.Rc2.AArch64.ConstantTime
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Rc2.AArch64.Cbc.Lit
public import VerifiedGarbage.Impl.Rc2.AArch64.Cbc
meta import VerifiedGarbage.Proof.Rc2.AArch64.ConstantTime
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Rc2.AArch64.Cbc.Lit
meta import VerifiedGarbage.Impl.Rc2.AArch64.Cbc

/-! # Constant-time CBC callers -/

@[expose] public section

namespace VG.Proof.Rc2.AArch64.Cbc

open VG VG.AArch64 VG.Impl.Rc2.AArch64.Cbc

theorem encrypt_constantTime (pre : State → Prop) :
    ConstantTime isa pre (PublicRegs [.x0, .x1, .x2, .x3, .x4]) encrypt := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) ?_
    (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact ⟨hp.1, fun r hr => hp.2 r (Taint.mem_ofRegs.mp hr)⟩

theorem decrypt_constantTime (pre : State → Prop) :
    ConstantTime isa pre (PublicRegs [.x0, .x1, .x2, .x3, .x4]) decrypt := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) ?_
    (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact ⟨hp.1, fun r hr => hp.2 r (Taint.mem_ofRegs.mp hr)⟩

end VG.Proof.Rc2.AArch64.Cbc
