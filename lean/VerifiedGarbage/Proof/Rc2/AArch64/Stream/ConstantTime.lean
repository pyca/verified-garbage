module

public import VerifiedGarbage.Proof.Rc2.AArch64.Stream.Lit
meta import VerifiedGarbage.Proof.Rc2.AArch64.Stream.Lit
public import VerifiedGarbage.Proof.Rc2.AArch64.ConstantTime
meta import VerifiedGarbage.Proof.Rc2.AArch64.ConstantTime
import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.TCB.AArch64.Target

/-! # Constant-time streaming RC2-CBC

The taint analysis of `init` and the update functions, the callees included,
from the public arguments: all seven (pointers and lengths), and the stack
pointer. -/

@[expose] public section

namespace VG.Proof.Rc2.AArch64.Stream

open VG VG.AArch64 VG.Impl.Rc2.AArch64.Stream

/-- The public registers: all seven arguments. -/
abbrev args : List Reg := [.x0, .x1, .x2, .x3, .x4, .x5, .x6]

theorem init_constantTime (pre : State → Prop) :
    ConstantTime isa pre (PublicRegs args) init := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs args) ?_ (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact ⟨hp.1, fun r hr => hp.2 r (Taint.mem_ofRegs.mp hr)⟩

theorem encryptUpdate_constantTime (pre : State → Prop) :
    ConstantTime isa pre (PublicRegs args) encryptUpdate := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs args) ?_ (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact ⟨hp.1, fun r hr => hp.2 r (Taint.mem_ofRegs.mp hr)⟩

theorem decryptUpdate_constantTime (pre : State → Prop) :
    ConstantTime isa pre (PublicRegs args) decryptUpdate := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs args) ?_ (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact ⟨hp.1, fun r hr => hp.2 r (Taint.mem_ofRegs.mp hr)⟩

end VG.Proof.Rc2.AArch64.Stream
