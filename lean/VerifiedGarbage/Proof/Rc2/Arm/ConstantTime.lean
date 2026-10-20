module

public import VerifiedGarbage.Proof.Rc2.Arm.Lit
meta import VerifiedGarbage.Proof.Rc2.Arm.Lit
import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.TCB.Arm.Target
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.TCB.Arm.Target

/-! # Constant-time RC2 block operations -/

@[expose] public section

namespace VG.Proof.Rc2.Arm

open VG VG.Arm VG.Impl.Rc2.Arm

def PublicRegs (rs : List Reg) (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ ∀ r ∈ rs, s₁.gpr r = s₂.gpr r

theorem encryptBlock_constantTime (pre : State → Prop) :
    ConstantTime isa pre (PublicRegs [.r0, .r1, .r2]) encryptBlock := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact Taint.agree_ofRegs hp.2

theorem decryptBlock_constantTime (pre : State → Prop) :
    ConstantTime isa pre (PublicRegs [.r0, .r1, .r2]) decryptBlock := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact Taint.agree_ofRegs hp.2

end VG.Proof.Rc2.Arm
