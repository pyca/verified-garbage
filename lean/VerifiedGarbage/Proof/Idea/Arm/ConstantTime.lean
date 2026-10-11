import VerifiedGarbage.Proof.Idea.Arm.Lit
import VerifiedGarbage.Proof.Framework.Arm.Taint

/-! # Constant-time IDEA programs on ARMv7

Only the stack pointer, the argument pointers and `n` are public; the key,
the subkeys and the data may differ between runs.
-/

namespace VG.Proof.Idea.Arm

open VG VG.Arm VG.Impl.Idea.Arm

def PublicRegs (rs : List Reg) (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ ∀ r ∈ rs, s₁.gpr r = s₂.gpr r

theorem expandKey_constantTime (pre : State → Prop) :
    ConstantTime isa pre (PublicRegs [.r0, .r1]) expandKey := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact Taint.agree_ofRegs hp.2

theorem invertKey_constantTime (pre : State → Prop) :
    ConstantTime isa pre (PublicRegs [.r0, .r1, .r2]) invertKey := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact Taint.agree_ofRegs hp.2

theorem ecb_constantTime (pre : State → Prop) :
    ConstantTime isa pre (PublicRegs [.r0, .r1, .r2, .r3]) ecb := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact Taint.agree_ofRegs hp.2

end VG.Proof.Idea.Arm
