module

public import VerifiedGarbage.Proof.Framework.Arm.TaintMono
import VerifiedGarbage.Proof.TripleDes.Arm.FunctionsLit
public import VerifiedGarbage.Impl.TripleDes.Arm.ExpandKey
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Arm.TaintMono
meta import VerifiedGarbage.Proof.TripleDes.Arm.FunctionsLit
meta import VerifiedGarbage.Impl.TripleDes.Arm.ExpandKey
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Constant-time Triple DES key expansion on ARMv7 -/

@[expose] public section

namespace VG.Proof.TripleDes.Arm

open VG VG.Arm VG.Impl.TripleDes.Arm

/-- Only argument pointers and explicitly public integer parameters agree;
all memory contents, including the key, schedule, and data, may differ. -/
def PublicRegs (rs : List Reg) (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ ∀ r ∈ rs, s₁.gpr r = s₂.gpr r

theorem expandKey_constantTime (pre : State → Prop) :
    ConstantTime isa pre (PublicRegs [.r0, .r1, .r2, .r3]) Key.expandKey := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact Taint.agree_ofRegs hp.2

end VG.Proof.TripleDes.Arm
