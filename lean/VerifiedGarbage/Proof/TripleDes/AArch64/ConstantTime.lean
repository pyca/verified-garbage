module

public import VerifiedGarbage.Proof.TripleDes.AArch64.FunctionsLit
meta import VerifiedGarbage.Proof.TripleDes.AArch64.FunctionsLit
public import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint
meta import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint
import VerifiedGarbage.Impl.Aes.AArch64.Alloc
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Impl.Aes.AArch64.Alloc
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.TCB.AArch64.Target

/-! # Constant-time Triple DES block and key-expansion programs -/

@[expose] public section

namespace VG.Proof.TripleDes.AArch64

open VG VG.AArch64 VG.Impl.TripleDes.AArch64

/-- Only argument pointers and explicitly public integer parameters agree;
all memory contents, including the key, schedule, and data, may differ. The
block functions keep their public pass state in vector registers, which
`VectorTaint` tracks. -/
def PublicRegs (rs : List Reg) (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ ∀ r ∈ rs, s₁.gpr r = s₂.gpr r

theorem encryptBlock_constantTime (pre : State → Prop) :
    ConstantTime isa pre (PublicRegs [.x0, .x1, .x2]) encryptBlock := by
  refine VG.Taint.constantTime (A := VectorTaint.taint) (VectorTaint.ofRegs [.x0, .x1, .x2]) ?_
    (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact ⟨⟨hp.1, fun r hr => hp.2 r (Taint.mem_ofRegs.mp hr)⟩, fun v hv => by
    simp [VectorTaint.ofRegs, RegSet.mem_ofList] at hv⟩

theorem decryptBlock_constantTime (pre : State → Prop) :
    ConstantTime isa pre (PublicRegs [.x0, .x1, .x2]) decryptBlock := by
  refine VG.Taint.constantTime (A := VectorTaint.taint) (VectorTaint.ofRegs [.x0, .x1, .x2]) ?_
    (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact ⟨⟨hp.1, fun r hr => hp.2 r (Taint.mem_ofRegs.mp hr)⟩, fun v hv => by
    simp [VectorTaint.ofRegs, RegSet.mem_ofList] at hv⟩

theorem expandKey_constantTime (pre : State → Prop) :
    ConstantTime isa pre (PublicRegs [.x0, .x1, .x2, .x3]) Key.expandKey := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact ⟨hp.1, fun r hr => hp.2 r (Taint.mem_ofRegs.mp hr)⟩

end VG.Proof.TripleDes.AArch64
