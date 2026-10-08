import VerifiedGarbage.Proof.Seed.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Taint

/-!
# Constant time

The pointers, the count of blocks and the stack pointer are public; so is
everything the functions compute from them (the batches' sizes, the counts
of rounds and lanes, the addresses of the round keys and of the lanes).
-/

namespace VG.Proof.Seed.AArch64

open VG VG.AArch64

/-- Only argument pointers and lengths agree; all memory contents, including
the key, schedule and data, may differ. -/
def PublicRegs (rs : List Reg) (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ ∀ r ∈ rs, s₁.gpr r = s₂.gpr r

theorem encrypt_constantTime (pre : State → Prop) :
    ConstantTime isa pre (PublicRegs [.x0, .x1, .x2, .x3]) Impl.Seed.AArch64.encrypt := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact ⟨hp.1, fun r hr => hp.2 r (Taint.mem_ofRegs.mp hr)⟩

theorem decrypt_constantTime (pre : State → Prop) :
    ConstantTime isa pre (PublicRegs [.x0, .x1, .x2, .x3]) Impl.Seed.AArch64.decrypt := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact ⟨hp.1, fun r hr => hp.2 r (Taint.mem_ofRegs.mp hr)⟩

theorem expandKey_constantTime (pre : State → Prop) :
    ConstantTime isa pre (PublicRegs [.x0, .x1, .x2]) Impl.Seed.AArch64.expandKey := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact ⟨hp.1, fun r hr => hp.2 r (Taint.mem_ofRegs.mp hr)⟩

end VG.Proof.Seed.AArch64
