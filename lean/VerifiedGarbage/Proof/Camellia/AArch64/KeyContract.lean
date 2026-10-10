import VerifiedGarbage.Impl.Camellia.AArch64.ExpandKey
import VerifiedGarbage.Spec.Camellia.Contract
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Camellia.AArch64.Lit

/-!
# The Camellia key schedule on AArch64: contract and constant time

`expandKeyAArch64`: `expandKey` with its working space at `x3`
(`scratch`), as the frame calls it. `expandKey_ct`: it is constant time,
by the taint analysis: the pointers, the key's length and the stack
pointer are public, and so is everything the code computes from them,
which it keeps in registers; the key's words, and everything computed from
them, are secret.
-/

namespace VG.Proof.Camellia.AArch64

open VG VG.AArch64 VG.Impl.Camellia.AArch64

/-- The key schedule on AArch64 with its working space at `x3`. -/
def expandKeyAArch64 : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
    let sched : Region := ⟨s.gpr .x2, 272⟩
    let scratch : Region := ⟨s.gpr .x3, 8 * slots⟩
    s.rd = [key] ∧ s.wr = [sched, scratch] ∧ key.Disjoint sched ∧ key.Disjoint scratch ∧
      sched.Disjoint scratch ∧
      (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + 272 ≤ 2 ^ 64 ∧
      (s.gpr .x3).toNat + 8 * slots ≤ 2 ^ 64 ∧
      ((s.gpr .x1).toNat = 16 ∨ (s.gpr .x1).toNat = 24 ∨ (s.gpr .x1).toNat = 32)
  post s s' :=
    Spec.Camellia.bytesAt s'.mem (s.gpr .x2)
        (8 * Spec.Camellia.scheduleLength (Spec.Camellia.rounds (s.gpr .x1).toNat)) =
      Spec.Camellia.scheduleBytes
        (Spec.Camellia.expandKey (Spec.Camellia.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat))
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

theorem expandKeyTaint_agree (s₁ s₂ : State) (_ : expandKeyAArch64.pre s₁) (_ : expandKeyAArch64.pre s₂)
    (hp : expandKeyAArch64.pub s₁ s₂) : VG.AArch64.Taint.Agree (Taint.ofRegs [.x0, .x1, .x2, .x3]) s₁ s₂ := by
  obtain ⟨h1, h2, h3, h4, hsp⟩ := hp
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem expandKey_ct : ConstantTime isa expandKeyAArch64.pre expandKeyAArch64.pub expandKey :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3]) expandKeyTaint_agree
    (by taint_decide)

end VG.Proof.Camellia.AArch64
