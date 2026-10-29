module

public import VerifiedGarbage.Impl.Camellia.RISCV64.ExpandKey
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Camellia.RISCV64.Lit
meta import VerifiedGarbage.Impl.Camellia.RISCV64.ExpandKey
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Camellia.RISCV64.Lit

/-!
# The Camellia key schedule on RISC-V: contract and constant time

As on PPC64LE (`Proof/Camellia/PPC64LE/KeyContract.lean`):
`expandKeyRISCV64`: `expandKey` with its working space at `a3`
(`scratch`, aligned), as the frame calls it. `expandKey_ct`: it is
constant time, by the taint analysis: the pointers, the key's length and
the stack pointer are public, and so is everything the code computes from
them, which it keeps in registers; the key's words, and everything computed
from them, are secret.
-/

@[expose] public section

namespace VG.Proof.Camellia.RISCV64

open VG VG.RISCV64 VG.Impl.Camellia.RISCV64

/-- The key schedule on RISC-V with its working space at `a3`. -/
def expandKeyRISCV64 : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
    let sched : Region := ⟨s.gpr .a2, 272⟩
    let scratch : Region := ⟨s.gpr .a3, 8 * slots⟩
    s.rd = [key] ∧ s.wr = [sched, scratch] ∧ key.Disjoint sched ∧ key.Disjoint scratch ∧
      sched.Disjoint scratch ∧
      (s.gpr .a0).toNat + (s.gpr .a1).toNat ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + 272 ≤ 2 ^ 64 ∧
      (s.gpr .a3).toNat + 8 * slots ≤ 2 ^ 64 ∧
      ((s.gpr .a1).toNat = 16 ∨ (s.gpr .a1).toNat = 24 ∨ (s.gpr .a1).toNat = 32) ∧
      (s.gpr .a3).toNat % 8 = 0
  post s s' :=
    Spec.Camellia.bytesAt s'.mem (s.gpr .a2)
        (8 * Spec.Camellia.scheduleLength (Spec.Camellia.rounds (s.gpr .a1).toNat)) =
      Spec.Camellia.scheduleBytes
        (Spec.Camellia.expandKey (Spec.Camellia.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat))
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.sp = s₂.sp

theorem expandKeyTaint_agree (s₁ s₂ : State) (_ : expandKeyRISCV64.pre s₁) (_ : expandKeyRISCV64.pre s₂)
    (hp : expandKeyRISCV64.pub s₁ s₂) : taint.Agree (Taint.ofRegs [.a0, .a1, .a2, .a3]) s₁ s₂ := by
  obtain ⟨h1, h2, h3, h4, hsp⟩ := hp
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem expandKey_ct : ConstantTime isa expandKeyRISCV64.pre expandKeyRISCV64.pub expandKey :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3]) expandKeyTaint_agree
    (by taint_decide)

end VG.Proof.Camellia.RISCV64
