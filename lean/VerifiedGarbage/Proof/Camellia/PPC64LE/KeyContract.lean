module

public import VerifiedGarbage.Impl.Camellia.PPC64LE.ExpandKey
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Camellia.PPC64LE.Lit
meta import VerifiedGarbage.Impl.Camellia.PPC64LE.ExpandKey
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Camellia.PPC64LE.Lit

/-!
# The Camellia key schedule on PPC64LE: contract and constant time

`expandKeyPPC64LE`: `expandKey` with its working space at `r6`
(`scratch`), as the frame calls it. `expandKey_ct`: it is constant time,
by the taint analysis: the pointers, the key's length and the stack
pointer are public, and so is everything the code computes from them,
which it keeps in registers; the key's words, and everything computed from
them, are secret.
-/

@[expose] public section

namespace VG.Proof.Camellia.PPC64LE

open VG VG.PPC64LE VG.Impl.Camellia.PPC64LE

/-- The key schedule on PPC64LE with its working space at `r6`. -/
def expandKeyPPC64LE : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
    let sched : Region := ⟨s.gpr .r5, 272⟩
    let scratch : Region := ⟨s.gpr .r6, 8 * slots⟩
    s.rd = [key] ∧ s.wr = [sched, scratch] ∧ key.Disjoint sched ∧ key.Disjoint scratch ∧
      sched.Disjoint scratch ∧
      (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + 272 ≤ 2 ^ 64 ∧
      (s.gpr .r6).toNat + 8 * slots ≤ 2 ^ 64 ∧
      ((s.gpr .r4).toNat = 16 ∨ (s.gpr .r4).toNat = 24 ∨ (s.gpr .r4).toNat = 32)
  post s s' :=
    Spec.Camellia.bytesAt s'.mem (s.gpr .r5)
        (8 * Spec.Camellia.scheduleLength (Spec.Camellia.rounds (s.gpr .r4).toNat)) =
      Spec.Camellia.scheduleBytes
        (Spec.Camellia.expandKey (Spec.Camellia.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat))
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
      s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.sp = s₂.sp

theorem expandKeyTaint_agree (s₁ s₂ : State) (_ : expandKeyPPC64LE.pre s₁) (_ : expandKeyPPC64LE.pre s₂)
    (hp : expandKeyPPC64LE.pub s₁ s₂) : VG.PPC64LE.Taint.Agree (Taint.ofRegs [.r3, .r4, .r5, .r6]) s₁ s₂ := by
  obtain ⟨h1, h2, h3, h4, hsp⟩ := hp
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.PPC64LE.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem expandKey_ct : ConstantTime isa expandKeyPPC64LE.pre expandKeyPPC64LE.pub expandKey :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6]) expandKeyTaint_agree
    (by taint_decide)

end VG.Proof.Camellia.PPC64LE
