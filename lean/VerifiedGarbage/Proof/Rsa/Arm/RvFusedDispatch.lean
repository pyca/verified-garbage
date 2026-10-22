module

import VerifiedGarbage.Proof.Rsa.Arm.RvFusedFlags
import VerifiedGarbage.Proof.Rsa.Arm.RvSlots
import VerifiedGarbage.Proof.Rsa.Arm.RvKM
import VerifiedGarbage.Proof.Rsa.Arm.RvStage
import VerifiedGarbage.Proof.Rsa.Arm.RvMmul2
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Impl.Rsa.Arm.RecoverFused
public import VerifiedGarbage.Proof.Rsa.Arm.RvSt

/-! Branch only on the public candidate index, never the exponent bit. -/

@[expose] public section
namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover
open VG.Proof.Rsa.Arm.Keys VG.Proof.X25519.Arm
open VG.Impl.Rsa.Arm.RecoverFused

theorem VP.knownBranch {F G : State → State → Prop} {c : Cond} {t e : Prog isa} (b : Bool)
    (known : ∀ σ s, F σ s → isa.eval c s = some b)
    (branch : VP F (if b then t else e) G) : VP F (.ite c t e) G := by
  cases b
  · refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => (known σ₁ s₁ h₁).trans (known σ₂ s₂ h₂).symm)
      ?_ (branch.mono (fun _ _ h => h.1) (fun _ _ h => h))
    refine ⟨fun σ s h => False.elim ?_, fun s₁ s₂ t₁ t₂ u v h _ _ => False.elim ?_⟩
    · have bad := h.2; rw [known σ s h.1] at bad; cases bad
    · obtain ⟨σ₁, _, h₁, _⟩ := h
      have bad := h₁.2; rw [known σ₁ s₁ h₁.1] at bad; cases bad
  · refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => (known σ₁ s₁ h₁).trans (known σ₂ s₂ h₂).symm)
      (branch.mono (fun _ _ h => h.1) (fun _ _ h => h)) ?_
    refine ⟨fun σ s h => False.elim ?_, fun s₁ s₂ t₁ t₂ u v h _ _ => False.elim ?_⟩
    · have bad := h.2; rw [known σ s h.1] at bad; cases bad
    · obtain ⟨σ₁, _, h₁, _⟩ := h
      have bad := h₁.2; rw [known σ₁ s₁ h₁.1] at bad; cases bad

section
variable {P : RP} {E : State → Prop} {A AW V : State → Nat → Nat} {L LW LS : List Nat}

theorem St.pcandidateTest {j v : Nat} (hj : j < 100) (hv : v < 100)
    (enc : encodable (BitVec.ofNat 32 v) = true) (cert : Cert (.block (candidateTest v)))
    (slot : sCand ∈ LS) (value : ∀ σ, E σ → V σ sCand = j) :
    VP (St P E A L AW LW V LS P.w nArr) (.block (candidateTest v))
      (fun σ s => St P E A L AW LW V LS P.w nArr σ s ∧ s.z = decide (j = v)) := by
  refine VP.ctx cert (fun _ _ h => h.2.2.2) fun σ s ⟨e, h, hm, hw⟩ => ?_
  unfold candidateTest
  refine h.ldrSlot hw slot (r := .r1) (by decide) fun s1 h1 hw1 u1 => ?_
  have m1 := hm.of_rest (u1.rest (ws := [.r1]) (by simp)) u1.mem
  refine wp_cmp (op2_imm enc) fun t u2 z2 => WP.block_nil ?_
  obtain ⟨h2, hw2⟩ := h1.reg hw1 (u2.rest []) u2.mem
  refine ⟨⟨e, h2, m1.of_rest (u2.rest []) u2.mem, hw2⟩, ?_⟩
  rw [z2, u1.gpr, value σ e, Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff,
    BitVec.sub_eq_iff_eq_add]
  change BitVec.ofNat 32 j = (0#32 + BitVec.ofNat 32 v) ↔ j = v
  rw [BitVec.zero_add, ← BitVec.toNat_inj, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

/-- Reuse a proof of the selected public branch after testing the index. -/
theorem St.pcandidateIf {j v : Nat} (hj : j < 100) (hv : v < 100)
    (enc : encodable (BitVec.ofNat 32 v) = true) (cert : Cert (.block (candidateTest v)))
    (slot : sCand ∈ LS) (value : ∀ σ, E σ → V σ sCand = j)
    {yes no : Prog isa} {G : State → State → Prop}
    (branch : VP (St P E A L AW LW V LS P.w nArr) (if j = v then yes else no) G) :
    VP (St P E A L AW LW V LS P.w nArr)
      (.seq (.block (candidateTest v)) (.ite .eq yes no)) G := by
  refine VP.seq (St.pcandidateTest hj hv enc cert slot value)
    (VP.knownBranch (decide (j = v)) (fun σ s h => congrArg some h.2) ?_)
  by_cases equal : j = v
  · simpa only [equal, decide_true, ↓reduceIte] using
      branch.mono (fun _ _ h => h.1) (fun _ _ h => h)
  · simpa only [equal, decide_false, Bool.false_eq_true, ↓reduceIte] using
      branch.mono (fun _ _ h => h.1) (fun _ _ h => h)

end
end VG.Proof.Rsa.Arm.Recover
