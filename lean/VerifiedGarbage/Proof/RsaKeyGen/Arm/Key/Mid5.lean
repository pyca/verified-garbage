module
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Mid1

import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Mid2
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Mid3
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Mid4
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Taint2
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Half
import VerifiedGarbage.Proof.Rsa.Arm.RvRest
import VerifiedGarbage.Proof.Rsa.RecoverSubtract

/-! # An RSA key on ARMv7: `d` by `e`'s case (`dPart_vp`), and whether it is too small (`small_vp`) -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Key
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Key VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP sub32 VP.of_imp)
open VG.Proof.Rsa (b2n)

section
variable {P : KP}

theorem St.weaken {E E' : State → Prop} {A : State → Nat → Nat} {L : List Nat} {V : State → Nat → Nat}
    {LS : List Nat} {σ s : State} (h : St P E A L V LS σ s) (he : E σ → E' σ) : St P E' A L V LS σ s :=
  ⟨he h.1, h.2⟩

theorem isa_eq (s : State) : isa.eval .eq s = some s.z := rfl

/-- The branch on a flag of `e`, `d := 1` if it holds. -/
theorem b2n_one {p : Prop} [Decidable p] {z : Bool} (hz : z = decide (b2n (decide p) = 1)) (ht : some z = some true) :
    p := by
  cases z <;> simp_all [b2n]

theorem b2n_zero {p : Prop} [Decidable p] {z : Bool} (hz : z = decide (b2n (decide p) = 1)) (ht : some z = some false) :
    ¬ p := by
  cases z <;> simp_all [b2n]

/-- `d` and its flag, by `e`'s case. -/
theorem dPart_vp [VG.Proof.Rsa.Arm.Keys.InvLaw] {E : State → Prop} : VP (SE P E) dPart (G4 P E) := by
  unfold dPart
  refine VP.seq (St.pisOne isE0_taint (by simp) fun _ _ => by rw [VE_0]; exact b2n_le' _) ?_
  refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [isa_eq, isa_eq, h₁.2, h₂.2]) ?_ ?_
  · refine (dZero_vp (E := E)).mono (fun σ s ⟨⟨h, z⟩, t⟩ => h.weaken fun e => ⟨e, ?_⟩) fun σ s h => h.weaken (·.1)
    rw [VE_0, isa_eq] at *; exact b2n_one z t
  refine VP.mono (F := SE P (fun σ => E σ ∧ P.e ≠ 0)) ?_
    (fun σ s ⟨⟨h, z⟩, t⟩ => h.weaken fun e => ⟨e, by rw [VE_0, isa_eq] at *; exact b2n_zero z t⟩)
    (fun _ _ h => h)
  refine VP.seq (St.pisOne isE1_taint (by simp) fun _ _ => by rw [VE_1]; exact b2n_le' _) ?_
  refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [isa_eq, isa_eq, h₁.2, h₂.2]) ?_ ?_
  · refine (dOne_vp (E := fun σ => E σ ∧ P.e ≠ 0)).mono (fun σ s ⟨⟨h, z⟩, t⟩ => h.weaken fun e => ⟨e, ?_⟩)
      fun σ s h => h.weaken (·.1.1)
    rw [VE_1, isa_eq] at *; exact b2n_one z t
  refine VP.mono (F := SE P (fun σ => (E σ ∧ P.e ≠ 0) ∧ P.e ≠ 1)) ?_
    (fun σ s ⟨⟨h, z⟩, t⟩ => h.weaken fun e => ⟨e, by rw [VE_1, isa_eq] at *; exact b2n_zero z t⟩)
    (fun _ _ h => h)
  refine VP.seq (St.pisOne isEo_taint (by simp) fun _ _ => by rw [VE_o]; exact b2n_le' _) ?_
  refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [isa_eq, isa_eq, h₁.2, h₂.2]) ?_ ?_
  · refine (dOdd_vp (E := E)).mono (fun σ s ⟨⟨h, z⟩, t⟩ => h.weaken fun e => ⟨e.1.1, e.1.2, e.2, ?_⟩)
      fun σ s h => h.weaken (·.1)
    rw [VE_o, isa_eq] at *; exact b2n_one z t
  · refine (dEven_vp (E := E)).mono (fun σ s ⟨⟨h, z⟩, t⟩ => h.weaken fun e => ⟨e.1.1, e.1.2, e.2, ?_⟩)
      fun σ s h => h.weaken (·.1)
    rw [VE_o, isa_eq] at *; exact b2n_zero z t

/-- Whether `d` exists and is too small. -/
def smv (P : KP) (σ : State) : Bool := okv P σ && decide (dv P σ ≤ 2 ^ (8 * P.K))

/-- The flags after `d`. -/
def V5 (P : KP) (σ : State) : Nat → Nat := upd (upd (VE P) sOk (b2n (okv P σ))) sFl (b2n (smv P σ))

/-- After the check of `d`. -/
abbrev G5 (P : KP) (E : State → Prop) : State → State → Prop :=
  St P E (fun σ => upd (upd (AS3 P σ) aD (dv P σ)) aC (1 + 2 ^ (8 * P.K))) (aC :: aD :: L3) (V5 P)
    [sFl, sOk, sEo, sE1, sE0]

/-- Whether `d` is too small: Z iff it exists and `d ≤ 2^(8 p_len)`. -/
theorem small_vp {E : State → Prop} (hE : ∀ σ, E σ → In P σ) :
    VP (G4 P E) smallPart (fun σ s => G5 P E σ s ∧ s.z = decide (b2n (smv P σ) = 1)) := by
  simp only [smallPart, seqs, List.cons_append, List.nil_append]
  refine VP.seq (St.pcopy cOne_taint (by decide) (by simp) (by decide)) ?_
  refine VP.seq (St.psetHi (i := fun P => P.K / 4) cHi_taint (by simp) (by decide) (by decide) (by decide)
    (fun σ _ pre => by have := pre.k8; have := pre.k1; simp only [KP.W]; omega)
    fun σ _ pre => ?_) ?_
  · simp (config := {decide := true}) only [upd, ↓reduceIte, AH_one]
    exact Nat.one_lt_two_pow (by have := pre.k1; omega)
  refine VP.assoc (VP.seq (St.pltS ltSm_taint (by simp) (by simp) (by decide) (by decide) (by decide)) ?_)
  refine (VP.block_append (St.pandS (d := sFl) (a := sSm) (b := sOk)
    (X := fun σ => decide (dv P σ < 1 + 2 ^ (8 * P.K))) (Y := fun σ => okv P σ) fl_taint (by simp) (by simp)
    (by decide) (fun σ _ => ?_) (fun σ _ => ?_)) (St.pisOne isFl_taint (by simp) fun σ _ => by
      rw [upd_self]; exact b2n_le' _)).mono (fun _ _ h => h) fun σ s ⟨h, z⟩ => ⟨?_, ?_⟩
  · have k := (hE σ ‹_›).k8
    have e8 : 32 * (P.K / 4) = 8 * P.K := by omega
    have o1 : (1 : Nat) % 2 ^ 32 = 1 := by decide
    simp (config := {decide := true}) only [upd, ↓reduceIte, AH_one, e8, o1, Nat.mul_one]
  · simp (config := {decide := true}) only [upd, ↓reduceIte]
  · have k := h.2.1.pre.k8
    have e8 : 32 * (P.K / 4) = 8 * P.K := by omega
    refine h.mono (fun j hj => ⟨by mem_sub, ?_⟩) (fun j hj => ⟨by mem_sub, ?_⟩)
    · have o1 : (1 : Nat) % 2 ^ 32 = 1 := by decide
      mem_cases <;> simp (config := {decide := true}) only [upd, ↓reduceIte, AH_one, e8, o1, Nat.mul_one]
    · have : (decide (dv P σ < 1 + 2 ^ (8 * P.K)) && okv P σ) = smv P σ := by
        unfold smv; rw [Bool.and_comm]; congr 2; exact propext ⟨fun h => by omega, fun h => by omega⟩
      mem_cases <;> simp (config := {decide := true}) only [V5, upd, ↓reduceIte, this]
  · have : (decide (dv P σ < 1 + 2 ^ (8 * P.K)) && okv P σ) = smv P σ := by
      unfold smv; rw [Bool.and_comm]; congr 2; exact propext ⟨fun h => by omega, fun h => by omega⟩
    rw [z]; simp only [upd_self, this]

end

end VG.Proof.RsaKeyGen.Arm.Key
