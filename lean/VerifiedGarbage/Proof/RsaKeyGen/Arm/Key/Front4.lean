module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Front3
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Div
import VerifiedGarbage.Proof.Rsa.Arm.RvHalving
import VerifiedGarbage.Proof.Rsa.Arm.RvRest
import VerifiedGarbage.Proof.Rsa.RecoverSubtract

/-! # An RSA key on ARMv7: `L = lcm(p − 1, q − 1)` (`lcm_vp`) -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Key
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Key VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP sub32 VP.of_imp)
open VG.Proof.Rsa (b2n)

/-- The modulus of the gcd's inverse: `v`, or 3 for `v < 2`. -/
def mG (P : KP) (σ : State) : Nat := if v2 P σ < 2 then 3 else v2 P σ

/-- The arrays before the gcd's inverse. -/
def AG (P : KP) (σ : State) : Nat → Nat :=
  upd (upd (upd (AH P σ (8 * P.K)) aU2 (u2 P σ)) aV2 (v2 P σ)) aTmp2 (mG P σ)

theorem ite_b2n_not {α : Type} (p : Prop) [Decidable p] (a b : α) :
    (if b2n (!decide p) = 0 then a else b) = if p then a else b := by
  by_cases h : p <;> simp [h, b2n]

theorem v2_eq (P : KP) (σ : State) : (if (hk P σ (8 * P.K)).2.1 % 2 = 1 then (hk P σ (8 * P.K)).2.1
    else (hk P σ (8 * P.K)).1) = v2 P σ := by
  show _ = if (hk P σ (8 * P.K)).2.1 % 2 = 0 then (hk P σ (8 * P.K)).1 else (hk P σ (8 * P.K)).2.1
  generalize hk P σ (8 * P.K) = st
  by_cases h : st.2.1 % 2 = 0
  · rw [ite_eq_right (by omega), ite_eq_left h]
  · rw [ite_eq_left (by omega), ite_eq_right h]

theorem u2_eq (P : KP) (σ : State) : (if (hk P σ (8 * P.K)).2.1 % 2 = 1 then (hk P σ (8 * P.K)).1
    else (hk P σ (8 * P.K)).2.1) = u2 P σ := by
  show _ = if (hk P σ (8 * P.K)).2.1 % 2 = 0 then (hk P σ (8 * P.K)).2.1 else (hk P σ (8 * P.K)).1
  generalize hk P σ (8 * P.K) = st
  by_cases h : st.2.1 % 2 = 0
  · rw [ite_eq_right (by omega), ite_eq_left h]
  · rw [ite_eq_left (by omega), ite_eq_right h]

theorem A1_two (P : KP) (σ : State) : A1 P σ aTwo = 2 := by
  simp (config := {decide := true}) only [A1, A0, upd, ↓reduceIte]

theorem A1_three (P : KP) (σ : State) : A1 P σ aThree = 3 := by
  simp (config := {decide := true}) only [A1, A0, upd, ↓reduceIte]

theorem A1_one (P : KP) (σ : State) : A1 P σ aOne = 1 := by
  simp (config := {decide := true}) only [A1, A0, upd, ↓reduceIte]

theorem A1_zero (P : KP) (σ : State) : A1 P σ aZero = 0 := by
  simp (config := {decide := true}) only [A1, A0, Aload, upd, ↓reduceIte]

theorem v2_odd (P : KP) (σ : State) (h : 2 ≤ v2 P σ) : v2 P σ % 2 = 1 :=
  (VG.Proof.RsaKeyGen.lcm_eq (K := 8 * P.K) (pm_lt P σ) (qm_lt P σ)).1 h

theorem mG_odd (P : KP) (σ : State) : mG P σ % 2 = 1 ∧ 1 < mG P σ := by
  unfold mG; split
  · exact ⟨rfl, by decide⟩
  · rename_i h; exact ⟨v2_odd P σ (by omega), by omega⟩

/-- After `lcm(p − 1, q − 1)`. -/
abbrev S3 (P : KP) (E : State → Prop) : State → State → Prop :=
  St P E (fun σ => upd (AH P σ (8 * P.K)) aL (lv P σ)) (aL :: LH) (fun _ _ => 0) []

section
variable {P : KP}

theorem gcdUV_vp [VG.Proof.Rsa.Arm.Keys.InvLaw] {E : State → Prop} : VP (S2 P E) gcdUV
    (St P E (fun σ => upd (AH P σ (8 * P.K)) aG (gv P σ)) (aG :: LH) (fun _ _ => 0) []) := by
  simp only [gcdUV, List.cons_append, List.nil_append]
  refine VP.seq (VP.block_append (St.pbitOf bitVe_taint (by simp) (by decide))
    (St.pnotS (X := fun σ => decide (AH P σ (8 * P.K) aV % 2 = 1)) notVe_taint (by simp) (by decide)
      fun _ _ => by rw [upd_self])) ?_
  refine VP.seq (St.psel selU2_taint (by decide) (by simp) (by simp) (by decide) (by decide) (by simp)
    fun _ _ => by rw [upd_self]; exact b2n_le' _) ?_
  refine VP.seq (St.psel selV2_taint (by decide) (by simp) (by simp) (by decide) (by decide) (by simp)
    fun _ _ => by rw [upd_self]; exact b2n_le' _) ?_
  refine VP.assoc (VP.seq (St.pltS ltV2_taint (by simp) (by simp) (by decide) (by decide) (by decide)) ?_)
  refine VP.seq (G := St P E (AG P) (aTmp2 :: aV2 :: aU2 :: LH)
    (fun σ => upd (fun _ => 0) sV2 (b2n (decide (v2 P σ < 2)))) [sV2])
    ((St.psel selT2_taint (by decide) (by simp) (by simp) (by decide) (by decide) (by simp)
    fun _ _ => by rw [upd_self]; exact b2n_le' _).mono (fun _ _ h => h) fun σ s h => ?_) ?_
  · refine h.mono (fun j hj => ⟨by mem_sub, ?_⟩)
      (fun d hd => ⟨by simp only [List.mem_singleton] at hd; simp [hd], ?_⟩)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp (config := {decide := true}) only [AG, AH, upd, ↓reduceIte, ite_b2n_not, ite_b2n, v2_eq, u2_eq,
          A1_two, A1_three]
      unfold mG; split <;> simp_all
    · simp only [List.mem_singleton] at hd; subst hd
      simp (config := {decide := true}) only [upd, ↓reduceIte, ite_b2n_not, v2_eq, AH, A1_two]
  refine VP.seq (St.pinv mT2_taint u2Copy_taint (by simp) (by simp) (by simp) (by simp) ?_ (by decide)
    fun σ _ => ?_) ?_
  · intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · simp (config := {decide := true}) only [AG, AH, upd, ↓reduceIte, A1_zero, A1_one]
    exact ⟨trivial, trivial, (mG_odd P σ).1, (mG_odd P σ).2⟩
  refine (St.psel selG_taint (by decide) (by simp) (by simp) (by decide) (by decide) (by simp)
    fun _ _ => by rw [upd_self]; exact b2n_le' _).mono (fun _ _ h => h) fun σ s h =>
      h.mono (fun j hj => ⟨by mem_sub, ?_⟩) (fun d hd => absurd hd (by simp))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;>
    simp (config := {decide := true}) only [AG, AH, upd, ↓reduceIte, ite_b2n, A1_one]
  unfold gv mG
  by_cases h2 : v2 P σ < 2
  · rw [ite_eq_left h2, ite_eq_left h2]
  · rw [ite_eq_right h2, ite_eq_right h2, ite_eq_right h2]

theorem gv_pos [VG.Proof.Rsa.Arm.Keys.InvLaw] (P : KP) (σ : State) : 0 < gv P σ := by
  unfold gv
  split
  · decide
  · rename_i h
    have lt := hv_lt P σ
    have u : u2 P σ < 2 ^ (32 * P.W) := by unfold u2; split <;> omega
    have v : v2 P σ < 2 ^ (32 * P.W) := by unfold v2; split <;> omega
    rw [(ivr_spec (v2_odd P σ (by omega)) (by omega) u v).1]
    exact Nat.gcd_pos_of_pos_right _ (by omega)

/-- `L = lcm(p − 1, q − 1)`. -/
theorem lcm_vp [VG.Proof.Rsa.Arm.Keys.InvLaw] {E : State → Prop} : VP (S1 P E) lcmPart (S3 P E) := by
  simp only [lcmPart, seqs]
  refine VP.seq halving_vp (VP.seq gcdUV_vp (VP.seq (St.pcopy lF_taint (by decide) (by simp) (by decide)) ?_))
  refine (St.pdivBy dvG_taint hdrL_taint (by decide) (by simp) (by simp) (by decide) fun σ _ => ?_).mono
    (fun _ _ h => h) fun σ s h => h.mono (fun j hj => ⟨by mem_sub, ?_⟩)
      (fun d hd => ⟨hd, rfl⟩)
  · simp (config := {decide := true}) only [upd, ↓reduceIte]; exact gv_pos P σ
  · mem_cases <;> simp (config := {decide := true}) only [AH, upd, ↓reduceIte]
    rfl

end

end VG.Proof.RsaKeyGen.Arm.Key
