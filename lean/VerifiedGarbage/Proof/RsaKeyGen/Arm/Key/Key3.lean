module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Key2
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # An RSA key on ARMv7: `n = p q` (`n_vp`) and the mask of the checks (`mask_vp`) -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Key
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Key VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP sub32 VP.of_imp)
open VG.Proof.Rsa (b2n)

/-- The arrays of the key. -/
abbrev AK (P : KP) (σ : State) : Nat → Nat :=
  upd (upd (upd (upd (A5 P σ) aQi (qx P σ)) aDP (dPv P σ)) aDQ (dQv P σ)) aN (nv P σ)
abbrev LK : List Nat := aN :: aDQ :: aDP :: LQ

/-- After `n`. -/
abbrev KN (P : KP) (E : State → Prop) : State → State → Prop :=
  St P E (AK P) LK (VQ P) [sGq, sPo, sFl, sOk, sEo, sE1, sE0]

/-- After the mask. -/
abbrev KF (P : KP) (E : State → Prop) : State → State → Prop :=
  St P E (AK P) LK (fun σ => upd (fun _ => 0) sMask (b2n (maskv P σ))) [sMask]

section
variable {P : KP}

theorem nv_lt (P : KP) (σ : State) : nv P σ < 2 ^ (16 * P.K) := by
  unfold nv
  rw [show 16 * P.K = 8 * P.K + 8 * P.K by omega, Nat.pow_add]
  exact Nat.mul_lt_mul'' (pv_lt P σ) (qv_lt P σ)

theorem n_vp {E : State → Prop} : VP (KC P E) nPart (KN P E) := by
  have b : ∀ σ, pv P σ < 2 ^ (32 * P.W - 1) := fun σ =>
    Nat.lt_of_lt_of_le (pv_lt P σ) (Nat.pow_le_pow_right (by decide) (by simp only [KP.W]; omega))
  refine (St.pmulFrom myQ_taint mxP_taint maZero_taint nMa_taint St.pcnt8 (n := 8 * P.K)
    (fun σ pre => by have := pre.k1; have := pre.k2; omega)
    (by simp) (by simp) (by simp) (by simp) (by simp) (by decide) (by decide)
    (by intro j hj; mem_cases <;> decide) (by intro j hj; mem_cases <;> decide) fun σ _ => ?_).mono
    (fun _ _ h => h) fun σ s h => h.mono (fun j hj => ⟨by mem_sub, ?_⟩) (fun d hd => ⟨hd, rfl⟩)
  · simp (config := {decide := true}) only [upd, ↓reduceIte, AH_zero, AH_mod, AH_P]
    refine ⟨trivial, Nat.two_pow_pos _, b σ, ?_⟩
    rw [Nat.mul_comm, ← Nat.pow_succ]; exact Nat.pow_le_pow_right (by decide) (by simp only [KP.W]; omega)
  · have phi : (0 + qv P σ % 2 ^ (8 * P.K) * pv P σ) % 2 ^ (32 * P.W - 1) = nv P σ := by
      rw [Nat.zero_add, Nat.mod_eq_of_lt (qv_lt P σ), Nat.mul_comm]
      refine Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (nv_lt P σ) (Nat.pow_le_pow_right (by decide) ?_))
      simp only [KP.W]; omega
    mem_cases <;> simp (config := {decide := true}) only [upd, ↓reduceIte, AH_zero, AH_mod, AH_P, AH_Q, phi]

/-- The mask of the checks. -/
theorem mask_vp {E : State → Prop} : VP (KN P E) maskPart (KF P E) := by
  simp only [maskPart]
  refine VP.assoc (VP.seq (St.pltS ltTop_taint (by simp) (by simp) (by decide) (by decide) (by decide)) ?_)
  refine VP.seq (St.pbitOf bitQo_taint (by simp) (by decide)) ?_
  refine VP.assoc (VP.seq (St.pltS ltE3_taint (by simp) (by simp) (by decide) (by decide) (by decide)) ?_)
  refine VP.assoc (VP.seq (St.pltS ltEv_taint (by simp) (by simp) (by decide) (by decide) (by decide)) ?_)
  let T := fun σ : State => decide (nv P σ < 2 ^ (16 * P.K - 1))
  let M1 := fun σ => !T σ && okv P σ
  let M2 := fun σ => M1 σ && decide (qg P σ = 1)
  let M3 := fun σ => M2 σ && decide (pv P σ % 2 = 1)
  let M4 := fun σ => M3 σ && decide (qv P σ % 2 = 1)
  let M5 := fun σ : State => M4 σ && decide (P.e % 2 = 1)
  let E3 := fun _ : State => !decide (P.e < 3) && decide (P.e < 2 ^ 33)
  refine VP.block_append (l₁ := andNotS sMask sTop sOk) (St.pandNotS (X := T) (Y := fun σ => okv P σ) m1_taint
    (by simp) (by simp) (by decide) (fun σ _ => ?_) (fun σ _ => ?_)) ?_
  · simp (config := {decide := true}) only [upd, ↓reduceIte, AH_top]; rfl
  · simp (config := {decide := true}) only [V5, VQ, upd, ↓reduceIte]
  refine VP.block_append (l₁ := andS sMask sMask sGq) (St.pandS (X := M1) (Y := fun σ => decide (qg P σ = 1)) m2_taint
    (by simp) (by simp) (by decide) (fun σ _ => by rw [upd_self]) (fun σ _ => ?_)) ?_
  · simp (config := {decide := true}) only [VQ, upd, ↓reduceIte]
  refine VP.block_append (l₁ := andS sMask sMask sPo) (St.pandS (X := M2) (Y := fun σ => decide (pv P σ % 2 = 1))
    m3_taint (by simp) (by simp) (by decide) (fun σ _ => by rw [upd_self]) (fun σ _ => ?_)) ?_
  · simp (config := {decide := true}) only [VQ, upd, ↓reduceIte]
  refine VP.block_append (l₁ := andS sMask sMask sQo) (St.pandS (X := M3) (Y := fun σ => decide (qv P σ % 2 = 1))
    m4_taint (by simp) (by simp) (by decide) (fun σ _ => by rw [upd_self]) (fun σ _ => ?_)) ?_
  · simp (config := {decide := true}) only [upd, ↓reduceIte, AH_Q]
  refine VP.block_append (l₁ := andS sMask sMask sEo) (St.pandS (X := M4) (Y := fun σ => decide (P.e % 2 = 1))
    m5_taint (by simp) (by simp) (by decide) (fun σ _ => by rw [upd_self]) (fun σ _ => ?_)) ?_
  · simp (config := {decide := true}) only [V5, VQ, VE, upd, ↓reduceIte]
  refine VP.block_append (l₁ := andNotS sE3 sE3 sEv) (St.pandNotS (X := fun _ => decide (P.e < 3))
    (Y := fun _ => decide (P.e < 2 ^ 33)) m6_taint (by simp) (by simp) (by decide) (fun σ _ => ?_) (fun σ _ => ?_)) ?_
  · simp (config := {decide := true}) only [upd, ↓reduceIte, AH_e, AH_three]
  · simp (config := {decide := true}) only [upd, ↓reduceIte, AH_e, AH_c33]
  refine (St.pandS (X := M5) (Y := E3) m7_taint (by simp) (by simp) (by decide)
    (fun σ _ => by simp (config := {decide := true}) only [upd, ↓reduceIte] <;> rfl) (fun σ _ => by rw [upd_self])).mono
    (fun _ _ h => h) fun σ s h => h.mono (fun j hj => ⟨by mem_sub, ?_⟩)
      (fun d hd => ⟨by simp only [List.mem_singleton] at hd; simp [hd], ?_⟩)
  · mem_cases <;> simp (config := {decide := true}) only [upd, ↓reduceIte]
  · simp only [List.mem_singleton] at hd; subst hd
    rw [upd_self, upd_self]
    rfl

end

end VG.Proof.RsaKeyGen.Arm.Key
