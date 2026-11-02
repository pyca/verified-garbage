module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Mid1
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Taint2
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Div
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Mul
import VerifiedGarbage.Proof.Rsa.Arm.RvRest
import VerifiedGarbage.Proof.Rsa.RecoverSubtract

/-! # An RSA key on ARMv7: `d` for an odd `e ≥ 3` (`dOdd_vp`) -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Key
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Key VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP sub32 VP.of_imp)
open VG.Proof.Rsa (b2n)

section
variable {P : KP}

/-- `e` odd, at least 3. -/
abbrev EOdd (P : KP) (E : State → Prop) (σ : State) : Prop := E σ ∧ P.e ≠ 0 ∧ P.e ≠ 1 ∧ P.e % 2 = 1

theorem dOdd_vp [VG.Proof.Rsa.Arm.Keys.InvLaw] {E : State → Prop} : VP (SE P (EOdd P E)) dOdd (G4 P (EOdd P E)) := by
  simp only [dOdd, seqs, List.cons_append, List.nil_append]
  refine VP.seq (St.pinv mE_taint l0_taint (by simp) (by simp) (by simp) (by simp) (by intro j hj; mem_cases <;> decide)
    (by decide) fun σ ⟨_, e0, e1, eo⟩ => ⟨AS3_zero, AS3_one, by rw [AS3_e]; exact eo, by rw [AS3_e]; omega⟩) ?_
  refine VP.seq (St.peqS eqG_taint (by simp) (by simp) (by decide) (by decide) (by decide) (by decide)) ?_
  refine VP.assoc (VP.seq (St.pltS ltL2_taint (by simp) (by simp) (by decide) (by decide) (by decide)) ?_)
  refine VP.seq (St.pandNotS (X := fun σ => decide (lv P σ < 2))
    (Y := fun σ => decide ((ivr P.W (lv P σ) P.e).2.1 = 1)) okOdd_taint (by simp) (by simp) (by decide)
    (fun σ _ => by simp (config := {decide := true}) only [upd, ↓reduceIte, AH_two, AS3_L])
    (fun σ _ => by simp (config := {decide := true}) only [upd, ↓reduceIte, AH_one, AH_e])) ?_
  refine VP.seq (St.psub3 tt_taint (by decide) (by simp) (by simp) (by decide) (by decide)) ?_
  refine VP.seq (St.pmulFrom myT_taint mxL_taint maOne_taint qdMa_taint St.pmov64 (n := 64)
    (fun _ _ => ⟨by decide, by decide⟩) (by simp) (by simp) (by simp) (by simp) (by simp) (by decide) (by decide)
    (by intro j hj; mem_cases <;> decide) (by intro d hj; mem_cases <;> decide) fun σ _ => ?_) ?_
  · have wge : 4 ≤ P.W := by simp only [KP.W]; omega
    simp (config := {decide := true}) only [upd, ↓reduceIte, AH_zero, AH_one, AH_mod, AS3_L]
    refine ⟨trivial, Nat.one_lt_two_pow (by omega), ?_, ?_⟩
    · have := lv_lt P σ
      exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by simp only [KP.W]; omega))
    · rw [Nat.mul_comm, ← Nat.pow_succ]; exact Nat.pow_le_pow_right (by decide) (by omega)
  refine VP.seq (St.pdivBy dvE_taint hdrQd_taint (by decide) (by simp) (by simp) (by intro j hj; mem_cases <;> decide)
    fun σ ⟨_, e0, _, _⟩ => by simp (config := {decide := true}) only [upd, ↓reduceIte, AH_e]; omega) ?_
  refine (St.pcopy dQd_taint (by decide) (by simp) (by decide)).mono (fun _ _ h => h) fun σ s h => h.mono
    (fun j hj => ⟨by mem_sub, ?_⟩) (fun j hj => ⟨by mem_sub, ?_⟩)
  · obtain ⟨_, e0, e1, eo⟩ := h.1
    have : dv P σ = ((1 + sub32 P.W P.e (ivr P.W (lv P σ) P.e).2.2.2 % 2 ^ 64 * lv P σ) % 2 ^ (32 * P.W - 1)) / P.e := by
      unfold dv; rw [ite_eq_right e0, ite_eq_right e1, ite_eq_left eo]
    rw [this]
    mem_cases <;> simp (config := {decide := true}) only [upd, ↓reduceIte, AH_e, AH_one, AH_mod, AS3_L]
  · obtain ⟨_, e0, e1, eo⟩ := h.1
    have : okv P σ = (!decide (lv P σ < 2) && decide ((ivr P.W (lv P σ) P.e).2.1 = 1)) := by
      unfold okv; rw [ite_eq_right e0, ite_eq_right e1, ite_eq_left eo]
    rw [this]
    mem_cases <;> simp (config := {decide := true}) only [upd, ↓reduceIte]

end

end VG.Proof.RsaKeyGen.Arm.Key
