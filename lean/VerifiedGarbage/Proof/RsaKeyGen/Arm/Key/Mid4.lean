module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Mid1
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Taint2
import VerifiedGarbage.Proof.Rsa.Arm.RvRest
import VerifiedGarbage.Proof.Rsa.RecoverSubtract

/-! # An RSA key on ARMv7: `d` for an even `e` (`dEven_vp`) -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Key
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Key VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP sub32 VP.of_imp)
open VG.Proof.Rsa (b2n)

section
variable {P : KP}

/-- `e` even and not 0. -/
abbrev EEven (P : KP) (E : State → Prop) (σ : State) : Prop := E σ ∧ P.e ≠ 0 ∧ P.e ≠ 1 ∧ ¬ P.e % 2 = 1

theorem mE_odd (P : KP) (σ : State) : mE P σ % 2 = 1 ∧ 1 < mE P σ := by
  unfold mE; split
  · rename_i h; exact ⟨h.1, by omega⟩
  · exact ⟨rfl, by decide⟩

theorem mE_eq (P : KP) (σ : State) :
    (if b2n (!decide (lv P σ < 3) && decide (lv P σ % 2 = 1)) = 0 then 3 else lv P σ) = mE P σ := by
  unfold mE
  by_cases h3 : lv P σ < 3 <;> by_cases ho : lv P σ % 2 = 1 <;> simp [h3, ho, b2n]

theorem dEven_vp [VG.Proof.Rsa.Arm.Keys.InvLaw] {E : State → Prop} : VP (SE P (EEven P E)) dEven (G4 P (EEven P E)) := by
  simp only [dEven, List.cons_append, List.nil_append]
  refine VP.seq (St.pbitOf bitLo_taint (by simp) (by decide)) ?_
  refine VP.assoc (VP.seq (St.pltS ltL3_taint (by simp) (by simp) (by decide) (by decide) (by decide)) ?_)
  refine VP.seq (St.pandNotS (X := fun σ => decide (lv P σ < 3)) (Y := fun σ => decide (lv P σ % 2 = 1))
    good_taint (by simp) (by simp) (by decide)
    (fun σ _ => by simp (config := {decide := true}) only [upd, ↓reduceIte, AH_three])
    (fun σ _ => by simp (config := {decide := true}) only [upd, ↓reduceIte])) ?_
  refine VP.seq (St.psel selME_taint (by decide) (by simp) (by simp) (by decide) (by decide) (by simp)
    fun _ _ => by rw [upd_self]; exact b2n_le' _) ?_
  refine VP.seq (G := St P (EEven P E) _ (1 :: 3 :: aTmp2 :: L3) _ _) ((St.pinv mT2_taint e0_taint (by simp) (by simp) (by simp) (by simp)
    (by intro j hj; mem_cases <;> decide) (by decide) fun σ _ => ?_).mono (fun _ _ h => h)
      fun σ s h => h.sub (L' := 1 :: 3 :: aTmp2 :: L3) (by intro j hj; mem_sub)
        (fun d hd => hd)) ?_
  · simp (config := {decide := true}) only [upd, ↓reduceIte, AH_zero, AH_one, AH_three, mE_eq]
    exact ⟨trivial, trivial, (mE_odd P σ).1, (mE_odd P σ).2⟩
  refine VP.seq (St.peqS (d := sG) (a := 1) (b := aOne) eqG_taint (by simp) (by simp) (by decide) (by decide)
    (by decide) (by decide)) ?_
  refine VP.seq (St.pandS (d := sOk) (a := sGood) (b := sG) (X := fun σ => !decide (lv P σ < 3) && decide (lv P σ % 2 = 1))
    (Y := fun σ => decide ((ivr P.W P.e (mE P σ)).2.1 = 1)) okEven_taint (by simp) (by simp) (by decide)
    (fun σ _ => by simp (config := {decide := true}) only [upd, ↓reduceIte])
    (fun σ _ => by simp (config := {decide := true}) only [upd, ↓reduceIte, AH_one, AH_e, AH_three, mE_eq])) ?_
  refine (St.pcopy d3_taint (by decide) (by simp) (by decide)).mono (fun _ _ h => h) fun σ s h => h.mono
    (fun j hj => ⟨by mem_sub, ?_⟩) (fun j hj => ⟨by mem_sub, ?_⟩)
  · obtain ⟨_, e0, e1, eo⟩ := h.1
    have : dv P σ = (ivr P.W P.e (mE P σ)).2.2.2 := by
      unfold dv; rw [ite_eq_right e0, ite_eq_right e1, ite_eq_right eo]
    rw [this]
    mem_cases <;> simp (config := {decide := true}) only [upd, ↓reduceIte, AH_e, AH_three, mE_eq]
  · obtain ⟨_, e0, e1, eo⟩ := h.1
    have : okv P σ = ((!decide (lv P σ < 3) && decide (lv P σ % 2 = 1)) &&
        decide ((ivr P.W P.e (mE P σ)).2.1 = 1)) := by
      unfold okv; rw [ite_eq_right e0, ite_eq_right e1, ite_eq_right eo]
    rw [this]
    mem_cases <;> simp (config := {decide := true}) only [upd, ↓reduceIte]

end

end VG.Proof.RsaKeyGen.Arm.Key
