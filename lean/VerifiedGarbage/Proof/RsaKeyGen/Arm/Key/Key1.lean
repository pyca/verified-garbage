module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Mid5
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Result
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Taint3
import VerifiedGarbage.Proof.Rsa.Arm.RvRest
import VerifiedGarbage.Proof.Rsa.RecoverSubtract

/-! # An RSA key on ARMv7: `qInv` (`qinv_vp`) -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Key
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Key VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP sub32 VP.of_imp)
open VG.Proof.Rsa (b2n)

/-- The arrays after the check of `d`. -/
abbrev A5 (P : KP) (σ : State) : Nat → Nat := upd (upd (AS3 P σ) aD (dv P σ)) aC (1 + 2 ^ (8 * P.K))
abbrev L5 : List Nat := aC :: aD :: L3

/-- The flags after `qInv`. -/
def VQ (P : KP) (σ : State) : Nat → Nat :=
  upd (upd (V5 P σ) sPo (b2n (decide (pv P σ % 2 = 1)))) sGq (b2n (decide (qg P σ = 1)))

abbrev KQ (P : KP) (E : State → Prop) : State → State → Prop :=
  St P E (fun σ => upd (A5 P σ) aQi (qx P σ)) (aQi :: L5) (VQ P) [sGq, sPo, sFl, sOk, sEo, sE1, sE0]

section
variable {P : KP}

theorem qM_eq (P : KP) (σ : State) :
    (if b2n (!decide (pv P σ < 3) && decide (pv P σ % 2 = 1)) = 0 then 3 else pv P σ) = qM P σ := by
  unfold qM VG.Proof.RsaKeyGen.qModP
  by_cases h3 : pv P σ < 3 <;> by_cases ho : pv P σ % 2 = 1 <;> simp [h3, ho, b2n]

theorem qinv_vp [VG.Proof.Rsa.Arm.Keys.InvLaw] {E : State → Prop} : VP (G5 P E) qinvPart (KQ P E) := by
  simp only [qinvPart, List.cons_append, List.nil_append]
  refine VP.seq (St.pbitOf bitPo_taint (by simp) (by decide)) ?_
  refine VP.assoc (VP.seq (St.pltS ltP3_taint (by simp) (by simp) (by decide) (by decide) (by decide)) ?_)
  refine VP.seq (St.pandNotS (X := fun σ => decide (pv P σ < 3)) (Y := fun σ => decide (pv P σ % 2 = 1))
    qg_taint (by simp) (by simp) (by decide)
    (fun σ _ => by simp (config := {decide := true}) only [upd, ↓reduceIte, AH_three, AH_P])
    (fun σ _ => by simp (config := {decide := true}) only [upd, ↓reduceIte, AH_P])) ?_
  refine VP.seq (St.psel selQM_taint (by decide) (by simp) (by simp) (by decide) (by decide) (by simp)
    fun _ _ => by rw [upd_self]; exact b2n_le' _) ?_
  refine VP.seq (G := St P E _ (1 :: 3 :: aTmp2 :: L5) _ _) ((St.pinv mT2_taint q0_taint (by simp) (by simp)
    (by simp) (by simp) (by intro j hj; mem_cases <;> decide) (by decide) fun σ _ => ?_).mono (fun _ _ h => h)
      fun σ s h => h.sub (by intro j hj; mem_sub) (fun d hd => hd)) ?_
  · simp (config := {decide := true}) only [upd, ↓reduceIte, AH_zero, AH_one, AH_three, AH_P, qM_eq]
    exact ⟨trivial, trivial, (qM_odd P σ).1, (qM_odd P σ).2.1⟩
  refine VP.seq (St.peqS (d := sGq) (a := 1) (b := aOne) eqGq_taint (by simp) (by simp) (by decide) (by decide)
    (by decide) (by decide)) ?_
  refine (St.pcopy qi_taint (by decide) (by simp) (by decide)).mono (fun _ _ h => h) fun σ s h => h.mono
    (fun j hj => ⟨by mem_sub, ?_⟩) (fun j hj => ⟨by mem_sub, ?_⟩)
  · mem_cases <;> simp (config := {decide := true}) only [upd, ↓reduceIte, AH_Q, AH_three, AH_P, qM_eq]
    rfl
  · mem_cases <;> simp (config := {decide := true}) only [VQ, V5, upd, ↓reduceIte, AH_Q, AH_P, AH_three, AH_one, qM_eq]
    all_goals rfl

end

end VG.Proof.RsaKeyGen.Arm.Key
