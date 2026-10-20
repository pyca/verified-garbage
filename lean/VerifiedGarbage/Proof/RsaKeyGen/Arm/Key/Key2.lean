module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Key1
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Taint3
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Taint2
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Div
import VerifiedGarbage.Proof.Bignum.Arm.WideMul
import VerifiedGarbage.Proof.Rsa.Arm.RvRest
import VerifiedGarbage.Proof.Rsa.RecoverSubtract

/-! # An RSA key on ARMv7: `dP`, `dQ` (`crt_vp`), `n` and the mask (`final_vp`) -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Key
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Key VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP sub32 VP.of_imp)
open VG.Proof.Rsa (b2n)

section
variable {P : KP} {E : State → Prop} {A : State → Nat → Nat} {L : List Nat} {V : State → Nat → Nat}
  {LS : List Nat}

/-- `divisorOf j`: `[aTmp2] := [j]`, or 1 for 0. -/
theorem St.pdivisorOf {j : Nat} (c1 : Cert (eqS sZ j aZero aTmp)) (c2 : Cert (sel aTmp2 j aOne sZ)) (hj : j ∈ L)
    (hZ : aZero ∈ L) (hO : aOne ∈ L) (hT : aTmp ∉ L) (hT2 : j ≠ aTmp2) (hls : sT ∉ LS)
    (hv : ∀ σ, E σ → A σ aZero = 0 ∧ A σ aOne = 1) :
    VP (St P E A L V LS) (divisorOf j)
      (St P E (fun σ => upd (A σ) aTmp2 (if A σ j = 0 then 1 else A σ j)) (aTmp2 :: L)
        (fun σ => upd (V σ) sZ (b2n (decide (A σ j = A σ aZero)))) (sZ :: LS)) := by
  simp only [divisorOf, seqs]
  refine VP.seq (St.peqS c1 hj hZ (by decide) hT hls (by decide)) ?_
  refine (St.psel c2 (by decide) hj hO (Ne.symm hT2) (by decide) (by simp) fun _ _ => by
    rw [upd_self]; exact b2n_le' _).mono (fun _ _ h => h) fun σ s h => h.mono (fun i hi => ⟨hi, ?_⟩)
      (fun d hd => ⟨hd, rfl⟩)
  obtain ⟨z, o⟩ := hv σ h.1
  have e : (if b2n (decide (A σ j = A σ aZero)) = 0 then A σ j else A σ aOne) = (if A σ j = 0 then 1 else A σ j) := by
    rw [z, o]; by_cases h0 : A σ j = 0 <;> simp [h0, b2n]
  rw [upd_self, e]

end

abbrev LQ : List Nat := aQi :: L5

/-- After `dP` and `dQ`. -/
abbrev KC (P : KP) (E : State → Prop) : State → State → Prop :=
  St P E (fun σ => upd (upd (upd (A5 P σ) aQi (qx P σ)) aDP (dPv P σ)) aDQ (dQv P σ)) (aDQ :: aDP :: LQ) (VQ P)
    [sGq, sPo, sFl, sOk, sEo, sE1, sE0]

section
variable {P : KP}

theorem crt_vp {E : State → Prop} : VP (KQ P E) crtPart (KC P E) := by
  simp only [crtPart, seqs]
  refine VP.seq (St.pdivisorOf zPm_taint selPm1_taint (by simp) (by simp) (by simp) (by decide) (by decide)
    (by decide) fun σ _ => ?_) ?_
  · simp (config := {decide := true}) only [upd, ↓reduceIte, AH_zero, AH_one]
  refine VP.seq (St.pcopy qdD_taint (by decide) (by simp) (by decide)) ?_
  refine VP.seq (St.pdivBy dvT2_taint hdrQd_taint (by decide) (by simp) (by simp)
    (by intro j hj; mem_cases <;> decide) fun σ _ => ?_) ?_
  · simp (config := {decide := true}) only [upd, ↓reduceIte]; split <;> omega
  refine VP.seq (G := St P E _ (aDP :: aQd :: aTmp2 :: LQ) _ _) ((St.pcopy dpDr_taint (by decide) (by simp)
    (by decide)).mono (fun _ _ h => h) fun σ s h => h.sub (by intro j hj; mem_sub) (fun d hd => hd)) ?_
  refine VP.seq (St.pdivisorOf zQm_taint selQm1_taint (by simp) (by simp) (by simp) (by decide) (by decide)
    (by decide) fun σ _ => ?_) ?_
  · simp (config := {decide := true}) only [upd, ↓reduceIte, AH_zero, AH_one]
  refine VP.seq (St.pcopy qdD_taint (by decide) (by simp) (by decide)) ?_
  refine VP.seq (St.pdivBy dvT2_taint hdrQd_taint (by decide) (by simp) (by simp)
    (by intro j hj; mem_cases <;> decide) fun σ _ => ?_) ?_
  · simp (config := {decide := true}) only [upd, ↓reduceIte]; split <;> omega
  refine (St.pcopy dqDr_taint (by decide) (by simp) (by decide)).mono (fun _ _ h => h) fun σ s h => h.mono
    (fun j hj => ⟨by mem_sub, ?_⟩) (fun j hj => ⟨by mem_sub, ?_⟩)
  · mem_cases <;> simp (config := {decide := true}) only [upd, ↓reduceIte, AH_zero, AH_Pm, AH_Qm]
    all_goals rfl
  · mem_cases <;> simp (config := {decide := true}) only [upd, ↓reduceIte]

end

end VG.Proof.RsaKeyGen.Arm.Key
