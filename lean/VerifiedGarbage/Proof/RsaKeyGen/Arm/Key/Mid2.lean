module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Mid1
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # An RSA key on ARMv7: `d` for `e = 0` and `e = 1` -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Key
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Key VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP sub32 VP.of_imp)
open VG.Proof.Rsa (b2n)

section
variable {P : KP}

theorem dZero_vp {E : State → Prop} :
    VP (SE P (fun σ => E σ ∧ P.e = 0)) (.block dZero) (G4 P (fun σ => E σ ∧ P.e = 0)) := by
  refine St.pdZero.mono (fun _ _ h => h) fun σ s h => h.mono
    (fun j hj => ⟨by mem_sub, ?_⟩) (fun d hd => ⟨hd, ?_⟩)
  · have e0 := h.1.2
    have : dv P σ = 0 := by unfold dv; rw [ite_eq_left e0]
    rw [this]
    mem_cases <;> simp (config := {decide := true}) only [upd, ↓reduceIte, AH_D]
  · have e0 := h.1.2
    have : okv P σ = false := by unfold okv; rw [ite_eq_left e0]
    rw [this]

theorem dOne_vp {E : State → Prop} :
    VP (SE P (fun σ => E σ ∧ P.e = 1)) dOne (G4 P (fun σ => E σ ∧ P.e = 1)) := by
  simp only [dOne, seqs]
  refine VP.seq (St.peqS eqG1_taint (by simp) (by simp) (by decide) (by decide) (by decide) (by decide)) ?_
  refine VP.seq (St.pnotS (X := fun σ => decide (lv P σ = 1)) notOk_taint (by simp) (by decide) fun σ _ => by
    simp only [upd_self, AS3_one]) ?_
  refine (St.pcopy dOne_taint (by decide) (by simp) (by decide)).mono (fun _ _ h => h) fun σ s h => h.mono
    (fun j hj => ⟨by mem_sub, ?_⟩) (fun j hj => ⟨by mem_sub, ?_⟩)
  · have e1 := h.1.2
    have : dv P σ = 1 := by unfold dv; rw [ite_eq_right (by omega), ite_eq_left e1]
    rw [this]
    mem_cases <;> simp (config := {decide := true}) only [upd, ↓reduceIte, AH_one]
  · have e1 := h.1.2
    have : okv P σ = !decide (lv P σ = 1) := by unfold okv; rw [ite_eq_right (by omega), ite_eq_left e1]
    rw [this]
    mem_cases <;> simp (config := {decide := true}) only [upd, ↓reduceIte]

end

end VG.Proof.RsaKeyGen.Arm.Key
