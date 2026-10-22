module

public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Fin
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Load1
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Trial2
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Seqs
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.St

/-! # DSA's probable-prime test on ARMv7: the body (`body_vp`)

The candidate loaded, trial division, and then Miller–Rabin or 2: which is
public, as the candidate is (`compv_pub`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.Rsa (b2n)
open VG.Proof.MillerRabin.Arm (RoundImpl)

section
variable {P : CP}

theorem compv_pub {σ : State} (pre : In P σ) :
    compv P σ = Spec.RsaKeyGen.obviouslyComposite P.bits P.cand := by
  unfold compv; rw [pre.cand]

theorem b2n_eq0' (b : Bool) : decide (b2n b = 0) = !b := by cases b <;> rfl

/-- The body: the status and the octets read of the test. -/
theorem body_vp (v : RoundImpl) {E : State → Prop} (hE : ∀ σ, E σ → In P σ) :
    VP (fun σ s => E σ ∧ Bk P σ s) (Impl.Dsa.Arm.ProbablePrime.body v.name v.code)
      (RF P E (statD P) (usedD P)) := by
  unfold Impl.Dsa.Arm.ProbablePrime.body
  rw [List.append_assoc]
  refine VP.seqs_app (List.cons_ne_nil _ _) (by simp) loadC_vp
    (VP.seqs_app (fun h => by simp [trial] at h) (List.cons_ne_nil _ _)
      (VP.mono (F := S1 P E) (trial_vp (E := E))
        (fun σ s (h : S0 P E σ s) => h.mono (fun j hj => ⟨by mem_sub, rfl⟩) fun d hd => ⟨hd, rfl⟩)
        fun _ _ h => h) ?_)
  have k2 : ∀ σ, E σ → V2 P σ sTr = b2n (Spec.RsaKeyGen.obviouslyComposite P.bits P.cand) := fun σ e => by
    simp only [V2, upd_self]; rw [compv_pub (hE σ e)]
  refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [isa_eq, isa_eq, h₁.2, h₂.2, k2 σ₁ h₁.1.1, k2 σ₂ h₂.1.1]) ?_ ?_
  · refine VP.ofImp (p := Spec.RsaKeyGen.obviouslyComposite P.bits P.cand = false) (fun σ s h => by
      have t := h.2; rw [isa_eq, h.1.2, k2 σ h.1.1.1, b2n_eq0'] at t; simpa using t) fun hc => ?_
    exact (mrPart_vp v (E := E) fun σ e => ⟨hE σ e, by rw [EM, compv_pub (hE σ e), hc]⟩).mono
      (fun σ s h => h.1.1) fun _ _ h => h
  · refine VP.ofImp (p := Spec.RsaKeyGen.obviouslyComposite P.bits P.cand = true) (fun σ s h => by
      have t := h.2; rw [isa_eq, h.1.2, k2 σ h.1.1.1, b2n_eq0'] at t; simpa using t) fun hc => ?_
    exact (composite_vp (E := E) fun σ e => ⟨hE σ e, by rw [compv_pub (hE σ e), hc]⟩).mono
      (fun σ s h => h.1.1) fun _ _ h => h

end

end VG.Proof.Dsa.Arm.Prime
