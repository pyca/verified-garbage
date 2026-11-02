module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Fin4
public import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Front
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Trial2
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Fin2
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Seqs
import VerifiedGarbage.Proof.Rsa.Arm.RvCand4

/-! # A candidate on ARMv7: the body after the entry (`candBody_vp`)

Each branch the candidate takes is public (`P.sch`); each ends with the
contract's status, `out` and `used` (`stR`, `outR`, `usedR`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Cand
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.Rsa (b2n)
open VG.Proof.MillerRabin.Arm (RoundImpl)

section
variable {P : CP}

theorem b2n_eq1 (b : Bool) : decide (b2n b = 1) = b := by cases b <;> rfl
theorem b2n_eq0 (b : Bool) : decide (b2n b = 0) = !b := by cases b <;> rfl

theorem usedR_drop {σ : State} (hL : P.L ≤ P.rl) {x : Spec.RsaKeyGen.Candidate}
    (h : res P σ = some (x, (rB P σ).drop P.L)) : usedR P σ = P.L := by
  unfold usedR; rw [h]; dsimp only; rw [List.length_drop, rB_length]; omega

theorem outR_close {σ : State} (h : res P σ = some (.close, (rB P σ).drop P.L)) :
    outR P σ = List.replicate P.L 0 := by unfold outR; rw [h]
theorem outR_rej {σ : State} (h : res P σ = some (.rejected, (rB P σ).drop P.L)) :
    outR P σ = List.replicate P.L 0 := by unfold outR; rw [h]

/-- After the candidate's octets: the branches. -/
theorem main_vp [VG.Proof.Rsa.Arm.Keys.InvLaw] (v : RoundImpl) {E : State → Prop} (hE : ∀ σ, E σ → In P σ ∧ P.L ≤ P.rl) :
    VP (fun σ s => E σ ∧ Bk P σ s) (main v.name v.code) (RF P E (stR P) (outR P) (usedR P)) := by
  unfold main
  rw [List.append_assoc]
  refine VP.seqs_app (List.cons_ne_nil _ _) (List.cons_ne_nil _ _) (loadC_vp hE)
    (VP.seqs_app (List.cons_ne_nil _ _) (List.cons_ne_nil _ _) (closeCheck_vp fun σ e => (hE σ e).1) ?_)
  have k1 : ∀ σ, E σ → V1 P σ sCl = b2n P.sch.close := fun σ e => by
    simp only [V1, upd_self]; rw [sched_close (hE σ e).1 (hE σ e).2]
  refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [isa_eq, isa_eq, h₁.2, h₂.2, k1 σ₁ h₁.1.1, k1 σ₂ h₂.1.1]) ?_ ?_
  · refine VP.ofImp (p := P.sch.close = true) (fun σ s h => by
      have t := h.2; rw [isa_eq, h.1.2, k1 σ h.1.1.1, b2n_eq1] at t; simpa using t) fun hc => ?_
    refine (finUsed_vp finTail2_taint (by decide) (by decide) (by simp)).mono (fun σ s h => h.1.1)
      fun σ s ⟨e, b, r0, o, u⟩ => ?_
    obtain ⟨pre, hL⟩ := hE σ e
    have hr := res_close pre hL (by rw [← sched_close pre hL, hc])
    refine ⟨e, b, by rw [r0]; unfold stR; rw [hr]; rfl, by rw [o, outR_close hr], ?_⟩
    rw [u, usedR_drop hL hr]
    simp (config := {decide := true}) only [V1, V0, upd, ↓reduceIte]
  refine VP.ofImp (p := P.sch.close = false) (fun σ s h => by
    have t := h.2; rw [isa_eq, h.1.2, k1 σ h.1.1.1, b2n_eq1] at t; simpa using t) fun hc => ?_
  have cl : ∀ σ, E σ → clv P σ = false := fun σ e => by rw [← sched_close (hE σ e).1 (hE σ e).2, hc]
  refine (VP.seqs_app (H := RF P (fun σ => E σ ∧ clv P σ = false) (stR P) (outR P) (usedR P))
    (fun h => by simp [trial] at h) (List.cons_ne_nil _ _)
    (trial_vp (E := fun σ => E σ ∧ clv P σ = false)) ?_).mono
    (fun σ s ⟨⟨h, _⟩, _⟩ => h.weaken fun e => ⟨e, cl σ e⟩) (G' := RF P E (stR P) (outR P) (usedR P))
    fun σ s ⟨e, h⟩ => ⟨e.1, h⟩
  have k2 : ∀ σ, E σ ∧ clv P σ = false → V2 P σ sTr = b2n P.sch.comp := fun σ e => by
    simp only [V2, upd_self]; rw [sched_comp (hE σ e.1).1 (hE σ e.1).2 e.2]
  refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [isa_eq, isa_eq, h₁.2, h₂.2, k2 σ₁ h₁.1.1, k2 σ₂ h₂.1.1]) ?_ ?_
  · refine VP.ofImp (p := P.sch.comp = false) (fun σ s h => by
      have t := h.2; rw [isa_eq, h.1.2, k2 σ h.1.1.1, b2n_eq0] at t; simpa using t) fun hco => ?_
    have co : ∀ σ, E σ ∧ clv P σ = false → compv P σ = false := fun σ e => by
      rw [← sched_comp (hE σ e.1).1 (hE σ e.1).2 e.2, hco]
    refine (VP.seqs_app (H := RF P (fun σ => (E σ ∧ clv P σ = false) ∧ compv P σ = false) (stR P) (outR P) (usedR P))
      (List.cons_ne_nil _ _) (List.cons_ne_nil _ _)
      (gcdCheck_vp (E := fun σ => (E σ ∧ clv P σ = false) ∧ compv P σ = false) fun σ e => (hE σ e.1.1).1) ?_).mono
      (fun σ s ⟨⟨h, _⟩, _⟩ => h.weaken fun e => ⟨e, co σ e⟩)
      (G' := RF P (fun σ => E σ ∧ clv P σ = false) (stR P) (outR P) (usedR P)) fun σ s ⟨e, h⟩ => ⟨e.1, h⟩
    have k3 : ∀ σ, (E σ ∧ clv P σ = false) ∧ compv P σ = false → V3 P σ sG = b2n (!P.sch.gbad) := fun σ e => by
      simp only [V3, upd_self]; rw [sched_gbad (hE σ e.1.1).1 (hE σ e.1.1).2 e.1.2 e.2, Bool.not_not]
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [isa_eq, isa_eq, h₁.2, h₂.2, k3 σ₁ h₁.1.1, k3 σ₂ h₂.1.1]) ?_ ?_
    · refine VP.ofImp (p := P.sch.gbad = false) (fun σ s h => by
        have t := h.2; rw [isa_eq, h.1.2, k3 σ h.1.1.1, b2n_eq1] at t; simpa using t) fun hg => ?_
      have gd : ∀ σ, (E σ ∧ clv P σ = false) ∧ compv P σ = false → gv P σ = true := fun σ e => by
        have := sched_gbad (hE σ e.1.1).1 (hE σ e.1.1).2 e.1.2 e.2; rw [hg] at this
        revert this; cases gv P σ <;> decide
      refine (mrPart_vp v (E := fun σ => ((E σ ∧ clv P σ = false) ∧ compv P σ = false) ∧ gv P σ = true)
        fun σ e => ⟨(hE σ e.1.1.1).1, (hE σ e.1.1.1).2, e.1.1.2, e.1.2, e.2⟩).mono
        (fun σ s ⟨⟨h, _⟩, _⟩ => h.weaken fun e => ⟨e, gd σ e⟩) fun σ s ⟨e, b, r0, o, u⟩ => ?_
      obtain ⟨hs, ho, hu⟩ := res_mr (hE σ e.1.1.1).1 ⟨(hE σ e.1.1.1).2, e.1.1.2, e.1.2, e.2⟩
      exact ⟨e.1, b, by rw [r0, hs], by rw [o, ho], by rw [u, hu]⟩
    · refine VP.ofImp (p := P.sch.gbad = true) (fun σ s h => by
        have t := h.2; rw [isa_eq, h.1.2, k3 σ h.1.1.1, b2n_eq1] at t; simpa using t) fun hg => ?_
      refine (finUsed_vp finTail3_taint (by decide) (by decide) (by simp)).mono (fun σ s h => h.1.1)
        fun σ s ⟨e, b, r0, o, u⟩ => ?_
      obtain ⟨pre, hL⟩ := hE σ e.1.1
      have g : gv P σ = false := by
        have := sched_gbad pre hL e.1.2 e.2; rw [hg] at this
        revert this; cases gv P σ <;> decide
      have hr := res_rej pre hL e.1.2 (by rw [e.2, g]; rfl)
      refine ⟨e, b, by rw [r0]; unfold stR; rw [hr]; rfl, by rw [o, outR_rej hr], ?_⟩
      rw [u, usedR_drop hL hr]
      simp (config := {decide := true}) only [V3, V2, V1, V0, upd, ↓reduceIte]
  · refine VP.ofImp (p := P.sch.comp = true) (fun σ s h => by
      have t := h.2; rw [isa_eq, h.1.2, k2 σ h.1.1.1, b2n_eq0] at t; simpa using t) fun hco => ?_
    refine (finUsed_vp finTail3_taint (by decide) (by decide) (by simp)).mono (fun σ s h => h.1.1)
      fun σ s ⟨e, b, r0, o, u⟩ => ?_
    obtain ⟨pre, hL⟩ := hE σ e.1
    have co : compv P σ = true := by rw [← sched_comp pre hL e.2, hco]
    have hr := res_rej pre hL e.2 (by rw [co]; rfl)
    refine ⟨e, b, by rw [r0]; unfold stR; rw [hr]; rfl, by rw [o, outR_rej hr], ?_⟩
    rw [u, usedR_drop hL hr]
    simp (config := {decide := true}) only [V2, V1, V0, upd, ↓reduceIte]

/-- The body after the entry. -/
theorem candBody_vp [VG.Proof.Rsa.Arm.Keys.InvLaw] (v : RoundImpl) :
    VP (fun σ s => In P σ ∧ Bk P σ s) (seqs [.block lenCheck, .ite .eq finNone (main v.name v.code)])
      (RF P (In P) (stR P) (outR P) (usedR P)) := by
  simp only [seqs]
  refine VP.seq lenCheck_vp (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [isa_eq, isa_eq, h₁.2, h₂.2]) ?_ ?_)
  · refine VP.ofImp (p := P.rl < P.L) (fun σ s h => by
      have t := h.2; rw [isa_eq, h.1.2] at t; simpa using t) fun hl => ?_
    refine finNone_vp.mono (fun σ s h => h.1.1) fun σ s ⟨e, b, r0, o, u⟩ => ?_
    have hr := res_none e hl
    exact ⟨e, b, by rw [r0]; unfold stR; rw [hr]; rfl, by rw [o]; unfold outR; rw [hr],
      by rw [u]; unfold usedR; rw [hr]⟩
  · refine VP.ofImp (p := ¬ P.rl < P.L) (fun σ s h => by
      have t := h.2; rw [isa_eq, h.1.2] at t; simpa using t) fun hl => ?_
    exact (main_vp v (E := In P) fun σ e => ⟨e, by omega⟩).mono (fun σ s h => h.1.1) fun _ _ h => h

end

end VG.Proof.RsaKeyGen.Arm.Cand
