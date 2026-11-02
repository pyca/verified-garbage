module

import VerifiedGarbage.Proof.Rsa.Arm.RvFusedSearch
public import VerifiedGarbage.Proof.Rsa.Arm.RvBody
import VerifiedGarbage.Proof.Rsa.Arm.RvRest
import VerifiedGarbage.Proof.Rsa.RecoverTries
public import VerifiedGarbage.Proof.Rsa.Arm.RvFusedCandidate

/-! Connect the fused search to shared factor extraction and the public result. -/

@[expose] public section
namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover
open VG.Proof.Rsa.Arm.Keys
open VG.Impl.Rsa.Arm.RecoverFused

section
variable {P : RP}

theorem fusedFin_vp [VG.Proof.Rsa.Arm.Keys.InvLaw] (hn : P.n % 2 = 1 ∧ 1 < P.n) (nl : P.n < 2 ^ (32 * P.w))
    {E : State → Prop} :
    VP (FCF P E (Jl P)) fin (Fe (F := fusedFinish P (Jl P)) P E) := by
  refine (finWith_vp hn nl (fusedFinish P (Jl P))).mono
    (fun σ s h => h.mono (fun k hk => ⟨hk, rfl⟩) (fun k hk => by simp at hk) ?_)
    (fun _ _ h => h)
  intro d hd
  simp only [List.mem_singleton] at hd; subst hd
  exact ⟨by decide, rfl⟩

theorem fusedRest_vp [VG.Proof.Rsa.Arm.Keys.InvLaw] (hv : Spec.Rsa.modulusValid P.n P.K = true) :
    VP (RestStart P) VG.Impl.Rsa.Arm.RecoverFused.rest (Res P) := by
  refine VP.of_imp (p := Sizes P ∧ 1 ≤ P.nt ∧ P.nt ≤ 100 ∧ P.B.toNat + P.Z ≤ 2 ^ 32 ∧
    P.el + P.dl ≤ 2 * P.K ∧ 0 < P.el + P.dl ∧ P.n < 2 ^ (32 * P.w) ∧ 2 ≤ P.K)
      (fun σ s ⟨⟨pre, go⟩, _⟩ => ?_)
      fun ⟨sz, nt1, nt100, nowrap, lengths, positive, nl, hk⟩ => ?_
  · obtain ⟨_, _, _, tries⟩ := rest_facts hv pre go
    have el := pre.el2; have dl := pre.dl2; have ep := pre.el1; have kp := pre.k1
    refine ⟨pre.sizes, ?_, ?_, pre.fS, by omega, by omega, n_lt pre, by omega⟩
    · rw [← tries]; exact VG.Proof.Rsa.go_pos _ _ _ _ (Nat.le_refl _)
    · rw [← tries]; exact VG.Proof.Rsa.go_le _ _ _ _ (Nat.le_refl _)
  obtain ⟨odd, large, above⟩ := valid_facts hv hk
  have hn : P.n % 2 = 1 ∧ 1 < P.n := ⟨odd, large⟩
  simp only [VG.Impl.Rsa.Arm.RecoverFused.rest, seqs]
  have setup : VP (RestStart P) mont
      (fun σ s => (In P σ ∧ goOn P σ = true) ∧
        KM P σ (fusedAW P σ) [wM] (fun _ => 0) [] s) := by
    refine (montFull_vp hn sz false).mono (fun σ s ⟨e, h, hw⟩ => ⟨e, ?_, hw⟩)
      (fun σ s ⟨e, h, hm, hw⟩ => ⟨e, ?_, hm, hw⟩)
    · exact h.mono (fun k hk => ⟨hk, rfl⟩) (fun k hk => by
        simp only [montWide, Bool.false_eq_true, ite_false, List.mem_singleton] at hk
        subst hk
        exact ⟨by simp, by simp [AWh, AWs, upd]⟩)
        (fun d hd => by simp [montInitSlots] at hd)
    · exact h.mono (fun k hk => ⟨hk, rfl⟩) (fun k hk => by
        simp only [List.mem_singleton] at hk; subst hk
        exact ⟨by simp [montWide], by simp [AWh, fusedAW, upd]⟩)
        (fun d hd => by simp at hd)
  refine (VP.seq setup
    (VP.seq (fusedCandidates_vp hn above sz nowrap lengths positive nt1 nt100
      (fun σ e => ⟨e.1, e.2, (rest_facts hv e.1 e.2).2.2.2⟩))
      (fusedFin_vp hn nl))).mono (fun _ _ h => h) fun σ s h => ?_
  obtain ⟨⟨pre, go⟩, previous⟩ := h.1
  refine finish_resWith h (resultWith_eq hv large nl pre go previous nt1 (fusedFinish P (Jl P)) ?_)
  calc
    (if (fusedFinish P (Jl P)).ok σ then some ((fusedFinish P (Jl P)).value σ) else none) =
        fusedResult P σ (Jl P) := by
      cases result : fusedResult P σ (Jl P) <;> simp [fusedFinish, result]
    _ = Spec.Rsa.recoverStep P.n (tv P σ) (rv P σ) (Jl P + 2) :=
      fusedResult_eq pre go large (Jl P)

theorem fused_body_vp [VG.Proof.Rsa.Arm.Keys.InvLaw] : BodyVerified VG.Impl.Rsa.Arm.RecoverFused.body := by
  intro P
  exact bodyWith_vp VG.Impl.Rsa.Arm.RecoverFused.valid
    (fun hv => validWith_vp hv VG.Impl.Rsa.Arm.RecoverFused.rest (fusedRest_vp hv))

end
end VG.Proof.Rsa.Arm.Recover
