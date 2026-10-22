module

public import VerifiedGarbage.Proof.Rsa.Arm.RvFusedCandidate
public import VerifiedGarbage.Proof.Rsa.Arm.RvCand5
import VerifiedGarbage.Proof.Rsa.Arm.RvRest
import VerifiedGarbage.Proof.Rsa.Arm.RvCand2
import VerifiedGarbage.Proof.Rsa.RecoverTries

/-! Candidate-count leakage agrees with the shared RSA recovery specification. -/

@[expose] public section
namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover
open VG.Proof.Rsa.Arm.Keys
open VG.Impl.Rsa.Arm.RecoverFused
open VG.Spec.Rsa (recoverPrimes recoverStep recoverTries)

section
variable {P : RP}

/-- The candidates. -/
theorem fusedCandidates_vp (hn : P.n % 2 = 1 ∧ 1 < P.n) (h101 : 101 < P.n)
    (sz : Sizes P) (nowrap : P.B.toNat + P.Z ≤ 2 ^ 32)
    (lengths : P.el + P.dl ≤ 2 * P.K) (positive : 0 < P.el + P.dl)
    (hnt : 1 ≤ P.nt) (hnt' : P.nt ≤ 100) {E : State → Prop}
    (hE : ∀ σ, E σ → In P σ ∧ goOn P σ = true ∧ (gos P σ 100).2 = P.nt) :
    VP (fun σ s => E σ ∧ KM P σ (AWh P σ P.c) [wR, wM] (Vh P σ P.c) [sTc] s) candidates
      (FCF P (Ej P E (P.nt - 1)) (P.nt - 1)) := by
  refine VP.seq (St.pcandZero (P := P) (E := E) (A := fun _ => AM P) (L := liveM) (AW := fun σ => AWh P σ P.c)
    (LW := [wR, wM]) (V := fun σ => Vh P σ P.c) (LS := [sTc])) ?_
  have hl := VP.loop (I := fun m σ s => m ≤ P.nt ∧ FCS P (Ej P E (P.nt - m)) (P.nt - m) σ s) (body := candidate)
    (c := .ne) (Q := FCF P (Ej P E (P.nt - 1)) (P.nt - 1)) (fun n => VP.pure fun hle => ?_) (P.nt - 1)
  · refine hl.mono (fun σ s h => ⟨by omega, ?_⟩) fun _ _ h => h
    rw [show P.nt - (P.nt - 1 + 1) = 0 by omega]
    refine St.monoE h ⟨h.1, rfl⟩ (fun x hx => ⟨hx, rfl⟩) (fun x hx => ⟨hx, rfl⟩) ?_
    intro d hd
    simp only [List.mem_singleton] at hd; subst hd
    exact ⟨by simp, by simp [upd]⟩
  · have hj : P.nt - (n + 1) < 100 := by omega
    refine (fusedCandidate_vp hn h101 hj sz nowrap lengths positive (fun σ e => by
      have upper := M_lt (hE σ e.1).1
      simp only [mv] at *
      omega)).mono (fun _ _ h => h)
      fun σ s ⟨hc, z⟩ => ?_
    obtain ⟨pre, go, hnt⟩ := hE σ hc.1.1
    have hgo := hc.1.2
    have hnt2 : (recoverPrimes.go P.n (tv P σ) (rv P σ) recoverTries).2 = P.nt := hnt
    have hgo2 : recoverPrimes.go P.n (tv P σ) (rv P σ) recoverTries =
        recoverPrimes.go P.n (tv P σ) (rv P σ) (recoverTries - (P.nt - (n + 1))) := hgo
    have cc := VG.Proof.Rsa.cand_cond P.n (tv P σ) (rv P σ) (j := P.nt - (n + 1)) (by rw [hnt2]; omega) hgo2
    have rootEq := fusedResult_eq pre go hn.2 (P.nt - (n + 1))
    rw [hnt2, ← rootEq] at cc
    have ev : isa.eval .ne s = some (decide (0 < n)) := by
      show some (!s.z) = some (decide (0 < n))
      rw [z, cc]
      congr 1
      simp only [decide_eq_decide]
      omega
    refine ⟨ev, fun h0 => ?_, fun hp => ⟨by omega, ?_⟩⟩
    · subst h0; exact hc
    · -- The candidate failed: `ok` is false, and the next one is tried.
      have hok : (fusedResult P σ (P.nt - (n + 1))).isSome = false := by
        have : (decide (P.nt - (n + 1) + 1 < 100) && !(fusedResult P σ (P.nt - (n + 1))).isSome) = true := by
          rw [← Bool.not_not (decide _ && _), cc]; simp only [decide_eq_true_eq]; omega
        simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at this
        exact this.2
      have hs : recoverStep P.n (tv P σ) (rv P σ) (P.nt - (n + 1) + 2) = none := by
        rw [rootEq] at hok
        exact Option.not_isSome_iff_eq_none.mp (by rw [hok]; decide)
      have hj100 : P.nt - (n + 1) < recoverTries := by unfold recoverTries; omega
      have g : recoverPrimes.go P.n (tv P σ) (rv P σ) (recoverTries - (P.nt - (n + 1))) =
          recoverPrimes.go P.n (tv P σ) (rv P σ) (recoverTries - (P.nt - (n + 1) + 1)) := by
        rw [VG.Proof.Rsa.go_eq _ _ _ hj100, hs]
      refine St.monoE hc ⟨hc.1.1, ?_⟩ ?_ (fun x hx => ⟨hx, rfl⟩) ?_
      · show recoverPrimes.go P.n (tv P σ) (rv P σ) recoverTries =
          recoverPrimes.go P.n (tv P σ) (rv P σ) (recoverTries - (P.nt - n))
        rw [hgo2, g, show P.nt - (n + 1) + 1 = P.nt - n by omega]
      · intro x hx
        refine ⟨List.mem_cons_of_mem _ hx, ?_⟩
        simp only [liveM, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [finishA, upd, mY, aNg, aO, mR2, aOne, aZ, aN]
      · intro d hd
        simp only [List.mem_singleton] at hd; subst hd
        exact ⟨by simp, by simp [fusedCandidateV, upd, sCand]; omega⟩

end
end VG.Proof.Rsa.Arm.Recover
