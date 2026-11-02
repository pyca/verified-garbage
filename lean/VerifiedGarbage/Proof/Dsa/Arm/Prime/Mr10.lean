module
public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Mr6
public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Mr8

import VerifiedGarbage.Proof.Dsa.Arm.Prime.Mr9
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Taint7
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Seqs
import VerifiedGarbage.Proof.Rsa.Arm.RvCand1
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Vals

/-! # A candidate on ARMv7: after the round (`tail_vp`)

Whether the witness passed is public (`rv_pass`: it is whether Miller–Rabin
did not end there with a composite, `passS`); if it did, the counts are
advanced, and the iteration goes on (`MRS`, `sStat = 4`) or ends with a
probable prime; if not, it ends with a composite (`QS`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.Rsa (b2n)
open VG.Proof.RsaKeyGen (goS shapeOf itersOf)
open VG.Proof.Dsa.Generation (DMrAt dmrS dwit dres)
open VG.Impl.RsaKeyGen.Arm.Key (isOne)

/-- After an iteration that goes on: `sStat = 4`. -/
abbrev MRS (P : CP) (E : State → Prop) (n : Nat) (σ s : State) : Prop :=
  1 ≤ n ∧ n ≤ Nt P + 1 ∧ DMrAt (cv P σ) (chP P) (taP P σ) (tmP P σ) P.D (rB P σ) (Nt P + 1 - n) (n - 1) ∧
    St P E (AB2 P) LB2 (fun σ => upd (VI P (Nt P + 1 - n) σ) sStat 4) (sStat :: LSI) σ s ∧ MS P σ s

/-- After an iteration, before its comparison. -/
abbrev GQ (P : CP) (E : State → Prop) (n : Nat) (σ s : State) : Prop :=
  (n = 0 ∧ QS P E σ s) ∨ (0 < n ∧ MRS P E n σ s)

theorem go_iff (a b c : Nat) :
    (decide (a + 1 < 17) || decide (b < c)) = decide (a + 1 ≤ Spec.RsaKeyGen.blindedChecks ∨ b < c) := by
  by_cases h1 : a + 1 < 17 <;> by_cases h2 : b < c <;> simp [h1, h2, Spec.RsaKeyGen.blindedChecks] <;> omega

section
variable {P : CP} {E : State → Prop}

/-- Whether witness `k` passes, from the public candidate and tape. -/
def passQ (P : CP) (k : Nat) : Bool := Proof.MillerRabin.Round.round P.cand (dwit P.cand P.D P.rnd (P.D * k)).1

theorem rv_pass {σ : State} (pre : In P σ) (k : Nat) :
    Proof.MillerRabin.Round.round (cv P σ) (wf P σ k).1 = passQ P k := by
  unfold passQ wf; rw [pre.cand, pre.rnd]

theorem round_eq (c b : Nat) : Proof.MillerRabin.Round.round c b =
    Spec.RsaKeyGen.mrIteration c (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2 b := rfl

/-- The values of the header words in an iteration. -/
theorem vF_vals (σ : State) (k : Nat) :
    upd (VF P k σ) sF (rv P σ k) sI = (dmrS (cv P σ) P.D (rB P σ) k).1 ∧
    upd (VF P k σ) sF (rv P σ k) sUni = (dmrS (cv P σ) P.D (rB P σ) k).2 ∧
    upd (VF P k σ) sF (rv P σ k) sU = b2n (wf P σ k).2 ∧
    upd (VF P k σ) sF (rv P σ k) sChk = chP P ∧
    upd (VF P k σ) sF (rv P σ k) sUsed = P.D * k + P.D ∧
    upd (VF P k σ) sF (rv P σ k) sF = rv P σ k := by
  simp (config := {decide := true}) only [upd, ↓reduceIte, VF, VW, VI]

/-- The iteration's end, after the round. -/
theorem tail_vp {n : Nat} (hE : ∀ σ, E σ → In P σ ∧ EM P σ) (hn : n ≤ Nt P) :
    VP (fun σ s => St P (EK P E (Nt P - n) n) (AF P (Nt P - n)) LF
        (fun σ => upd (VF P (Nt P - n) σ) sF (rv P σ (Nt P - n))) (sF :: LSF) σ s ∧ MS P σ s)
      (seqs [.block (isOne sF), .ite .eq (.block onPass) (.block (setS sStat 3))]) (GQ P E n) := by
  have hk1 : Nt P + 1 - n = Nt P - n + 1 := by omega
  simp only [seqs]
  refine VP.seq (St.pisOneM isOneF_taint (by simp) fun σ _ => by
    simp only [upd_self]; exact VG.Proof.Rsa.b2n_le _) ?_
  refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) ?_ ?_
  · obtain ⟨e₁, mr₁, av₁⟩ := h₁.1.1.1
    obtain ⟨e₂, mr₂, av₂⟩ := h₂.1.1.1
    rw [isa_eq, isa_eq, h₁.2, h₂.2]
    simp only [upd_self, rv]
    rw [rv_pass (hE σ₁ e₁).1, rv_pass (hE σ₂ e₂).1]
  · refine VP.ofImp (p := passQ P (Nt P - n) = true) (fun σ s h => ?_) fun hp => ?_
    · obtain ⟨e, mr, av⟩ := h.1.1.1.1
      have z := h.1.2
      rw [isa_eq, z] at h
      have h1 := h.2
      simp only [upd_self, rv, Option.some.injEq, decide_eq_true_eq] at h1
      rw [← rv_pass (hE σ e).1 (Nt P - n)]
      revert h1; unfold b2n; split <;> simp_all
    refine (St.ponPass (by simp) (by simp) (by simp) (by simp) fun σ ek => ?_).mono (fun σ s h => h.1.1)
      fun σ s ⟨⟨⟨e, mr, av⟩, h, hw⟩, m⟩ => ?_
    · have e := ek.1
      obtain ⟨vI, vUni, vU, vChk, -, -⟩ := vF_vals (P := P) σ (Nt P - n)
      rw [vI, vUni, vU, vChk, mrS_fst]
      have := mrS_snd_le (cv P σ) P.D (rB P σ) (Nt P - n)
      have hc : chP P ≤ 128 := by simp only [chP, Spec.Dsa.primeChecks]; split <;> decide
      have := VG.Proof.Rsa.b2n_le (wf P σ (Nt P - n)).2
      have av := ek.2.2
      have sz := (hE σ e).1.sizes
      have := (hE σ e).1.rlt
      have : Nt P - n + 1 ≤ P.rl / 24 := by
        rw [Nat.le_div_iff_mul_le (by decide)]
        exact Nat.le_trans (Nat.mul_le_mul_left _ (show 24 ≤ P.D by omega))
          (by rw [Nat.mul_comm, Nat.mul_succ]; omega)
      refine ⟨by omega, by omega, by omega, by omega⟩
    · obtain ⟨pre, hm⟩ := hE σ e
      obtain ⟨-, hwb, -⟩ := mr_facts pre hm
      have hpass : Spec.RsaKeyGen.mrIteration (cv P σ) (taP P σ) (tmP P σ) (dwit (cv P σ) P.D (rB P σ)
          (P.D * (Nt P - n))).1 = true := by
        have := rv_pass pre (Nt P - n)
        rw [hp, round_eq] at this
        exact this
      obtain ⟨vI, vUni, vU, vChk, vUsed, -⟩ := vF_vals (P := P) σ (Nt P - n)
      have hgo : ((decide ((dmrS (cv P σ) P.D (rB P σ) (Nt P - n)).1 + 1 < 17) ||
          decide ((dmrS (cv P σ) P.D (rB P σ) (Nt P - n)).2 + b2n (wf P σ (Nt P - n)).2 < chP P)) = true) ↔
          goS (chP P) (dmrS (cv P σ) P.D (rB P σ) (Nt P - n + 1)) := by
        rw [go_iff, decide_eq_true_eq]
        exact Iff.rfl
      have hAF : ∀ j ∈ LB2, j ∈ LF ∧ AF P (Nt P - n) σ j = AB2 P σ j := fun j hj =>
        ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hj),
          by simp only [AF, AW]; rw [upd_ne _ _ (by revert hj; revert j; decide),
          upd_ne _ _ (by revert hj; revert j; decide)]⟩
      have hD : 0 < P.D := by have := pre.sizes; omega
      by_cases hg : goS (chP P) (dmrS (cv P σ) P.D (rB P σ) (Nt P - n + 1))
      · obtain ⟨hn0, mr'⟩ := VG.Proof.Dsa.Generation.dmrAt_next mr hwb hD (by rw [rB_length]; exact av) hpass hg
        refine .inr ⟨hn0, by omega, by omega, by rw [hk1, show n - 1 = n - 1 from rfl]; exact
          (show Nt P - n + 1 = Nt P + 1 - n by omega) ▸ mr', ?_, m⟩
        rw [hk1]
        refine ⟨e, h.mono hAF fun d hd => ⟨by revert hd; revert d; decide, ?_⟩, hw⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl | rfl | rfl | rfl
        · simp (config := {decide := true}) only [upd, ↓reduceIte, VF, VW, VI]
          split
          · rfl
          · exact absurd (hgo.mpr hg) ‹_›
        · simp (config := {decide := true}) only [upd, ↓reduceIte, VF, VW, VI]
          rfl
        · simp (config := {decide := true}) only [upd, ↓reduceIte, VF, VW, VI]
          rfl
        · simp (config := {decide := true}) only [upd, ↓reduceIte, VF, VW, VI]
          simp only [Nat.mul_succ]
        · simp (config := {decide := true}) only [upd, ↓reduceIte, VF, VW, VI]
      · obtain ⟨hn0, hres⟩ := VG.Proof.Dsa.Generation.dmrAt_done mr hwb hD (by rw [rB_length]; exact av) hpass hg
        have hres' : resP P σ = some (true, (rB P σ).drop (P.D * (Nt P - n) + P.D)) := hres
        refine .inl ⟨hn0, e, h.mono hAF fun d hd => ⟨by revert hd; revert d; decide, ?_⟩, hw⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl
        · simp (config := {decide := true}) only [upd, ↓reduceIte, VF, VW, VI]
          split
          · exact absurd (hgo.mp ‹_›) hg
          · unfold statQ; rw [hres']
        · simp (config := {decide := true}) only [upd, ↓reduceIte, VF, VW]
          unfold usedQ; rw [hres']
          dsimp only
          rw [List.length_drop, rB_length]
          omega
  · refine VP.ofImp (p := passQ P (Nt P - n) = false) (fun σ s h => ?_) fun hp => ?_
    · obtain ⟨e, mr, av⟩ := h.1.1.1.1
      have z := h.1.2
      rw [isa_eq, z] at h
      have h1 := h.2
      simp only [upd_self, rv, Option.some.injEq, decide_eq_false_iff_not] at h1
      rw [← rv_pass (hE σ e).1 (Nt P - n)]
      revert h1; unfold b2n; split <;> simp_all
    refine (St.psetSM stat3_taint (by decide) (by decide) (by decide)).mono (fun σ s h => h.1.1)
      fun σ s ⟨⟨⟨e, mr, av⟩, h, hw⟩, m⟩ => ?_
    obtain ⟨pre, hm⟩ := hE σ e
    obtain ⟨-, hwb, -⟩ := mr_facts pre hm
    have hfail : Spec.RsaKeyGen.mrIteration (cv P σ) (taP P σ) (tmP P σ) (dwit (cv P σ) P.D (rB P σ)
        (P.D * (Nt P - n))).1 = false := by
      have := rv_pass pre (Nt P - n)
      rw [hp, round_eq] at this
      exact this
    obtain ⟨-, -, -, -, vUsed, -⟩ := vF_vals (P := P) σ (Nt P - n)
    obtain ⟨hn0, hres⟩ := VG.Proof.Dsa.Generation.dmrAt_fail mr hwb (by have := pre.sizes; omega)
      (by rw [rB_length]; exact av) hfail
    have hres' : resP P σ = some (false, (rB P σ).drop (P.D * (Nt P - n) + P.D)) := hres
    have hAF : ∀ j ∈ LB2, j ∈ LF ∧ AF P (Nt P - n) σ j = AB2 P σ j := fun j hj =>
      ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hj),
        by simp only [AF, AW]; rw [upd_ne _ _ (by revert hj; revert j; decide),
          upd_ne _ _ (by revert hj; revert j; decide)]⟩
    refine .inl ⟨hn0, e, h.mono hAF fun d hd => ⟨by revert hd; revert d; decide, ?_⟩, hw⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · simp (config := {decide := true}) only [upd, ↓reduceIte]
      unfold statQ; rw [hres']
    · simp (config := {decide := true}) only [upd, ↓reduceIte, VF, VW]
      unfold usedQ; rw [hres']
      dsimp only
      rw [List.length_drop, rB_length]
      omega

end

end VG.Proof.Dsa.Arm.Prime
