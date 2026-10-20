module
public import VerifiedGarbage.Proof.Rsa.Arm.RvFin5

import VerifiedGarbage.Proof.Rsa.Arm.RvFail
import VerifiedGarbage.Proof.Rsa.Arm.RvRest
import VerifiedGarbage.Proof.Rsa.Arm.RvNumbers

/-! # `vg_rsa_recover_primes` on ARMv7: the body (`body_vp`)

From the start of the body (`Bs`, Z if `n` is valid): `p`, `q` and the
result as `primesKey` gives them (`Res`), and constant time with the number
of candidates tried public.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa (b2n)
open VG.Spec.Rsa (recoverPrimes)

/-- The end of the body. -/
def Res (P : RP) (σ s : State) : Prop :=
  Bo P σ s ∧ Spec.Rsa.writtenAll s.mem [(State.addr P.pP, P.K), (State.addr P.qP, P.K)] (s.gpr .r0)
    ((Spec.Rsa.primesKey P.nB P.eB (dB P σ)).1.map fun v => [v.1, v.2])

section
variable {P : RP}

theorem numbers_vp {E : State → Prop} :
    VP (fun σ s => E σ ∧ Bs P σ s) numbers (fun σ s => E σ ∧
      KS P σ (Aload P σ) [aN] (AWs P σ) [wM, wZ] (Vs P σ) [sBit] s ∧ Ws s P.B P.Z P.W 22 ∧ s.z = goOn P σ) := by
  simp only [numbers, seqs]
  exact loads_vp.seq ((prod_vp.mono (fun σ s ⟨e, h⟩ => ⟨e, h.ks⟩) fun _ _ h => h).seq skip_vp)

/-- Whether candidates are tried: whether any is. -/
theorem goOn_eq (hv : Spec.Rsa.modulusValid P.n P.K = true) {σ : State} (pre : In P σ) :
    goOn P σ = decide (0 < P.nt) := by
  by_cases hg : goOn P σ = true
  · obtain ⟨-, -, -, hnt⟩ := rest_facts hv pre hg
    rw [hg, eq_comm, decide_eq_true_eq, ← hnt]
    exact VG.Proof.Rsa.go_pos _ _ _ _ (Nat.le_refl _)
  · have h1 : dv P σ * P.e < 2 ∨ (dv P σ * P.e - 1) % 2 = 1 := by
      simp only [goOn, decide_eq_true_eq, mv, Mv] at hg; omega
    have := pre.tries
    rw [primesKey_snd hv pre, VG.Proof.Rsa.recoverPrimes_none h1] at this
    rw [Bool.eq_false_iff.mpr hg, ← this]; rfl

theorem primesKey_none (hv : Spec.Rsa.modulusValid P.n P.K = true) {σ : State} (pre : In P σ)
    (hg : goOn P σ = false) : (Spec.Rsa.primesKey P.nB P.eB (dB P σ)).1 = none := by
  have h1 : dv P σ * P.e < 2 ∨ (dv P σ * P.e - 1) % 2 = 1 := by
    simp only [goOn, decide_eq_false_iff_not] at hg; simp only [mv, Mv] at hg; omega
  have hl : P.nB.length = P.K := by rw [← pre.nB]; simp [Spec.Rsa.bytesAt]
  simp only [Spec.Rsa.primesKey, hl, show Spec.Rsa.os2ip P.nB = P.n from rfl, hv, ite_true]
  show (match recoverPrimes P.n P.e (dv P σ) with
    | (some (p, q), tries) => (some (Spec.Rsa.i2osp p P.K, Spec.Rsa.i2osp q P.K), tries)
    | (none, tries) => (none, tries)).1 = none
  rw [VG.Proof.Rsa.recoverPrimes_none h1]

theorem fail_res {E : State → Prop} (hE : ∀ σ, E σ → (Spec.Rsa.primesKey P.nB P.eB (dB P σ)).1 = none) {σ s : State}
    (h : E σ ∧ Bo P σ s ∧ Spec.Rsa.bytesAt s.mem (State.addr P.pP) P.K = List.replicate P.K 0 ∧
      Spec.Rsa.bytesAt s.mem (State.addr P.qP) P.K = List.replicate P.K 0 ∧ s.gpr .r0 = 0) : Res P σ s := by
  obtain ⟨e, h, bp, bq, r0⟩ := h
  refine ⟨h, ?_⟩
  rw [hE σ e]
  refine ⟨r0, fun o ho => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl
  · exact bp
  · exact bq

/-- Once `n` is known valid. -/
theorem valid_vp (hv : Spec.Rsa.modulusValid P.n P.K = true) :
    VP (fun σ s => True ∧ Bs P σ s) valid (Res P) := by
  refine (numbers_vp (E := fun _ => True)).seq (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) ?_ ?_)
  · show some s₁.z = some s₂.z
    rw [h₁.2.2.2, h₂.2.2.2, goOn_eq hv h₁.2.1.bs.pre, goOn_eq hv h₂.2.1.bs.pre]
  · refine (rest_vp hv).mono (fun σ s ⟨⟨_, h, hw, z⟩, ev⟩ => ⟨⟨h.bs.pre, ?_⟩, h, hw⟩) fun σ s ⟨⟨⟨pre, hg⟩, hgo⟩, h, bp, bq, r0⟩ => ?_
    · have : some s.z = some true := ev
      rw [← z]; simpa using this
    · refine ⟨h, ?_⟩
      have hnt1 : 1 ≤ P.nt := by
        have := goOn_eq hv pre; rw [hg] at this
        have : 0 < P.nt := by simpa [eq_comm] using this
        omega
      rw [result_eq hv (valid_facts hv (by have := pre.k1; omega)).2.1 (n_lt pre) pre hg hgo hnt1]
      by_cases ho : okF P σ = true
      · simp only [ho, ite_true, Option.map_some]
        refine ⟨by rw [r0, ho]; rfl, ?_⟩
        simp only [List.map_cons, List.map_nil, bp, bq, outP, outQ, ho, ite_true]
      · have ho' : okF P σ = false := by simpa using ho
        simp only [ho', Bool.false_eq_true, ite_false, Option.map_none]
        refine ⟨by rw [r0, ho']; rfl, fun o hoo => ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hoo
        rcases hoo with rfl | rfl
        · rw [bp]; simp [outP, ho']
        · rw [bq]; simp [outQ, ho']
  · refine (fail_vp (E := fun σ => In P σ ∧ goOn P σ = false)).mono
      (fun σ s ⟨⟨_, h, _, z⟩, ev⟩ => ⟨⟨h.bs.pre, ?_⟩, h.bs.bo⟩)
      fun σ s h => fail_res (E := fun σ => In P σ ∧ goOn P σ = false) (fun σ e => ?_) h
    · have : some s.z = some false := ev
      rw [← z]; simpa using this
    · exact primesKey_none hv e.1 e.2

theorem primesKey_invalid (hv : Spec.Rsa.modulusValid P.n P.K = false) {σ : State} (pre : In P σ) :
    (Spec.Rsa.primesKey P.nB P.eB (dB P σ)).1 = none := by
  have hl : P.nB.length = P.K := by rw [← pre.nB]; simp [Spec.Rsa.bytesAt]
  simp only [Spec.Rsa.primesKey, hl, show Spec.Rsa.os2ip P.nB = P.n from rfl, hv, Bool.false_eq_true, ite_false]

/-- The body after the entry: Z iff `n` is valid. -/
theorem body_vp : VP (fun σ s => Bs P σ s ∧ s.z = Spec.Rsa.modulusValid P.n P.K) (.ite .eq valid fail) (Res P) := by
  refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) ?_ ?_
  · show some s₁.z = some s₂.z
    rw [h₁.2, h₂.2]
  · refine VP.of_imp (p := Spec.Rsa.modulusValid P.n P.K = true) (fun σ s ⟨⟨_, z⟩, ev⟩ => ?_)
      fun hv => (valid_vp hv).mono (fun σ s ⟨⟨h, _⟩, _⟩ => ⟨trivial, h⟩) fun _ _ h => h
    have : some s.z = some true := ev
    rw [← z]; simpa using this
  · refine (fail_vp (E := fun σ => In P σ ∧ Spec.Rsa.modulusValid P.n P.K = false)).mono
      (fun σ s ⟨⟨h, z⟩, ev⟩ => ⟨⟨h.pre, ?_⟩, h.bo⟩)
      fun σ s h => fail_res (E := fun σ => In P σ ∧ Spec.Rsa.modulusValid P.n P.K = false)
        (fun σ e => primesKey_invalid e.2 e.1) h
    have : some s.z = some false := ev
    rw [← z]; simpa using this

end

end VG.Proof.Rsa.Arm.Recover
