import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Shared

/-!
# An RSA key from its primes on AArch64: `dP` and `dQ`

`crtPart`: `dP = d mod (p − 1)` into `aX₁` and `dQ = d mod (q − 1)` into
`aV`, each divisor 1 for 0 (`divisorOf_k`; `crtPart_k`).
-/

namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Key
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.RsaKeyGen.AArch64.Candidate (loadE kE kElen)

/-- The parts `crtPart` changes. -/
abbrev csC : List Rc := [.arr aM, .arr aC, .arr aU, .arr aV, .arr aT, .arr aX₁]

/-- `crtPart`: `[aX₁] := d mod dv(P − 1)`, `[aV] := d mod dv(Q − 1)`, for `[aDd] = d`,
`[aPm] = P − 1` and `[aQm] = Q − 1`. -/
theorem crtPart_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {d a b : Nat} (hd : av I s.mem aDd = d)
    (ha : av I s.mem aPm = a) (hb : av I s.mem aQm = b) :
    WP isa (seqs crtPart) s fun t => KS I s₀ t ∧ KF I.B I.W csC s.mem t.mem ∧
      av I t.mem aX₁ = d % dv a ∧ av I t.mem aV = d % dv b := by
  have hZ := h.hZ
  have hdv : ∀ x, 0 < dv x := fun x => by unfold dv; split <;> omega
  unfold crtPart
  simp only [List.append_assoc]
  -- `dP`.
  refine wp_seqs_append (by simp [divisorOf]) (by simp) (WP.mono (divisorOf_k h (j := aPm) (by decide) (by decide)
    (by decide)) fun s₁ ⟨h₁, f₁, v₁⟩ => ?_)
  rw [ha] at v₁
  have hok1 : [Rc.arr aM, Rc.arr aC].all Rc.ok = true := by decide
  have vD₁ : av I s₁.mem aDd = d := by rw [f₁.av hok1 (by decide) (by decide) hZ, hd]
  refine wp_seqs_append (by simp) (by simp [divisorOf]) ?_
  simp only [seqs]
  refine WP.seq (WP.mono (zeroA_k h₁ (j := aU) (by decide)) fun s₂ ⟨h₂, f₂, _, _⟩ =>
    WP.seq (WP.mono (copyA_k h₂ (o := aU) (a := aDd) (by decide) (by decide) (by decide)) fun s₃ ⟨h₃, f₃, v₃, _, _⟩ =>
      WP.seq (WP.mono (divmod_k h₃ (iQ := aU) (iR := aV) (iD := aM) (iT := aT) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) fun s₄ ⟨h₄, f₄, d₄⟩ =>
        WP.seq (WP.mono (zeroA_k h₄ (j := aX₁) (by decide)) fun s₅ ⟨h₅, f₅, _, _⟩ =>
          WP.mono (copyA_k h₅ (o := aX₁) (a := aV) (by decide) (by decide) (by decide))
            fun s₆ ⟨h₆, f₆, v₆, _, _⟩ => ?_))))
  have vM₃ : av I s₃.mem aM = dv a := by
    rw [f₃.av (by decide) (by decide) (by decide) hZ, f₂.av (by decide) (by decide) (by decide) hZ, v₁]
  have vU₃ : av I s₃.mem aU = d := by rw [v₃, f₂.av (by decide) (by decide) (by decide) hZ, vD₁]
  rw [vM₃, vU₃] at d₄
  have hR := (d₄ (hdv a)).1
  have hlt : d % dv a < dv a := Nat.mod_lt _ (hdv a)
  have vM₁W : dv a < 2 ^ (64 * I.W) := by rw [← v₁]; exact wv_lt _ _ _ _
  have vX₆ : av I s₆.mem aX₁ = d % dv a := by
    rw [v₆, f₅.av (by decide) (by decide) (by decide) hZ, ← hR]
    exact wv_low_of_lt (by omega) (by rw [hR]; omega)
  have hok4 : [Rc.arr aU, Rc.arr aV, Rc.arr aT].all Rc.ok = true := by decide
  have pres6 : ∀ j, j < 16 → j ≠ aU → j ≠ aV → j ≠ aT → j ≠ aX₁ → av I s₆.mem j = av I s₁.mem j :=
    fun j hj h1 h2 h3 h4 => by
      rw [f₆.av (by decide) hj (by simp [h4]) hZ, f₅.av (by decide) hj (by simp [h4]) hZ,
        f₄.av hok4 hj (by simp [h1, h2, h3]) hZ, f₃.av (by decide) hj (by simp [h1]) hZ,
        f₂.av (by decide) hj (by simp [h1]) hZ]
  have vQm₆ : av I s₆.mem aQm = b := by
    rw [pres6 aQm (by decide) (by decide) (by decide) (by decide) (by decide), f₁.av hok1 (by decide) (by decide) hZ,
      hb]
  have vD₆ : av I s₆.mem aDd = d := by
    rw [pres6 aDd (by decide) (by decide) (by decide) (by decide) (by decide), vD₁]
  -- `dQ`.
  refine wp_seqs_append (by simp [divisorOf]) (by simp) (WP.mono (divisorOf_k h₆ (j := aQm) (by decide) (by decide)
    (by decide)) fun s₇ ⟨h₇, f₇, v₇⟩ => ?_)
  rw [vQm₆] at v₇
  have vD₇ : av I s₇.mem aDd = d := by rw [f₇.av hok1 (by decide) (by decide) hZ, vD₆]
  have vX₇ : av I s₇.mem aX₁ = d % dv a := by rw [f₇.av hok1 (by decide) (by decide) hZ, vX₆]
  simp only [seqs]
  refine WP.seq (WP.mono (zeroA_k h₇ (j := aU) (by decide)) fun s₈ ⟨h₈, f₈, _, _⟩ =>
    WP.seq (WP.mono (copyA_k h₈ (o := aU) (a := aDd) (by decide) (by decide) (by decide)) fun s₉ ⟨h₉, f₉, v₉, _, _⟩ =>
      WP.mono (divmod_k h₉ (iQ := aU) (iR := aV) (iD := aM) (iT := aT) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
        fun t ⟨ht, f₁₀, d₁₀⟩ => ?_))
  have vM₉ : av I s₉.mem aM = dv b := by
    rw [f₉.av (by decide) (by decide) (by decide) hZ, f₈.av (by decide) (by decide) (by decide) hZ, v₇]
  have vU₉ : av I s₉.mem aU = d := by rw [v₉, f₈.av (by decide) (by decide) (by decide) hZ, vD₇]
  rw [vM₉, vU₉] at d₁₀
  have hR' := (d₁₀ (hdv b)).1
  have vMb : dv b < 2 ^ (64 * I.W) := by rw [← v₇]; exact wv_lt _ _ _ _
  refine ⟨ht, ?_, ?_, ?_⟩
  · exact (((((((((f₁.trans f₂).trans f₃).trans f₄).trans f₅).trans f₆).trans f₇).trans f₈).trans f₉).trans
      f₁₀).mono (by simp)
  · rw [f₁₀.av hok4 (by decide) (by decide) hZ, f₉.av (by decide) (by decide) (by decide) hZ,
      f₈.av (by decide) (by decide) (by decide) hZ, vX₇]
  · rw [← hR']
    exact wv_low_of_lt (by omega) (by rw [hR']; exact Nat.lt_trans (Nat.mod_lt _ (hdv b)) vMb)

end VG.Proof.RsaKeyGen.AArch64.Key
