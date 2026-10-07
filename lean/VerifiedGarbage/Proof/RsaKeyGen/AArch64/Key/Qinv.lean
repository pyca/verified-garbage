import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Shared

/-!
# An RSA key from its primes on AArch64: `qInv`

`qinvPart`: the inverse of `q` modulo `M = p` (3 unless `p` is odd and at
least 3) into `aX₂`, and `kOk &= ` the mask of `gcd(q, M) = 1`
(`qinvPart_k`). The mask `selC` takes is that of the bad case: `p` below 3
or even.
-/

namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Key
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.RsaKeyGen.AArch64.Candidate (loadE kE kElen)

theorem qinvPart_eq : qinvPart = [zeroA aU, copyA aU aQa] ++ (constA 3 ++ (ltA aPa aC ++
    (([.block (([mov .x10 .x15] : List Instr) ++ (evenMaskOf aPa ++ ([.logic .orr .x .x15 .x15 .x10] : List Instr))),
      zeroA aM, copyA aM aPa] : List (Prog isa)) ++
    (selC aM ++ (invFrom aM ++ (([inverse aU aV aX₁ aX₂ aM aT] : List (Prog isa)) ++ gcdIsOne)))))) := by
  simp only [qinvPart, List.append_assoc]

/-- The modulus of `qInv`: `p` if it is odd and at least 3, else 3. -/
abbrev qMod (P : Nat) : Nat := if (decide (P % 2 = 1) && !decide (P < 3)) = true then P else 3

/-- The parts `qinvPart` changes. -/
abbrev csQ : List Rc := [.arr aU, .arr aC, .arr aM, .arr aV, .arr aX₁, .arr aX₂, .arr aT, .hdr kOk]

theorem qinv_mask_or (a b : Bool) : mask a ||| mask b = mask (a || b) := by cases a <;> cases b <;> decide

/-- `qMod`, from the mask of the bad case. -/
theorem qMod_bad (P : Nat) : (if (decide (P % 2 = 0) || decide (P < 3)) = true then 3 else P) = qMod P := by
  unfold qMod
  by_cases h1 : P % 2 = 0 <;> by_cases h2 : P < 3 <;>
    simp [h1, h2, show P % 2 = 1 ↔ ¬ P % 2 = 0 by omega]

/-- `qinvPart`, for `[aPa] = P` and `[aQa] = Q`. -/
theorem qinvPart_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {P Q : Nat} {ok : Bool}
    (hP : av I s.mem aPa = P) (hQ : av I s.mem aQa = Q) (hok : word s.mem I.B (8 * kOk) = mask ok) :
    WP isa (seqs qinvPart) s fun t => KS I s₀ t ∧ KF I.B I.W csQ s.mem t.mem ∧
      word t.mem I.B (8 * kOk) = mask (decide (Nat.gcd Q (qMod P) = 1) && ok) ∧
      ((qMod P : Nat) : Int) ∣ (av I t.mem aX₂ : Int) * Q - Nat.gcd Q (qMod P) ∧ av I t.mem aX₂ < qMod P := by
  have hZ := h.hZ
  rw [qinvPart_eq]
  -- `[aU] := q`.
  refine wp_seqs_append (by simp) (by simp [constA]) (WP.mono (zc_k h (o := aU) (a := aQa) (by decide) (by decide)
    (by decide)) fun s₁ ⟨h₁, f₁, v₁, t₁⟩ => ?_)
  rw [hQ] at v₁
  refine wp_seqs_append (by simp [constA]) (by simp [ltA, cmpA]) (WP.mono (constA_k h₁ (x := 3) (by decide))
    fun s₂ ⟨h₂, f₂, c₂, _⟩ => ?_)
  have c3 : av I s₂.mem aC = 3 :=
    av_of_full c₂ (Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by decide)
      (show 2 ≤ 64 * I.W by have := h.ws.w1; omega)))
  have vP₂ : av I s₂.mem aPa = P := by
    rw [f₂.av (by decide) (by decide) (by decide) hZ, f₁.av (by decide) (by decide) (by decide) hZ, hP]
  refine wp_seqs_append (by simp [ltA, cmpA]) (by simp) (WP.mono (ltA_k h₂ (a := aPa) (b := aC) (by decide)
    (by decide)) fun s₃ ⟨h₃, m₃, h15₃, _, _⟩ => ?_)
  rw [vP₂, c3] at h15₃
  generalize hpv : (decide (P % 2 = 0) || decide (P < 3)) = pv
  -- `x15 := ` the mask of `p` even or below 3; `[aM] := p`.
  refine wp_seqs_append (by simp) (by simp [selC]) ?_
  simp only [seqs]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (WP.keep [.x10]
    (Q := fun t => t.gpr .x10 = mask (decide (P < 3)) ∧ t.mem = s₃.mem) (by brun [h15₃]) (by decide) (by decide)
      (by decide +kernel)) fun s₄ ⟨⟨h10₄, m₄⟩, k₄⟩ => WP.block_append_iff.mpr ?_))
  have h₄ := h₃.regs m₄ k₄
  refine WP.mono (evenMaskOf_k h₄ (j := aPa) (by decide)) fun s₅ ⟨h₅, m₅, h15₅, _, _, k₅⟩ => ?_
  rw [m₄, m₃, vP₂] at h15₅
  have h10₅ : s₅.gpr .x10 = mask (decide (P < 3)) := by rw [k₅.gpr .x10 (by decide), h10₄]
  refine WP.mono (WP.keep [.x15] (Q := fun t => t.gpr .x15 = mask pv ∧ t.mem = s₅.mem) (by
    brun [h15₅, h10₅, qinv_mask_or]; rw [hpv]) (by decide) (by decide) (by decide +kernel))
    fun s₆ ⟨⟨h15₆, m₆⟩, k₆⟩ => ?_
  have h₆ := h₅.regs m₆ k₆
  have hm₆ : s₆.mem = s₂.mem := by rw [m₆, m₅, m₄, m₃]
  refine WP.seq (WP.mono (zeroA_k h₆ (j := aM) (by decide)) fun s₇ ⟨h₇, f₇, _, _, k₇⟩ =>
    WP.mono (copyA_k h₇ (o := aM) (a := aPa) (by decide) (by decide) (by decide)) fun s₈ ⟨h₈, f₈, v₈, _, k₈⟩ => ?_)
  have vP₆ : av I s₆.mem aPa = P := by rw [hm₆, vP₂]
  rw [f₇.av (by decide) (by decide) (by decide) hZ, vP₆] at v₈
  have vC₈ : av I s₈.mem aC = 3 := by
    rw [f₈.av (by decide) (by decide) (by decide) hZ, f₇.av (by decide) (by decide) (by decide) hZ, hm₆, c3]
  -- `[aM] := M`.
  refine wp_seqs_append (by simp [selC]) (by simp [invFrom]) (WP.mono (selC_k h₈ (j := aM) (by decide) (by decide)
    (c := pv) (by rw [k₈.gpr .x15 (by decide), k₇.gpr .x15 (by decide), h15₆])) fun s₉ ⟨h₉, f₉, v₉, _, _⟩ => ?_)
  rw [v₈, vC₈] at v₉
  have hM : (if pv = true then 3 else P) = qMod P := by rw [← hpv]; exact qMod_bad P
  rw [hM] at v₉
  have hMo : qMod P % 2 = 1 ∧ 1 < qMod P := by
    unfold qMod
    by_cases hc : (decide (P % 2 = 1) && !decide (P < 3)) = true
    · rw [ite_eq_left hc]
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not] at hc
      omega
    · rw [ite_eq_right hc]; decide
  -- The inverse.
  refine wp_seqs_append (by simp [invFrom]) (by simp) (WP.mono (invFrom_k h₉ (j := aM) (by decide) (by decide))
    fun s₁₀ ⟨h₁₀, f₁₀, vV₁₀, vX₁₁₀, vX₂₁₀⟩ => ?_)
  have hok10 : [Rc.arr aV, Rc.arr aX₁, Rc.arr aX₂].all Rc.ok = true := by decide
  have vM₁₀ : av I s₁₀.mem aM = qMod P := by rw [f₁₀.av hok10 (by decide) (by decide) hZ, v₉]
  have pU : av I s₁₀.mem aU = Q ∧ atop I s₁₀.mem aU = 0 := by
    have hK : ∀ {m m' : Mem} {cs : List Rc}, KF I.B I.W cs m m' → cs.all Rc.ok = true → .arr aU ∉ cs →
        av I m' aU = av I m aU ∧ atop I m' aU = atop I m aU := fun f ok hn =>
      ⟨f.av ok (by decide) hn hZ, f.at ok (by decide) hn hZ⟩
    obtain ⟨a1, b1⟩ := hK f₁₀ hok10 (by decide)
    obtain ⟨a2, b2⟩ := hK f₉ (by decide) (by decide)
    obtain ⟨a3, b3⟩ := hK f₈ (by decide) (by decide)
    obtain ⟨a4, b4⟩ := hK f₇ (by decide) (by decide)
    obtain ⟨a5, b5⟩ := hK f₂ (by decide) (by decide)
    rw [hm₆] at a4 b4
    exact ⟨by rw [a1, a2, a3, a4, a5, v₁], by rw [b1, b2, b3, b4, b5, t₁]⟩
  refine wp_seqs_append (by simp) (by simp [gcdIsOne, constA]) ?_
  simp only [seqs]
  refine WP.mono (inverse_k h₁₀ (iU := aU) (iV := aV) (iX₁ := aX₁) (iX₂ := aX₂) (iM := aM) (iT := aT)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) pU.2 (by rw [vV₁₀, v₉, vM₁₀]) vX₁₁₀ vX₂₁₀) fun s₁₁ ⟨h₁₁, f₁₁, hinv⟩ => ?_
  rw [vM₁₀, pU.1] at hinv
  obtain ⟨hg₁₁, hdv₁₁, hx₁₁⟩ := hinv hMo.1 hMo.2
  have hokI : [Rc.arr aU, Rc.arr aV, Rc.arr aX₁, Rc.arr aX₂, Rc.arr aT].all Rc.ok = true := by decide
  have ok₁₁ : word s₁₁.mem I.B (8 * kOk) = mask ok := by
    rw [f₁₁.word hokI (by decide) (by decide), f₁₀.word hok10 (by decide) (by decide),
      f₉.word (by decide) (by decide) (by decide), f₈.word (by decide) (by decide) (by decide),
      f₇.word (by decide) (by decide) (by decide), hm₆, f₂.word (by decide) (by decide) (by decide),
      f₁.word (by decide) (by decide) (by decide), hok]
  refine WP.mono (gcdIsOne_k h₁₁ ok₁₁) fun t ⟨ht, f₁₂, ok₁₂⟩ => ?_
  rw [hg₁₁] at ok₁₂ hdv₁₁
  have vX : av I t.mem aX₂ = av I s₁₁.mem aX₂ := f₁₂.av (by decide) (by decide) (by decide) hZ
  have f₂₆ : KF I.B I.W [.arr aC] s₁.mem s₆.mem := by rw [hm₆]; exact f₂
  refine ⟨ht, ?_, ok₁₂, by rw [vX]; exact hdv₁₁, by rw [vX]; exact hx₁₁⟩
  exact ((((((((f₁.trans f₂₆).trans f₇).trans f₈).trans f₉).trans f₁₀).trans f₁₁).trans f₁₂)).mono (by simp)

end VG.Proof.RsaKeyGen.AArch64.Key
