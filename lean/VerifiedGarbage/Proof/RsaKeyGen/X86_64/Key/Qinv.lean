import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.Small

/-!
# An RSA key from its primes on x86-64: `qInv`

`qinvPart`: the inverse of `q` modulo `M = p` (3 unless `p` is odd and at
least 3) into `aX₂`, and `kOk &= ` the mask of `gcd(q, M) = 1`
(`qinvPart_k`).
-/

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.RsaKeyGen.X86_64.Key
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

theorem qinvPart_eq : qinvPart = [zeroA aU, copyA aU aQa] ++ (constA 3 ++ (ltA aPa aC ++
    ([.block ([.mov .rcx (.reg .rbp), .alu .xor .rcx (.imm (BitVec.ofInt 32 (-1)))] ++ oddMask aPa ++
        [.alu .and .rax (.reg .rcx), .mov .rbp (.reg .rax)]), zeroA aM, copyA aM aPa] ++
    (selC aM ++ (invFrom aM ++ ([inverse aU aV aX₁ aX₂ aM aT] ++ gcdIsOne)))))) := by
  simp only [qinvPart, gcdIsOne, List.append_assoc]

/-- The modulus of `qInv`: `p` if it is odd and at least 3, else 3. -/
abbrev qMod (P : Nat) : Nat := if (decide (P % 2 = 1) && !decide (P < 3)) = true then P else 3

/-- The parts `qinvPart` changes. -/
abbrev csQ : List Rc :=
  [.arr aU, .arr aC, .arr aM, .arr aV, .arr aX₁, .arr aX₂, .arr aT, .hdr sMo, .hdr kOk]

/-- `qinvPart`, for `[aPa] = P` and `[aQa] = Q`. -/
theorem qinvPart_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {P Q : Nat} {ok : Bool}
    (hP : av I s.mem aPa = P) (hQ : av I s.mem aQa = Q) (hok : word s.mem I.B (8 * kOk) = mask ok) :
    WP isa (seqs qinvPart) s fun t => KS I m₀ t ∧ KF I.B I.W csQ s.mem t.mem ∧
      word t.mem I.B (8 * kOk) = mask (decide (Nat.gcd Q (qMod P) = 1) && ok) ∧
      ((qMod P : Nat) : Int) ∣ (av I t.mem aX₂ : Int) * Q - Nat.gcd Q (qMod P) ∧ av I t.mem aX₂ < qMod P := by
  have hZ := h.hZ
  rw [qinvPart_eq]
  -- `[aU] := q`.
  refine wp_seqs_append (by simp) (by simp [constA]) (WP.mono (zc_k h (o := aU) (a := aQa) (by decide) (by decide)
    (by decide)) fun s₁ ⟨h₁, f₁, v₁, t₁⟩ => ?_)
  rw [hQ] at v₁
  refine wp_seqs_append (by simp [constA]) (by simp [ltA]) (WP.mono (constA_k h₁ 3) fun s₂ ⟨h₂, f₂, c₂, _⟩ => ?_)
  have c3 : av I s₂.mem aC = 3 := av_of_full c₂ (two_le_pow h (by decide))
  have vP₂ : av I s₂.mem aPa = P := by
    rw [f₂.av (by decide) (by decide) (by decide) hZ, f₁.av (by decide) (by decide) (by decide) hZ, hP]
  refine wp_seqs_append (by simp [ltA]) (by simp) (WP.mono (ltA_k h₂ (a := aPa) (b := aC) (by decide) (by decide))
    fun s₃ ⟨h₃, m₃, hbp₃, _, _, _, k₃⟩ => ?_)
  rw [vP₂, c3] at hbp₃
  generalize hpv : (decide (P % 2 = 1) && !decide (P < 3)) = pv
  -- `rbp := ` the mask of `p` odd and at least 3; `[aM] := p`.
  refine wp_seqs_append (by simp) (by simp [selC]) ?_
  simp only [seqs]
  refine WP.seq (WP.block_append_iff.mpr (WP.block_append_iff.mpr (WP.mono (WP.keep [.rcx]
    (Q := fun t => t.gpr .rcx = mask (!decide (P < 3)) ∧ t.mem = s₃.mem) (by xrun [hbp₃, sxM1, maskNot]) rfl)
    fun s₄ ⟨⟨hcx₄, m₄⟩, k₄⟩ => ?_)))
  have h₄ := h₃.step (cs := []) (by rw [m₄]; exact KF.refl _ _ _) rfl k₄ (by decide)
  refine WP.mono (oddMask_k h₄ (j := aPa) (by decide)) fun s₅ ⟨m₅, hax, _, _, k₅⟩ => ?_
  rw [m₄, m₃, vP₂] at hax
  have hcx₅ : s₅.gpr .rcx = mask (!decide (P < 3)) := by rw [k₅.gpr (by decide), hcx₄]
  refine WP.mono (WP.keep [.rax, .rbp] (Q := fun t => t.gpr .rbp = mask pv ∧ t.mem = s₅.mem) (by
    xrun [hax, hcx₅, mask_and']; rw [hpv]) rfl) fun s₆ ⟨⟨hbp₆, m₆⟩, k₆⟩ => ?_
  have h₆ := h₄.step (cs := []) (by rw [m₆, m₅]; exact KF.refl _ _ _) rfl (k₅.trans k₆) (by decide)
  have hm₆ : s₆.mem = s₂.mem := by rw [m₆, m₅, m₄, m₃]
  refine WP.seq (WP.mono (zeroA_k h₆ (j := aM) (by decide)) fun s₇ ⟨h₇, f₇, _, k₇⟩ =>
    WP.mono (copyA_k h₇ (o := aM) (a := aPa) (by decide) (by decide) (by decide)) fun s₈ ⟨h₈, f₈, v₈, _, k₈⟩ => ?_)
  have vP₆ : av I s₆.mem aPa = P := by rw [hm₆, vP₂]
  rw [f₇.av (by decide) (by decide) (by decide) hZ, vP₆] at v₈
  have vC₈ : av I s₈.mem aC = 3 := by
    rw [f₈.av (by decide) (by decide) (by decide) hZ, f₇.av (by decide) (by decide) (by decide) hZ, hm₆, c3]
  -- `[aM] := M`.
  refine wp_seqs_append (by simp [selC]) (by simp [invFrom]) (WP.mono (selC_k h₈ (j := aM) (by decide) (by decide)
    (c := pv) (by rw [k₈.gpr (by decide), k₇.gpr (by decide), hbp₆])) fun s₉ ⟨h₉, f₉, v₉, _, _⟩ => ?_)
  rw [v₈, vC₈] at v₉
  have hM : (if pv = true then P else 3) = qMod P := by rw [← hpv]
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
  have hokI : [Rc.arr aU, Rc.arr aV, Rc.arr aX₁, Rc.arr aX₂, Rc.arr aT, Rc.hdr sMo].all Rc.ok = true := by decide
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

end VG.Proof.RsaKeyGen.X86_64.Key
