import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.DOdd
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.DEven

/-!
# An RSA key from its primes on AArch64: `d = e⁻¹ mod L`

`dPart`, by `e` (`cbz`/`cbnz` on `x3`): none for 0 (`dZero`), 1 for 1 but
`L = 1` (`dOne_k`), `dOdd` for an odd `e` and `dEven` for an even one
(`dPart_k`).
-/

namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Key
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.RsaKeyGen.AArch64.Candidate (loadE kE kElen)

/-- `e = 1`: `d = 1`, `kOk` the mask of `L ≠ 1`. -/
theorem dOne_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {L : Nat} (hL : av I s.mem aL = L) :
    WP isa (seqs dOne) s fun t => KS I s₀ t ∧ KF I.B I.W csD s.mem t.mem ∧ DRes I 1 L t.mem := by
  have hZ := h.hZ
  unfold dOne
  simp only [List.append_assoc]
  refine wp_seqs_append (by simp [constA]) (by simp [neMask, eqA]) (WP.mono (constA_k h (x := 1) (by decide))
    fun s₁ ⟨h₁, f₁, c₁, _⟩ => ?_)
  have c1 : av I s₁.mem aC = 1 := av_of_full c₁ (lt_pow_W h (by decide))
  have vL : av I s₁.mem aL = L := by rw [f₁.av (by decide) (by decide) (by decide) hZ, hL]
  refine wp_seqs_append (by simp [neMask, eqA]) (by simp) (WP.mono (neMask_k h₁ (a := aL) (b := aC) (by decide)
    (by decide)) fun s₂ ⟨h₂, m₂, h15, _, _⟩ => ?_)
  rw [vL, c1] at h15
  simp only [seqs]
  have hst := h₂.ws.scr.st (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega)
  refine WP.seq (WP.mono (WP.keep [] (Q := fun t => t.mem = s₂.mem.writeW (off I.B (8 * kOk))
    (mask (!decide (L = 1)))) (by brun [h₂.ws.x0, hdr_enc (show kOk < 32 by decide), hst, h15]) rfl rfl rfl)
    fun s₃ ⟨m₃, k₃⟩ => ?_)
  obtain ⟨h₃, f₃, ok₃⟩ := h₂.hdrW (i := kOk) (by unfold kOk sFn; omega) m₃ k₃
  refine WP.seq (WP.mono (zeroA_k h₃ (j := aDd) (by decide)) fun s₄ ⟨h₄, f₄, z₄, _, _⟩ =>
    WP.mono (setOne_k h₄ (j := aDd) (by decide) z₄) fun t ⟨ht, f₅, o₅, _⟩ => ?_)
  refine ⟨ht, (((f₁.trans (by rw [← m₂]; exact f₃)).trans f₄).trans f₅).mono (by simp),
    ⟨!decide (L = 1), ?_, ?_, ?_⟩⟩
  · rw [f₅.word (by decide) (by decide) (by decide), f₄.word (by decide) (by decide) (by decide), ok₃]
  · rw [VG.Proof.RsaKeyGen.inverse_one]
    by_cases h1 : L = 1 <;> simp [h1]
  · intro d hd
    rw [VG.Proof.RsaKeyGen.inverse_one] at hd
    by_cases h1 : L = 1
    · simp [h1] at hd
    · simp only [h1, ite_false, Option.some.injEq] at hd
      subst hd
      exact av_of_full o₅ (lt_pow_W h (by decide))

/-- A word's test against zero. -/
theorem ofNat_beq_zero {e : Nat} (he : e < 2 ^ 64) : (BitVec.ofNat 64 e == 0) = decide (e = 0) := by
  by_cases h : e = 0
  · subst h; rfl
  · have : BitVec.ofNat 64 e ≠ 0 := fun h' => h (by
      have := congrArg BitVec.toNat h'
      rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt he] at this)
    rw [beq_eq_false_iff_ne.mpr this, decide_eq_false h]

/-- `dPart`, for `e < 2⁶⁴`. -/
theorem dPart_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {e L : Nat} (he64 : e < 2 ^ 64)
    (hev : word s.mem I.B (8 * kEv) = BitVec.ofNat 64 e) (hL : av I s.mem aL = L) (hLW : L < 2 ^ (64 * I.W)) :
    WP isa dPart s fun t => KS I s₀ t ∧ KF I.B I.W csD s.mem t.mem ∧ DRes I e L t.mem := by
  have hld := h.ws.scr.ld (d := 8 * kEv) (by have := h.ws.h256; unfold kEv sFn; omega)
  unfold dPart
  refine WP.seq (WP.mono (WP.keep [.x3] (Q := fun t => t.gpr .x3 = BitVec.ofNat 64 e ∧ t.mem = s.mem) (by
    brun [h.ws.x0, hdr_enc (show kEv < 32 by decide), hld, hev]) (by decide) (by decide) (by decide +kernel))
    fun s₁ ⟨⟨h3₁, m₁⟩, k₁⟩ => ?_)
  have h₁ := h.regs m₁ k₁
  have hev₁ : word s₁.mem I.B (8 * kEv) = BitVec.ofNat 64 e := by rw [m₁, hev]
  have hL₁ : av I s₁.mem aL = L := by rw [show av I s₁.mem aL = av I s.mem aL by rw [m₁], hL]
  have post : ∀ {u : State}, u.mem = s.mem → ∀ t, KS I s₀ t ∧ KF I.B I.W csD u.mem t.mem ∧ DRes I e L t.mem →
      KS I s₀ t ∧ KF I.B I.W csD s.mem t.mem ∧ DRes I e L t.mem := fun hu t ⟨a, b, c⟩ =>
    ⟨a, by rw [← hu]; exact b, c⟩
  refine WP.ite (decide (e = 0)) (by rw [VG.Proof.MlKem.AArch64.eval_zero, h3₁, ofNat_beq_zero he64])
    (fun he0 => ?_) (fun he0 => ?_)
  · -- `e = 0`: no inverse.
    simp only [decide_eq_true_eq] at he0
    have hst := h₁.ws.scr.st (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega)
    refine WP.mono (WP.keep [.x3] (Q := fun t => t.mem = s₁.mem.writeW (off I.B (8 * kOk)) (mask false)) (by
      unfold dZero
      brun [h₁.ws.x0, hdr_enc (show kOk < 32 by decide), hst]
      rfl) (by decide) (by decide) (by decide +kernel)) fun t ⟨m, k⟩ => post m₁ t ?_
    obtain ⟨ht, ft, okt⟩ := h₁.hdrW (i := kOk) (by unfold kOk sFn; omega) m k
    refine ⟨ht, ft.mono (by simp), false, okt, ?_, fun d hd => ?_⟩
    · rw [he0, VG.Proof.RsaKeyGen.inverse_zero]; simp
    · rw [he0, VG.Proof.RsaKeyGen.inverse_zero] at hd; cases hd
  simp only [decide_eq_false_iff_not] at he0
  refine WP.seq (WP.mono (WP.keep [.x3] (Q := fun t => t.gpr .x3 = BitVec.ofNat 64 (e - 1) ∧ t.mem = s₁.mem) (by
    brun [h3₁]
    exact VG.Offset.ofNat_sub_ofNat (by omega)) (by decide) (by decide) (by decide +kernel)) fun s₂ ⟨⟨h3₂, m₂⟩, k₂⟩ => ?_)
  have h₂ := h₁.regs m₂ k₂
  have hm₂ : s₂.mem = s.mem := m₂.trans m₁
  refine WP.ite (decide (e = 1)) (by
      rw [VG.Proof.MlKem.AArch64.eval_zero, h3₂, ofNat_beq_zero (by omega)]
      congr 1; exact decide_eq_decide.mpr (by omega))
    (fun he1 => ?_) (fun he1 => ?_)
  · simp only [decide_eq_true_eq] at he1
    subst he1
    exact WP.mono (dOne_k h₂ (by rw [show av I s₂.mem aL = av I s₁.mem aL by rw [m₂], hL₁])) (post hm₂)
  simp only [decide_eq_false_iff_not] at he1
  have hev₂ : word s₂.mem I.B (8 * kEv) = BitVec.ofNat 64 e := by rw [m₂, hev₁]
  have hld₂ := h₂.ws.scr.ld (d := 8 * kEv) (by have := h.ws.h256; unfold kEv sFn; omega)
  refine WP.seq (WP.mono (WP.keep [.x3, .x4] (Q := fun t => t.gpr .x3 = BitVec.ofNat 64 (e % 2) ∧ t.mem = s₂.mem) (by
    brun [h₂.ws.x0, hdr_enc (show kEv < 32 by decide), hld₂, hev₂]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (BitVec.setWidth 64 1#16).toNat = 1 from rfl, Nat.and_one_is_mod, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat]
    omega) (by decide) (by decide) (by decide +kernel)) fun s₃ ⟨⟨h3₃, m₃⟩, k₃⟩ => ?_)
  have h₃ := h₂.regs m₃ k₃
  have hm₃ : s₃.mem = s.mem := m₃.trans hm₂
  have hev₃ : word s₃.mem I.B (8 * kEv) = BitVec.ofNat 64 e := by rw [hm₃, hev]
  have hL₃ : av I s₃.mem aL = L := by rw [show av I s₃.mem aL = av I s.mem aL by rw [hm₃], hL]
  refine WP.ite (decide (e % 2 = 1)) (by
      rw [VG.Proof.MlKem.AArch64.eval_nonzero, h3₃]
      rcases Nat.mod_two_eq_zero_or_one e with h2 | h2 <;> rw [h2] <;> decide)
    (fun ho => ?_) (fun ho => ?_)
  · simp only [decide_eq_true_eq] at ho
    exact WP.mono (dOdd_k h₃ (by omega) he64 ho hev₃ hL₃ hLW) (post hm₃)
  · simp only [decide_eq_false_iff_not] at ho
    exact WP.mono (dEven_k h₃ he64 (by omega) hev₃ hL₃ hLW) (post hm₃)

end VG.Proof.RsaKeyGen.AArch64.Key
