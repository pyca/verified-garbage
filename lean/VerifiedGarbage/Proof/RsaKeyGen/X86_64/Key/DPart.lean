import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.DEven

/-!
# An RSA key from its primes on x86-64: `d = e⁻¹ mod L`

`dPart`, by `e`: none for 0, 1 for 1 but `L = 1`, `dOdd` for an odd `e`
and `dEven` for an even one (`dPart_k`).
-/

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.RsaKeyGen.X86_64.Key
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

/-- `e = 1`: `d = 1`, `kOk` the mask of `L ≠ 1`. -/
theorem dOne_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {L : Nat} (hL : av I s.mem aL = L) :
    WP isa (seqs dOne) s fun t => KS I m₀ t ∧ KF I.B I.W csD s.mem t.mem ∧ DRes I 1 L t.mem := by
  have hZ := h.hZ
  unfold dOne
  simp only [List.append_assoc]
  refine wp_seqs_append (by simp [constA]) (by simp [eqMask, eqA]) (WP.mono (constA_k h 1) fun s₁ ⟨h₁, f₁, c₁, _⟩ => ?_)
  have c1 : av I s₁.mem aC = 1 := av_of_full c₁ (two_le_pow h (by decide))
  have vL : av I s₁.mem aL = L := by rw [f₁.av (by decide) (by decide) (by decide) hZ, hL]
  refine wp_seqs_append (by simp [eqMask, eqA]) (by simp) (WP.mono (eqMask_k h₁ (a := aL) (b := aC) (by decide)
    (by decide)) fun s₂ ⟨h₂, m₂, hbp, _⟩ => ?_)
  rw [vL, c1] at hbp
  simp only [seqs]
  have hst := h₂.ws.scr.st (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega)
  refine WP.seq (WP.mono (WP.keep [.rbp] (Q := fun t => t.mem = s₂.mem.writeW (off I.B (8 * kOk))
    (mask (!decide (L = 1)))) (by xrun [State.ea, hdr, h₂.ws.rdi, hdrOff, hst, hbp, sxM1, maskNot]) rfl)
    fun s₃ ⟨m₃, k₃⟩ => ?_)
  obtain ⟨h₃, f₃, ok₃⟩ := h₂.hdrW (i := kOk) (by unfold kOk sFn; omega) m₃ k₃ (by decide)
  refine WP.seq (WP.mono (zeroA_k h₃ (j := aDd) (by decide)) fun s₄ ⟨h₄, f₄, z₄, _⟩ =>
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
      exact av_of_full o₅ (two_le_pow h (by decide))

/-- `dPart`, for `e < 2⁶⁴`. -/
theorem dPart_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {e L : Nat} (he64 : e < 2 ^ 64)
    (hev : word s.mem I.B (8 * kEv) = BitVec.ofNat 64 e) (hL : av I s.mem aL = L) (hLW : L < 2 ^ (64 * I.W)) :
    WP isa dPart s fun t => KS I m₀ t ∧ KF I.B I.W csD s.mem t.mem ∧ DRes I e L t.mem := by
  have hld := h.ws.scr.ld (d := 8 * kEv) (by have := h.ws.h256; unfold kEv sFn; omega)
  unfold dPart
  refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun t => t.cf = some (decide (e < 1)) ∧ t.zf = some (decide (e = 1)) ∧
    t.mem = s.mem) (by
      xrun [State.ea, hdr, h.ws.rdi, hdrOff, hld, hev, sx1]
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt he64, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
        ofNat_sub_beq he64 (by decide)]
      exact ⟨rfl, rfl⟩) rfl) fun s₁ ⟨⟨hcf, hzf, m₁⟩, k₁⟩ => ?_)
  have h₁ := h.step (cs := []) (by rw [m₁]; exact KF.refl _ _ _) rfl k₁ (by decide)
  have hev₁ : word s₁.mem I.B (8 * kEv) = BitVec.ofNat 64 e := by rw [m₁, hev]
  have hL₁ : av I s₁.mem aL = L := by rw [show av I s₁.mem aL = av I s.mem aL by rw [m₁], hL]
  have post : ∀ t, KS I m₀ t ∧ KF I.B I.W csD s₁.mem t.mem ∧ DRes I e L t.mem →
      KS I m₀ t ∧ KF I.B I.W csD s.mem t.mem ∧ DRes I e L t.mem := fun t ⟨a, b, c⟩ => ⟨a, by rw [← m₁]; exact b, c⟩
  refine WP.ite (decide (e < 1)) (by simp [eval, hcf]) (fun he0 => ?_) (fun he0 => ?_)
  · -- `e = 0`: no inverse.
    simp only [decide_eq_true_eq] at he0
    have hst := h₁.ws.scr.st (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega)
    refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = s₁.mem.writeW (off I.B (8 * kOk)) (mask false)) (by
      unfold dZero
      xrun [State.ea, hdr, h₁.ws.rdi, hdrOff, hst]
      rfl) rfl) fun t ⟨m, k⟩ => post t ?_
    obtain ⟨ht, ft, okt⟩ := h₁.hdrW (i := kOk) (by unfold kOk sFn; omega) m k (by decide)
    refine ⟨ht, ft.mono (by simp), false, okt, ?_, fun d hd => ?_⟩
    · rw [show e = 0 by omega, VG.Proof.RsaKeyGen.inverse_zero]; simp
    · rw [show e = 0 by omega, VG.Proof.RsaKeyGen.inverse_zero] at hd; cases hd
  simp only [decide_eq_false_iff_not] at he0
  refine WP.ite (decide (e = 1)) (by simp [eval, hzf]) (fun he1 => ?_) (fun he1 => ?_)
  · simp only [decide_eq_true_eq] at he1
    subst he1
    exact WP.mono (dOne_k h₁ hL₁) post
  simp only [decide_eq_false_iff_not] at he1
  refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun t => t.zf = some (decide (e % 2 = 0)) ∧ t.mem = s₁.mem) (by
      have hld₁ := h₁.ws.scr.ld (d := 8 * kEv) (by have := h.ws.h256; unfold kEv sFn; omega)
      xrun [State.ea, hdr, h₁.ws.rdi, hdrOff, hld₁, hev₁, sx1]
      rw [and1_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt he64]
      rcases Nat.mod_two_eq_zero_or_one e with h2 | h2 <;> rw [h2] <;> decide) rfl) fun s₂ ⟨⟨hzf₂, m₂⟩, k₂⟩ => ?_)
  have h₂ := h₁.step (cs := []) (by rw [m₂]; exact KF.refl _ _ _) rfl k₂ (by decide)
  have post₂ : ∀ t, KS I m₀ t ∧ KF I.B I.W csD s₂.mem t.mem ∧ DRes I e L t.mem →
      KS I m₀ t ∧ KF I.B I.W csD s.mem t.mem ∧ DRes I e L t.mem := fun t ⟨a, b, c⟩ =>
    ⟨a, by rw [← m₁, ← m₂]; exact b, c⟩
  have hev₂ : word s₂.mem I.B (8 * kEv) = BitVec.ofNat 64 e := by rw [m₂, hev₁]
  have hL₂ : av I s₂.mem aL = L := by rw [show av I s₂.mem aL = av I s₁.mem aL by rw [m₂], hL₁]
  refine WP.ite (decide (e % 2 = 1)) (by
    simp only [eval, hzf₂, Option.map_some, Option.some.injEq]
    rcases Nat.mod_two_eq_zero_or_one e with h2 | h2 <;> simp [h2]) (fun ho => ?_) (fun ho => ?_)
  · simp only [decide_eq_true_eq] at ho
    exact WP.mono (dOdd_k h₂ (by omega) he64 ho hev₂ hL₂ hLW) post₂
  · simp only [decide_eq_false_iff_not] at ho
    exact WP.mono (dEven_k h₂ he64 (by omega) hev₂ hL₂ hLW) post₂

end VG.Proof.RsaKeyGen.X86_64.Key
