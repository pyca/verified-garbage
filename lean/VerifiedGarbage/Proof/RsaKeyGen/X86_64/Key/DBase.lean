import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.Lcm
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.Minv

/-!
# An RSA key from its primes on x86-64: the pieces of `d`

`[aE] := e` (`loadEv_k`), the masks of `L ≥ 2` (`lGe2_k`) and of a gcd of 1
(`gcdIsOne_k`) into `kOk`, and the inverse's start (`invFrom_k`).
-/

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.RsaKeyGen.X86_64.Key
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

theorem two_le_pow {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {x : Nat} (hx : x < 2 ^ 64) :
    x < 2 ^ (64 * I.W) :=
  Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by have := h.ws.w1; omega))

/-- `loadEv`: `[aE] := e` over `W + 2` words. -/
theorem loadEv_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {e : Nat} (he : e < 2 ^ 64)
    (hev : word s.mem I.B (8 * kEv) = BitVec.ofNat 64 e) :
    WP isa (seqs loadEv) s fun t => KS I m₀ t ∧ KF I.B I.W [.arr aE] s.mem t.mem ∧
      wv t.mem I.B (slot I.W aE) (I.W + 2) = e := by
  have hn := h.ws.scr.nowrap
  have sE := h.ws.sl (j := aE) (by decide)
  simp only [loadEv, seqs]
  refine WP.seq (WP.mono (zeroA_k h (j := aE) (by decide)) fun s₁ ⟨h₁, f₁, z₁, _⟩ => ?_)
  have hev₁ : word s₁.mem I.B (8 * kEv) = BitVec.ofNat 64 e := by rw [f₁.word (by decide) (by decide) (by decide), hev]
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono h₁.ws.ws_ok fun s₂ ⟨_, h9, m₂, k₂⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (base_ok aE (r := .rbx) (by decide) ((k₂.gpr (by decide)).trans h₁.ws.rdi) h9)
    fun s₃ ⟨hbx, m₃, k₃⟩ => ?_
  have hs₃ := h₁.ws.scr.congr (k₂.trans k₃).2.2
  have hdi₃ : s₃.gpr .rdi = I.B := ((k₂.trans k₃).gpr (by decide)).trans h₁.ws.rdi
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = s₁.mem.writeW (off I.B (slot I.W aE)) (BitVec.ofNat 64 e)) (by
    xrun [State.ea, at0, hdr, hbx, hdi₃, hdrOff, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
      hs₃.ld (d := 8 * kEv) (by have := h.ws.h256; unfold kEv sFn; omega), hs₃.st (d := slot I.W aE) (by omega),
      m₃, m₂, hev₁]) rfl) fun t ⟨hm, k₄⟩ => ?_
  have o₄ := writeW_outside s₁.mem I.B (BitVec.ofNat 64 e) (d := slot I.W aE) (by omega)
  rw [← hm] at o₄
  have f₄ := KF.arr1 (I := I) (j := aE) o₄ (Nat.le_refl _) (by omega)
  refine ⟨h₁.step f₄ (all_mut_arr (by decide)) ((k₂.trans k₃).trans k₄) (by decide), (f₁.trans f₄).mono (by simp), ?_⟩
  rw [hm]
  have := wv_put (m := s₁.mem) (B := I.B) (d := slot I.W aE) (N := I.W + 2) (k := 0) (BitVec.ofNat 64 e)
    ((wv_eq_zero_iff _ _ _ _).mp z₁) (by omega) (by omega) (I.W + 2) (Nat.le_refl _)
  rw [Nat.mul_zero, Nat.add_zero] at this
  rw [this, ite_eq_left (show 0 < I.W + 2 by omega), Nat.pow_zero, Nat.one_mul, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt he]

/-- `lGe2`: `kOk := ` the mask of `L ≥ 2`. -/
theorem lGe2_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) :
    WP isa (seqs lGe2) s fun t => KS I m₀ t ∧ KF I.B I.W [.arr aC, .hdr kOk] s.mem t.mem ∧
      word t.mem I.B (8 * kOk) = mask (!decide (av I s.mem aL < 2)) := by
  have hZ := h.hZ
  unfold lGe2
  simp only [List.append_assoc]
  refine wp_seqs_append (by simp [constA]) (by simp [ltA]) (WP.mono (constA_k h 2) fun s₁ ⟨h₁, f₁, c₁, _⟩ => ?_)
  have c2 : av I s₁.mem aC = 2 := av_of_full c₁ (two_le_pow h (by decide))
  have vL : av I s₁.mem aL = av I s.mem aL := f₁.av (by decide) (by decide) (by decide) hZ
  refine wp_seqs_append (by simp [ltA]) (by simp) (WP.mono (ltA_k h₁ (a := aL) (b := aC) (by decide) (by decide))
    fun s₂ ⟨h₂, m₂, hbp, _, _, _, k₂⟩ => ?_)
  rw [vL, c2] at hbp
  simp only [seqs]
  have hst := h₂.ws.scr.st (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega)
  refine WP.mono (WP.keep [.rbp] (Q := fun t => t.mem = s₂.mem.writeW (off I.B (8 * kOk))
    (mask (!decide (av I s.mem aL < 2)))) (by xrun [State.ea, hdr, h₂.ws.rdi, hdrOff, hst, hbp, sxM1, maskNot]) rfl)
    fun t ⟨hm, k₃⟩ => ?_
  obtain ⟨ht, f₃, hw⟩ := h₂.hdrW (i := kOk) (by unfold kOk sFn; omega) hm k₃ (by decide)
  exact ⟨ht, (f₁.trans (by rw [← m₂]; exact f₃)).mono (by simp), hw⟩

/-- `gcdIsOne`: `kOk &= ` the mask of `[aV] = 1`. -/
theorem gcdIsOne_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {c : Bool}
    (hok : word s.mem I.B (8 * kOk) = mask c) :
    WP isa (seqs gcdIsOne) s fun t => KS I m₀ t ∧ KF I.B I.W [.arr aC, .hdr kOk] s.mem t.mem ∧
      word t.mem I.B (8 * kOk) = mask (decide (av I s.mem aV = 1) && c) := by
  have hZ := h.hZ
  unfold gcdIsOne
  simp only [List.append_assoc]
  refine wp_seqs_append (by simp [constA]) (by simp [eqMask, eqA]) (WP.mono (constA_k h 1) fun s₁ ⟨h₁, f₁, c₁, _⟩ => ?_)
  have c1 : av I s₁.mem aC = 1 := av_of_full c₁ (two_le_pow h (by decide))
  have vV : av I s₁.mem aV = av I s.mem aV := f₁.av (by decide) (by decide) (by decide) hZ
  have hok₁ : word s₁.mem I.B (8 * kOk) = mask c := by rw [f₁.word (by decide) (by decide) (by decide), hok]
  refine wp_seqs_append (by simp [eqMask, eqA]) (by simp) (WP.mono (eqMask_k h₁ (a := aV) (b := aC) (by decide)
    (by decide)) fun s₂ ⟨h₂, m₂, hbp, k₂⟩ => ?_)
  rw [vV, c1] at hbp
  simp only [seqs]
  have hst := h₂.ws.scr.st (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega)
  have hld := h₂.ws.scr.ld (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega)
  have hok₂ : word s₂.mem I.B (8 * kOk) = mask c := by rw [m₂, hok₁]
  refine WP.mono (WP.keep [.rbp] (Q := fun t => t.mem = s₂.mem.writeW (off I.B (8 * kOk))
    (mask (decide (av I s.mem aV = 1) && c))) (by
      xrun [State.ea, hdr, h₂.ws.rdi, hdrOff, hst, hld, hbp, hok₂, mask_and']) rfl)
    fun t ⟨hm, k₃⟩ => ?_
  obtain ⟨ht, f₃, hw⟩ := h₂.hdrW (i := kOk) (by unfold kOk sFn; omega) hm k₃ (by decide)
  exact ⟨ht, (f₁.trans (by rw [← m₂]; exact f₃)).mono (by simp), hw⟩

/-- `invFrom j`: `v := [j]`, `x₁ := 1`, `x₂ := 0`. -/
theorem invFrom_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {j : Nat} (hj : j < 16) (hjV : j ≠ aV) :
    WP isa (seqs (invFrom j)) s fun t => KS I m₀ t ∧ KF I.B I.W [.arr aV, .arr aX₁, .arr aX₂] s.mem t.mem ∧
      av I t.mem aV = av I s.mem j ∧ av I t.mem aX₁ = 1 ∧ av I t.mem aX₂ = 0 := by
  have hZ := h.hZ
  have hw1 := h.ws.w1
  simp only [invFrom, seqs]
  refine WP.seq (WP.mono (zeroA_k h (j := aV) (by decide)) fun s₁ ⟨h₁, f₁, _, _⟩ =>
    WP.seq (WP.mono (copyA_k h₁ (o := aV) (a := j) (by decide) hj hjV.symm) fun s₂ ⟨h₂, f₂, v₂, _, _⟩ =>
      WP.seq (WP.mono (zeroA_k h₂ (j := aX₁) (by decide)) fun s₃ ⟨h₃, f₃, z₃, _⟩ =>
        WP.seq (WP.mono (setOne_k h₃ (j := aX₁) (by decide) z₃) fun s₄ ⟨h₄, f₄, o₄, _⟩ =>
          WP.mono (zeroA_k h₄ (j := aX₂) (by decide)) fun t ⟨ht, f₅, z₅, _⟩ => ?_))))
  refine ⟨ht, ((((f₁.trans f₂).trans f₃).trans f₄).trans f₅).mono (by simp), ?_, ?_, (wv_zero2 z₅).1⟩
  · rw [f₅.av (by decide) (by decide) (by decide) hZ, f₄.av (by decide) (by decide) (by decide) hZ,
      f₃.av (by decide) (by decide) (by decide) hZ, v₂, f₁.av (by decide) hj (by simp [hjV]) hZ]
  · rw [f₅.av (by decide) (by decide) (by decide) hZ]
    exact av_of_full o₄ (two_le_pow h (by decide))

end VG.Proof.RsaKeyGen.X86_64.Key
