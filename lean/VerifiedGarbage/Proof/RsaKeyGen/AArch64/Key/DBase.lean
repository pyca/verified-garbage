import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Shared
import VerifiedGarbage.Proof.Bignum.AArch64.Setup

/-!
# An RSA key from its primes on AArch64: the pieces of `d`

`[aE] := e` (`loadEv_k`), the mask of `L ≥ 2` into `kOk` (`lGe2_k`), and
`minv`'s inverse of `e` modulo `2⁶⁴`, left in `x4` (`minvX4_ok`).
-/

namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Key
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.RsaKeyGen.AArch64.Candidate (loadE kE kElen)

/-- A word is below `2^(64 W)`. -/
theorem lt_pow_W {I : KIn} {s₀ s : State} (h : KS I s₀ s) {x : Nat} (hx : x < 2 ^ 64) : x < 2 ^ (64 * I.W) :=
  Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by have := h.ws.w1; omega))

/-! ## `e⁻¹ mod 2⁶⁴` -/

theorem inv_of_emod {a x : Nat} (h : ((a : Int) * x - 1) % (2 ^ 64 : Int) = 0) : a * x % 2 ^ 64 = 1 := by
  obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero h
  have e : ((a * x : Nat) : Int) = 1 + 2 ^ 64 * k := by push_cast; omega
  have : ((a * x : Nat) : Int) % 2 ^ 64 = 1 := by rw [e, Int.add_mul_emod_self_left]; decide
  exact_mod_cast this

/-- `minv`: `x3⁻¹ mod 2⁶⁴` into `x4`, for an odd `x3`. -/
theorem minvX4_ok (s : State) (hodd : (s.gpr .x3).toNat % 2 = 1) :
    WP isa (.block minv) s fun t =>
      ((s.gpr .x3).toNat * (t.gpr .x4).toNat % 2 ^ 64 = 1 ∧ t.gpr .x3 = s.gpr .x3 ∧ t.mem = s.mem) ∧
        Keep [.x4, .x5, .x6, .x15] s t := by
  unfold minv
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x4] (c := .block [mov .x4 .x3]) (Q := fun t =>
    t.gpr .x4 = s.gpr .x3 ∧ t.mem = s.mem) (by brun) (by decide) rfl (by decide +kernel))
    fun t₀ ⟨⟨h₀, hm₀⟩, k₀⟩ => ?_
  have hb₀ : t₀.gpr .x3 = s.gpr .x3 := k₀.gpr .x3 (by decide)
  have e₀ : (((t₀.gpr .x3).toNat : Int) * (t₀.gpr .x4).toNat - 1) % (2 ^ 3 : Int) = 0 := by
    rw [hb₀, h₀]
    have h1 := odd_sq _ hodd
    have h2 : (((s.gpr .x3).toNat : Int) * (s.gpr .x3).toNat) % 8 = 1 := by
      simpa only [Int.natCast_mul, Int.natCast_emod, show ((8 : Nat) : Int) = 8 from rfl,
        show ((1 : Nat) : Int) = 1 from rfl] using congrArg (fun n : Nat => (n : Int)) h1
    show (((s.gpr .x3).toNat : Int) * (s.gpr .x3).toNat - 1) % 8 = 0
    omega
  rw [WP.block_append_iff]
  refine WP.mono (newton_step_ok t₀ (j := 3) (by decide) e₀) fun t₁ ⟨⟨e₁, hb₁, hm₁⟩, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (newton_step_ok t₁ (j := 6) (by decide) e₁) fun t₂ ⟨⟨e₂, hb₂, hm₂⟩, k₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (newton_step_ok t₂ (j := 12) (by decide) e₂) fun t₃ ⟨⟨e₃, hb₃, hm₃⟩, k₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (newton_step_ok t₃ (j := 24) (by decide) e₃) fun t₄ ⟨⟨e₄, hb₄, hm₄⟩, k₄⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (newton_step_ok t₄ (j := 32) (by decide) (VG.Proof.Bignum.emod_pow_weaken (by decide) e₄))
    fun t₅ ⟨⟨e₅, hb₅, hm₅⟩, k₅⟩ => ?_
  have hb : t₅.gpr .x3 = s.gpr .x3 := hb₅.trans (hb₄.trans (hb₃.trans (hb₂.trans (hb₁.trans hb₀))))
  have kk := ((((k₀.trans k₁).trans k₂).trans k₃).trans k₄).trans k₅
  rw [hb] at e₅
  refine WP.mono (WP.keep [.x6, .x15] (Q := fun t => t.mem = t₅.mem)
    (by brun) (by decide) (by decide) (by decide +kernel)) fun t ⟨hm, k⟩ =>
    ⟨⟨?_, (k.gpr .x3 (by decide)).trans hb, ?_⟩, (kk.trans k).mono (by decide)⟩
  · rw [k.gpr .x4 (by decide)]; exact inv_of_emod e₅
  · rw [hm, hm₅, hm₄, hm₃, hm₂, hm₁, hm₀]

/-! ## `[aE] := e` -/

/-- `loadEv`: `[aE] := e` over `W + 2` words. -/
theorem loadEv_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {e : Nat} (he : e < 2 ^ 64)
    (hev : word s.mem I.B (8 * kEv) = BitVec.ofNat 64 e) :
    WP isa (seqs loadEv) s fun t => KS I s₀ t ∧ KF I.B I.W [.arr aE] s.mem t.mem ∧
      wv t.mem I.B (slot I.W aE) (I.W + 2) = e := by
  have hn := h.ws.scr.nowrap
  have sE := h.ws.sl (j := aE) (by decide)
  simp only [loadEv, seqs]
  refine WP.seq (WP.mono (zeroA_k h (j := aE) (by decide)) fun s₁ ⟨h₁, f₁, z₁, _, _⟩ => ?_)
  have hev₁ : word s₁.mem I.B (8 * kEv) = BitVec.ofNat 64 e := by
    rw [f₁.word (by decide) (by decide) (by decide), hev]
  rw [WP.block_append_iff]
  refine WP.mono (wsBase16_ok h₁ aE) fun s₂ ⟨⟨h16, _, _, m₂⟩, k₂⟩ => ?_
  have hs₂ := h₁.ws.scr.congr k₂.wr
  have hx0 : s₂.gpr .x0 = I.B := (k₂.gpr .x0 (by decide)).trans h₁.ws.x0
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.mem = s₁.mem.writeW (off I.B (slot I.W aE)) (BitVec.ofNat 64 e)) (by
    brun [hx0, hdr_enc (show kEv < 32 by decide), h16,
      hs₂.ld (d := 8 * kEv) (by have := h.ws.h256; unfold kEv sFn; omega), hs₂.st (d := slot I.W aE) (by omega),
      m₂, hev₁]) (by decide) (by decide) (by decide +kernel)) fun t ⟨hm, k₃⟩ => ?_
  have o₃ := writeW_outside s₁.mem I.B (BitVec.ofNat 64 e) (d := slot I.W aE) (by omega)
  rw [← hm] at o₃
  have f₃ := KF.arr1 (B := I.B) (W := I.W) (j := aE) o₃ (Nat.le_refl _) (by omega)
  refine ⟨h₁.step f₃ (all_mut_arr (by decide)) (k₂.trans k₃), (f₁.trans f₃).mono (by simp), ?_⟩
  rw [hm, wv_put0 _ z₁ (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt he]

/-! ## `L ≥ 2` -/

/-- `lGe2`: `kOk := ` the mask of `L ≥ 2` (`geA_k`). -/
theorem lGe2_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) :
    WP isa (seqs lGe2) s fun t => KS I s₀ t ∧ KF I.B I.W [.arr aC, .hdr kOk] s.mem t.mem ∧
      word t.mem I.B (8 * kOk) = mask (decide (2 ≤ av I s.mem aL)) := by
  have hZ := h.hZ
  unfold lGe2
  simp only [List.append_assoc]
  refine wp_seqs_append (by simp [constA]) (by simp [geA, cmpA]) (WP.mono (constA_k h (x := 2) (by decide))
    fun s₁ ⟨h₁, f₁, c₁, _⟩ => ?_)
  have c2 : av I s₁.mem aC = 2 := av_of_full c₁ (lt_pow_W h (by decide))
  have vL : av I s₁.mem aL = av I s.mem aL := f₁.av (by decide) (by decide) (by decide) hZ
  refine wp_seqs_append (by simp [geA, cmpA]) (by simp) (WP.mono (geA_k h₁ (a := aL) (b := aC) (by decide)
    (by decide)) fun s₂ ⟨h₂, m₂, h15, _, _⟩ => ?_)
  rw [vL, c2] at h15
  simp only [seqs]
  have hst := h₂.ws.scr.st (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega)
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = s₂.mem.writeW (off I.B (8 * kOk))
    (mask (decide (2 ≤ av I s.mem aL)))) (by
      brun [h₂.ws.x0, hdr_enc (show kOk < 32 by decide), hst, h15]) rfl rfl rfl)
    fun t ⟨hm, k₃⟩ => ?_
  obtain ⟨ht, f₃, hw⟩ := h₂.hdrW (i := kOk) (by unfold kOk sFn; omega) hm k₃
  exact ⟨ht, (f₁.trans (by rw [← m₂]; exact f₃)).mono (by simp), hw⟩

end VG.Proof.RsaKeyGen.AArch64.Key
