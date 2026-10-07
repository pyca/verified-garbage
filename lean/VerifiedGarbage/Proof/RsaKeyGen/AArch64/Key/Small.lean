import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.DBase

/-!
# An RSA key from its primes on AArch64: `d` too small

`smallMask`: `x15 := kOk & ` the mask of `d ≤ 2^(64 w)`, by `ltA` against
`[aC] = 2^(64 w) + 1` (`smallMask_k`).
-/

namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Key
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.RsaKeyGen.AArch64.Candidate (loadE kE kElen)

/-- Word `k` of a number written, from zero. -/
theorem wv_set_k {m : Mem} {B : Addr} {d N k : Nat} (v : BitVec 64) (hz : word m B (d + 8 * k) = 0)
    (hd : d + 8 * N ≤ 2 ^ 64) (hk : k < N) : ∀ n ≤ N,
    wv (m.writeW (off B (d + 8 * k)) v) B d n = wv m B d n + (if k < n then 2 ^ (64 * k) * v.toNat else 0)
  | 0, _ => by simp [wv]
  | n + 1, hn => by
    rw [wv, wv, wv_set_k v hz hd hk n (by omega)]
    by_cases hkn : n = k
    · subst hkn; rw [word_writeW_self, hz]; simp
    · rw [(writeW_outside m B v (d := d + 8 * k) (by omega)).word (by omega) (by omega)]
      by_cases hk' : k < n
      · simp [hk', show k < n + 1 by omega]; omega
      · simp [hk', show ¬ k < n + 1 by omega]

/-- `smallMask`: `x15 := kOk & ` the mask of `d ≤ 2^(64 w)` (`ltA_k` against
`2^(64 w) + 1`). -/
theorem smallMask_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {w : Nat} (hW : I.W = 2 * w) {ok : Bool}
    (hok : word s.mem I.B (8 * kOk) = mask ok) :
    WP isa (seqs smallMask) s fun t => KS I s₀ t ∧ KF I.B I.W [.arr aC] s.mem t.mem ∧
      t.gpr .x15 = mask (decide (av I s.mem aDd ≤ 2 ^ (64 * w)) && ok) := by
  have hn := h.ws.scr.nowrap
  have hZ := h.hZ
  have hw1 : 1 ≤ w := by have := h.ws.w1; omega
  have hw2 := h.ws.w2
  have sC := h.ws.sl (j := aC) (by decide)
  unfold smallMask
  simp only [List.append_assoc]
  refine wp_seqs_append (by simp [constA]) (by simp) (WP.mono (constA_k h (x := 1) (by decide))
    fun s₁ ⟨h₁, f₁, c₁, _⟩ => ?_)
  -- Word `w` of `[aC]` set: `[aC] = 2^(64 w) + 1`.
  refine wp_seqs_append (by simp) (by simp [ltA, cmpA]) ?_
  simp only [seqs]
  rw [← List.append_assoc, WP.block_append_iff]
  refine WP.mono (wsBase16_ok h₁ aC) fun s₂ ⟨⟨h16, h12, _, m₂⟩, k₂⟩ => ?_
  have hs₂ := h₁.ws.scr.congr k₂.wr
  have ew : BitVec.ofNat 64 I.W >>> 1 = BitVec.ofNat 64 w := by
    rw [ofNat_shr1 (by omega)]; congr 1; omega
  have e8 : BitVec.ofNat 64 w <<< 3 = BitVec.ofNat 64 (8 * w) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (show w < 2 ^ 64 by omega)]
    omega
  have ea : off I.B (slot I.W aC) + BitVec.ofNat 64 (8 * w) = off I.B (slot I.W aC + 8 * w) :=
    VG.Offset.add_add _ _ _
  refine WP.mono (WP.keep [.x3, .x16] (Q := fun t => t.mem = s₁.mem.writeW (off I.B (slot I.W aC + 8 * w))
      (1 : BitVec 64)) (by
    brun [h16, h12, ew, e8, ea, hs₂.st (d := slot I.W aC + 8 * w) (by omega), m₂]
    rfl) (by decide) (by decide) (by decide +kernel)) fun s₃ ⟨m₃, k₃⟩ => ?_
  have o₃ := writeW_outside s₁.mem I.B (1 : BitVec 64) (d := slot I.W aC + 8 * w) (by omega)
  rw [← m₃] at o₃
  have f₃ := KF.arr1 (B := I.B) (W := I.W) (j := aC) o₃ (by omega) (by omega)
  have h₃ := h₁.step f₃ (all_mut_arr (by decide)) (k₂.trans k₃)
  have c₃ : av I s₃.mem aC = 2 ^ (64 * w) + 1 := by
    have hz : word s₁.mem I.B (slot I.W aC + 8 * w) = 0 := by
      have e := VG.Proof.Rsa.AArch64.wv_low (m := s₁.mem) (B := I.B) (e := slot I.W aC) (w := I.W + 2) (by omega)
      rw [c₁] at e
      have h0 : wv s₁.mem I.B (slot I.W aC + 8) (I.W + 2 - 1) = 0 := by
        rcases Nat.eq_zero_or_pos (wv s₁.mem I.B (slot I.W aC + 8) (I.W + 2 - 1)) with h0 | h0
        · exact h0
        · have := Nat.le_mul_of_pos_right (2 ^ 64) h0; omega
      have := (wv_eq_zero_iff _ _ _ _).mp h0 (w - 1) (by omega)
      rwa [show slot I.W aC + 8 + 8 * (w - 1) = slot I.W aC + 8 * w by omega] at this
    have hv1 : av I s₁.mem aC = 1 := av_of_full c₁ (lt_pow_W h (by decide))
    dsimp only [av] at hv1 ⊢
    rw [m₃, wv_set_k (1 : BitVec 64) hz (by omega) (by omega) I.W (Nat.le_refl _), hv1, ite_eq_left (by omega)]
    simp; omega
  have vD : av I s₃.mem aDd = av I s.mem aDd := by
    rw [f₃.av (by decide) (by decide) (by decide) hZ, f₁.av (by decide) (by decide) (by decide) hZ]
  refine wp_seqs_append (by simp [ltA, cmpA]) (by simp) (WP.mono (ltA_k h₃ (a := aDd) (b := aC) (by decide)
    (by decide)) fun s₄ ⟨h₄, m₄, h15, _, _⟩ => ?_)
  rw [vD, c₃] at h15
  simp only [seqs]
  have hok₄ : word s₄.mem I.B (8 * kOk) = mask ok := by
    rw [m₄, f₃.word (by decide) (by decide) (by decide), f₁.word (by decide) (by decide) (by decide), hok]
  have hld := h₄.ws.scr.ld (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega)
  have hd : decide (av I s.mem aDd < 2 ^ (64 * w) + 1) = decide (av I s.mem aDd ≤ 2 ^ (64 * w)) :=
    decide_eq_decide.mpr Nat.lt_succ_iff
  rw [hd] at h15
  refine WP.mono (WP.keep [.x3, .x15] (Q := fun t => t.gpr .x15 = mask (decide (av I s.mem aDd ≤ 2 ^ (64 * w)) && ok) ∧
    t.mem = s₄.mem) (by
      brun [h₄.ws.x0, hdr_enc (show kOk < 32 by decide), hld, hok₄, h15, mask_and'])
      (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h15t, m⟩, k⟩ => ?_
  have f' : KF I.B I.W [.arr aC] s₁.mem t.mem := by rw [m, m₄]; exact f₃
  exact ⟨h₄.regs m k, (f₁.trans f').mono (by simp), h15t⟩

end VG.Proof.RsaKeyGen.AArch64.Key
