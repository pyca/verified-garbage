import VerifiedGarbage.Proof.Rsa.AArch64.RpHalf
import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
import VerifiedGarbage.Proof.Bignum.AArch64.Csub

/-!
# `vg_rsa_recover_primes` on AArch64: Montgomery form

`minvBlk`: `-n⁻¹ mod 2⁶⁴` into `sMinv` (`minvBlk_ok`). `mont`: `R² mod n`
as `vg_rsa_public` computes it, 1, `R mod n` and `n - R mod n`, the
Montgomery forms of 1 and `-1` (`mont_ok`).
-/

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.Recover
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY aOne sCnt)

/-- `minvBlk`: `-n⁻¹ mod 2⁶⁴` into `sMinv`, for an odd `n`. -/
theorem minvBlk_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w)
    (hodd : (word s.mem B (slot w aN)).toNat % 2 = 1) :
    WP isa (.block minvBlk) s fun t =>
      ((word t.mem B (slot w aN)).toNat * (word t.mem B (8 * sMinv)).toNat + 1) % 2 ^ 64 = 0 ∧
      Frm B (rg w [] [sMinv]) s.mem t.mem ∧ Keep [.x3, .x4, .x5, .x6, .x11, .x12, .x15, .x16] s t := by
  have hn := h.scr.nowrap
  have h256 := h.h256
  have sN := h.sl (j := aN) (by decide)
  have hN0 := hdr_lt_slot w aN (show sMinv < 32 by decide)
  unfold minvBlk
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono h.ws_ok fun t₁ ⟨⟨_, h11, m₁, _⟩, k₁⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (base_ok aN .x16 ((k₁.gpr .x0 (by decide)).trans h.x0) h11) fun t₂ ⟨⟨h16, m₂, _⟩, k₂⟩ =>
    WP.block_append_iff.mpr ?_
  have hs₂ := h.scr.congr (k₁.trans k₂).wr
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.gpr .x3 = word s.mem B (slot w aN) ∧ t.mem = s.mem) (by
    brun [h16, hs₂.ld (d := slot w aN) (by omega), m₂, m₁]) (by decide) (by decide) (by decide +kernel))
    fun t₃ ⟨⟨h3, m₃⟩, k₃⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (minv_ok t₃ (by rw [h3]; exact hodd)) fun t₄ ⟨hi, k₄, m₄⟩ => ?_
  have k14 := ((k₁.trans k₂).trans k₃).trans k₄
  have h0₄ : t₄.gpr .x0 = B := (k14.gpr .x0 (by decide)).trans h.x0
  have hs₄ := h.scr.congr k14.wr
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = t₄.mem.writeW (off B (8 * sMinv)) (t₄.gpr .x15)) (by
    brun [h0₄, hdr_enc (show sMinv < 32 by decide), hs₄.st (d := 8 * sMinv) (by simp only [sMinv]; omega)])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨mt, k₅⟩ => ?_
  have o := writeW_outside t₄.mem B (t₄.gpr .x15) (d := 8 * sMinv) (by simp only [sMinv]; omega)
  rw [← mt] at o
  have m4 : t₄.mem = s.mem := m₄.trans m₃
  refine ⟨?_, by rw [← m4]; exact Frm.rg_of_hdr o _ _ (List.mem_singleton_self _), (k14.trans k₅).mono (by decide)⟩
  rw [o.word (Or.inr (by omega)) (by omega), mt, word_writeW_self, m4, ← h3]
  exact hi

/-- The bases of a subtraction `[c] := [a] - [b]` over `w` words, from the
carry set. -/
theorem subSet_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) (a b c : Nat) :
    WP isa (.block (ws ++ [movi .x7 0, mov .x14 .x12, .subs .x .x3 .x7 .x7] ++ base a .x16 ++ base b .x17 ++
      base c .x13)) s fun t =>
      (t.gpr .x16 = off B (slot w a) ∧ t.gpr .x17 = off B (slot w b) ∧ t.gpr .x13 = off B (slot w c) ∧
        t.gpr .x14 = BitVec.ofNat 64 w ∧ t.gpr .x12 = BitVec.ofNat 64 w ∧ t.gpr .x7 = 0 ∧ t.c = true ∧
        t.mem = s.mem) ∧ Keep [.x3, .x7, .x11, .x12, .x13, .x14, .x16, .x17] s t := by
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono h.ws_ok fun t₁ ⟨⟨h12, h11, m₁, _⟩, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x7, .x14] (Q := fun t => t.gpr .x14 = BitVec.ofNat 64 w ∧ t.gpr .x7 = 0 ∧
      t.c = true ∧ t.mem = t₁.mem) (by brun [h12]) (by decide) (by decide) (by decide +kernel))
    fun t₂ ⟨⟨h14, h7, hc, m₂⟩, k₂⟩ => ?_
  have h0₂ : t₂.gpr .x0 = B := ((k₁.trans k₂).gpr .x0 (by decide)).trans h.x0
  rw [← List.append_assoc]
  refine WP.mono (base3_ok a b c .x16 .x17 .x13 h0₂ ((k₂.gpr .x11 (by decide)).trans h11))
    fun t ⟨⟨h16, h17, h13, m₃, c₃⟩, k₃⟩ => ⟨⟨h16, h17, h13, (k₃.gpr .x14 (by decide)).trans h14,
      (k₃.gpr .x12 (by decide)).trans ((k₂.gpr .x12 (by decide)).trans h12), (k₃.gpr .x7 (by decide)).trans h7,
      c₃.trans hc, by rw [m₃, m₂, m₁]⟩, ((k₁.trans k₂).trans k₃).mono (by decide)⟩

/-- The loop of `subBody`: `[x13] := [x16] - [x17]` over `N` words, from the
carry set. -/
theorem subLoop_ok {s : State} {B : Addr} {Z N eA eN eT : Nat} (hs : Scr s B Z)
    (h16 : s.gpr .x16 = off B eA) (h17 : s.gpr .x17 = off B eN) (h13 : s.gpr .x13 = off B eT)
    (h14 : s.gpr .x14 = BitVec.ofNat 64 N) (hc : s.c = true) (hN1 : 1 ≤ N) (hN : N < 2 ^ 31)
    (hA : eA + 8 * N ≤ Z) (hNz : eN + 8 * N ≤ Z) (hT : eT + 8 * N ≤ Z)
    (sA : eT + 8 * N ≤ eA ∨ eA + 8 * N ≤ eT) (sN : eT + 8 * N ≤ eN ∨ eN + 8 * N ≤ eT) :
    WP isa (countLoop .x14 subBody) s fun t =>
      wv t.mem B eT N + wv s.mem B eN N = wv s.mem B eA N + 2 ^ (64 * N) * (!t.c).toNat ∧
      Outside B eT (8 * N) s.mem t.mem ∧ Keep [.x3, .x4, .x13, .x14, .x16, .x17] s t := by
  unfold countLoop subBody
  refine WP.mono (wp_countdown (N := N) (by omega) (by omega) (SubInv s B Z eA eN eT)
    (fun j hj t hI _ => subStep_ok hA hNz hT sA sN hj hI)
    ⟨hs, Keep.refl _ _, by rw [h16]; rfl, by rw [h17]; rfl, by rw [h13]; rfl, Outside.refl _ _ _ _,
      by rw [hc]; rfl⟩ h14) fun t hI => ⟨hI.val, hI.out, hI.keep⟩

/-- `mont`: `R² mod n`, 1, `R mod n` and `n - R mod n`, for the odd `n` in
its array, of `w` words with the top one not zero, and `-n⁻¹` in `sMinv`. -/
theorem mont_ok (M : Mont) {s : State} {B : Addr} {Z w N : Nat} (h : Ws s B Z w)
    (hinv : ((word s.mem B (slot w aN)).toNat * (word s.mem B (8 * sMinv)).toNat + 1) % 2 ^ 64 = 0)
    (hn : wv s.mem B (slot w aN) w = N) (hodd : N % 2 = 1) (hlo : 2 ^ (64 * (w - 1)) ≤ N) :
    WP isa (seqs (mont M.mm)) s fun t => Ws t B Z w ∧
      wv t.mem B (slot w aR2) w < N ∧ wv t.mem B (slot w aR2) w % N = 2 ^ (64 * w) * 2 ^ (64 * w) % N ∧
      wv t.mem B (slot w aOne) w = 1 ∧ wv t.mem B (slot w aO) w = 2 ^ (64 * w) % N ∧
      wv t.mem B (slot w aNg) w = N - 2 ^ (64 * w) % N ∧
      Frm B (rg w [aAcc, aTmp, aR2, aOne, aY, aO, aNg] [sCnt]) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn0 := h.scr.nowrap
  have h256 := h.h256
  have hZ := h.hZ
  have hw1 := h.w1
  have hw2 := h.w2
  have hZ16 : slot w 16 ≤ 2 ^ 64 := by omega
  have hR : Nat.Coprime (2 ^ (64 * w)) N := VG.Proof.Bignum.coprime_pow2 hodd _
  have hN1 : 1 < N := by
    have : 2 ^ 64 ≤ 2 ^ (64 * (w - 1)) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  obtain ⟨minv, hmv⟩ : ∃ v, word s.mem B (8 * sMinv) = v := ⟨_, rfl⟩
  rw [hmv] at hinv
  have hg := h.good
  rw [hmv] at hg
  unfold mont
  refine wp_seqs_append (by simp [VG.Impl.Rsa.AArch64.r2Steps]) (by simp) (WP.mono (r2_ok M hg.1 hg.2 hw1 (by omega) hn hinv hodd hlo)
    fun t₂ ⟨hg₂, hlt, hc, hf₂, k₂⟩ => ?_)
  have hf₂' : Frm B (rg w [aAcc, aTmp, aR2] [sCnt]) s.mem t₂.mem := hf₂
  have hw₂ : Ws t₂ B Z w := h.congrG hf₂' (by decide) k₂ (by decide)
  have hN₂ : wv t₂.mem B (slot w aN) w = N := by
    rw [hf₂'.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega), hn]
  have hi₂ : ((word t₂.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [hf₂'.rg_word0 hZ16 (by decide) (by decide) (by decide)]; exact hinv
  have hmv₂ : word t₂.mem B (8 * sMinv) = minv := hg₂.hdr.hminv
  simp only [seqs]
  -- 1, 0 and `w`.
  refine WP.seq (WP.mono (WP.keep [.x9, .x12, .x13] (Q := fun t => t.gpr .x9 = BitVec.ofNat 64 1 ∧
      t.gpr .x13 = BitVec.ofNat 64 0 ∧ t.gpr .x12 = BitVec.ofNat 64 w ∧ t.mem = t₂.mem) (by
    brun [hw₂.x0, hdr_enc (show sW < 32 by decide), hw₂.scr.ld (d := 8 * sW) (by simp only [sW]; omega), hw₂.hw])
    (by decide) (by decide) (by decide +kernel)) fun t₃ ⟨⟨h9, h13, h12₃, m₃⟩, k₃⟩ => ?_)
  have hw₃ : Ws t₃ B Z w := hw₂.congrG (js := []) (hs := []) (by rw [m₃]; exact Frm.refl _ _ _) (by simp) k₃
    (by decide)
  have hH₃ : Hdr t₃.mem B w minv := ⟨hw₃.hw, by rw [m₃]; exact hmv₂, fun j hj => hw₃.harr j hj⟩
  refine WP.seq (WP.mono (setWord_ok hw₃.scr hw₃.x0 hH₃ hg.2 h12₃ (by omega) (o := aOne) (by decide) (i := 0)
    (by omega) h13) fun t₄ ⟨hv₄, o₄, k₄⟩ => ?_)
  rw [h9, BitVec.toNat_ofNat] at hv₄
  have hf₄ : Frm B (rg w [aOne] []) t₃.mem t₄.mem := Frm.rg_of_out o₄ (Nat.le_refl _) _ _ (by decide)
  have hw₄ : Ws t₄ B Z w := hw₃.congrG hf₄ (by simp) k₄ (by decide)
  have hg₄ := hw₄.good
  have hmv₄ : word t₄.mem B (8 * sMinv) = minv := by
    rw [hf₄.rg_word (by decide) (by simp), m₃, hmv₂]
  rw [hmv₄] at hg₄
  have hN₄ : wv t₄.mem B (slot w aN) w = N := by
    rw [hf₄.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega), m₃, hN₂]
  have hi₄ : ((word t₄.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [hf₄.rg_word0 hZ16 (by simp) (by decide) (by decide), m₃]; exact hi₂
  have hR2₄ : wv t₄.mem B (slot w aR2) w = wv t₂.mem B (slot w aR2) w := by
    rw [hf₄.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega), m₃]
  simp only [Nat.mul_zero, Nat.pow_zero, Nat.mul_one] at hv₄
  -- `Y = R mod n`.
  refine WP.seq (WP.mono (M.mm_ok hg₄.1 hg₄.2 hw1 (by omega) (o := aY) (a := aR2) (b := aOne) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hi₄
    (by rw [hv₄, hN₄]; omega)) fun t₅ ⟨hg₅, hlt₅, hc₅, ha₅, k₅⟩ => ?_)
  rw [hN₄] at hlt₅
  rw [hN₄, hR2₄, hv₄] at hc₅
  have hY₅ : wv t₅.mem B (slot w aY) w = 2 ^ (64 * w) % N := VG.Proof.Rsa.r_one hR hlt₅ hc (by simpa using hc₅)
  have hf₅ : Frm B (rg w [aAcc, aTmp, aY] []) t₄.mem t₅.mem := Frm.rg_of_arrays ha₅ _ _ (by decide)
  have hw₅ : Ws t₅ B Z w := hw₄.congrG hf₅ (by simp) k₅ (by decide)
  -- `R mod n` into its array.
  refine WP.seq (WP.mono (copyA_ok hw₅ (o := aO) (a := aY) (by decide) (by decide) (by decide))
    fun t₆ ⟨hv₆, o₆, _, _, k₆⟩ => ?_)
  have hf₆ : Frm B (rg w [aO] []) t₅.mem t₆.mem := Frm.rg_of_out o₆ (by omega) _ _ (by decide)
  have hw₆ : Ws t₆ B Z w := hw₅.congrG hf₆ (by simp) k₆ (by decide)
  rw [hY₅] at hv₆
  -- `n - R mod n`.
  refine WP.seq (WP.mono (subSet_ok hw₆ aN aO aNg) fun t₇ ⟨⟨h16₇, h17₇, h13₇, h14₇, _, _, hc₇, m₇⟩, k₇⟩ => ?_)
  have hs₇ := hw₆.scr.congr k₇.wr
  refine WP.mono (subLoop_ok hs₇ h16₇ h17₇ h13₇ h14₇ hc₇ (by omega) (by omega)
    (by have := hw₆.sl (j := aN) (by decide); omega) (by have := hw₆.sl (j := aO) (by decide); omega)
    (by have := hw₆.sl (j := aNg) (by decide); omega)
    (by have := slot_sep (w := w) (show aNg ≠ aN by decide); omega)
    (by have := slot_sep (w := w) (show aNg ≠ aO by decide); omega))
    fun t ⟨hv, o₈, k₈⟩ => ?_
  have hf₈ : Frm B (rg w [aNg] []) t₆.mem t.mem := by
    rw [← m₇]; exact Frm.rg_of_out o₈ (by omega) _ _ (by decide)
  have k68 := k₇.trans k₈
  have hw₈ : Ws t B Z w := hw₆.congrG hf₈ (by simp) k68 (by decide)
  -- The values, through the later pieces.
  have hO₇ : wv t₆.mem B (slot w aO) w = 2 ^ (64 * w) % N := hv₆
  have hN₆ : wv t₆.mem B (slot w aN) w = N := by
    rw [hf₆.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega),
      hf₅.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega), hN₄]
  rw [m₇, hO₇, hN₆] at hv
  have hRN : 2 ^ (64 * w) % N < N := Nat.mod_lt _ (by omega)
  have hc0 : (!t.c).toNat = 0 := by
    cases hb : (!t.c)
    · rfl
    · have := wv_lt t.mem B (slot w aNg) w
      have hNR : N < 2 ^ (64 * w) := hn ▸ wv_lt _ _ _ _
      rw [hb] at hv
      simp only [Bool.toNat_true, Nat.mul_one] at hv
      omega
  rw [hc0, Nat.mul_zero, Nat.add_zero] at hv
  have hR2₆ : wv t₆.mem B (slot w aR2) w = wv t₂.mem B (slot w aR2) w := by
    rw [hf₆.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega),
      hf₅.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega), hR2₄]
  have hOne₆ : wv t₆.mem B (slot w aOne) w = 1 := by
    rw [hf₆.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega),
      hf₅.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega), hv₄]
  refine ⟨hw₈, ?_, ?_, ?_, ?_, by omega, ?_,
    ((((((k₂.trans k₃).trans k₄).trans k₅).trans k₆).trans k68).mono (by decide))⟩
  · rw [hf₈.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega), hR2₆]; exact hlt
  · rw [hf₈.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega), hR2₆]; exact hc
  · rw [hf₈.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega), hOne₆]
  · rw [hf₈.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega), hO₇]
  · have hf₄s : Frm B (rg w [aOne] []) t₂.mem t₄.mem := by rw [← m₃]; exact hf₄
    have := ((hf₂'.rg_trans hf₄s).rg_trans hf₅).rg_trans hf₆
    exact (this.rg_trans hf₈).rg_mono (by decide) (by decide)

end VG.Proof.Rsa.AArch64
