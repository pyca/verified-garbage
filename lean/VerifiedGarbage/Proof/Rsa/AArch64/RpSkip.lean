import VerifiedGarbage.Proof.Rsa.AArch64.RpProd
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks

/-!
# `vg_rsa_recover_primes` on AArch64: whether `d e - 1` is even and positive

`skipBlk` takes the mask of `M = d e` even and clears `M`'s low bit (`m =
M - 1` for an odd `M`); `orLoop` tests `m = 0`, and `skipTest` sets `x10` to
zero iff neither (`skip_ok`).
-/

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.Recover
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- A word's low bit, as a word. -/
theorem and_one (x : BitVec 64) : x &&& BitVec.setWidth 64 1#16 = BitVec.ofNat 64 (x.toNat % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (BitVec.setWidth 64 1#16).toNat = 1 from rfl, Nat.and_one_is_mod, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show x.toNat % 2 < 2 ^ 64 by omega)]

/-- The mask of an even word, from its low bit. -/
theorem low_sub_one (x : BitVec 64) :
    (x &&& BitVec.setWidth 64 1#16) - BitVec.ofNat 64 1 = mask (decide (x.toNat % 2 = 0)) := by
  rw [and_one]
  rcases Nat.mod_two_eq_zero_or_one x.toNat with h | h <;> rw [h] <;> decide

/-- A word minus its low bit. -/
theorem sub_low (x : BitVec 64) : (x - (x &&& BitVec.setWidth 64 1#16)).toNat = x.toNat - x.toNat % 2 := by
  rw [and_one, BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega)]

/-- `Bw = w + ⌈e_len / 8⌉`, as `bw` computes it. -/
theorem bw_val (w el : Nat) (hel : el < 2 ^ 32) :
    (BitVec.ofNat 64 el + 7#64) >>> 3 + BitVec.ofNat 64 w =
      BitVec.ofNat 64 (w + (el + 7) / 8) := by
  rw [shr3_w el hel, BitVec.ofNat_add_ofNat, Nat.add_comm]

/-- `zeroMask`: `x15` the mask of `x9 = 0`, and `x7 = 0`. -/
theorem zeroMask_ok (s : State) :
    WP isa (.block zeroMask) s fun t =>
      (t.gpr .x15 = mask (decide (s.gpr .x9 = 0)) ∧ t.gpr .x7 = 0 ∧ t.mem = s.mem) ∧ Keep [.x3, .x4, .x7, .x15] s t :=
  WP.keep [.x3, .x4, .x7, .x15] (by brun [zeroMask, borrowMask, csel_mask', subs_one_c, Bool.not_not])
    (by decide) (by decide) (by decide +kernel)

/-- `bw`. -/
theorem bw_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (h256 : 8 * 32 ≤ Z) {el : Nat}
    (hel : word s.mem B (8 * Public.sElen) = BitVec.ofNat 64 el) (hel' : el < 2 ^ 32)
    (h12 : s.gpr .x12 = BitVec.ofNat 64 w) :
    WP isa (.block bw) s fun t =>
      (t.gpr .x14 = BitVec.ofNat 64 (w + (el + 7) / 8) ∧ t.mem = s.mem ∧ t.c = s.c) ∧ Keep [.x3, .x14] s t :=
  have hn := hs.nowrap
  WP.keep [.x3, .x14] (by
    brun [bw, h0, h12, hdr_enc (show Public.sElen < 32 by decide), hs.ld (d := 8 * Public.sElen) (by
      simp only [Public.sElen, sFn]; omega), hel, bw_val w el hel']) (by decide) (by decide) (by decide +kernel)

/-- `skipBlk`. -/
theorem skipBlk_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {el : Nat}
    (hel : word s.mem B (8 * Public.sElen) = BitVec.ofNat 64 el) (hel' : el < 2 ^ 32) :
    WP isa (.block skipBlk) s fun t =>
      t.gpr .x16 = off B (slot w aM) ∧ t.gpr .x9 = 0 ∧ t.gpr .x14 = BitVec.ofNat 64 (w + (el + 7) / 8) ∧
      t.gpr .x0 = B ∧
      t.mem = (s.mem.writeW (off B (slot w aM)) (word s.mem B (slot w aM) -
          (word s.mem B (slot w aM) &&& BitVec.setWidth 64 1#16))).writeW
        (off B (8 * sC2)) (mask (decide ((word s.mem B (slot w aM)).toNat % 2 = 0))) ∧
      Keep [.x11, .x12, .x16, .x3, .x4, .x5, .x9, .x14] s t := by
  have hn := h.scr.nowrap
  have h256 := h.h256
  have sM := h.sl (j := aM) (by decide)
  have hM0 := hdr_lt_slot w aM (show sC2 < 32 by decide)
  unfold skipBlk
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono h.ws_ok fun t₁ ⟨⟨h12, h11, m₁, _⟩, k₁⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (base_ok aM .x16 ((k₁.gpr .x0 (by decide)).trans h.x0) h11) fun t₂ ⟨⟨h16, m₂, _⟩, k₂⟩ => ?_
  have k12 := k₁.trans k₂
  have hs₂ := h.scr.congr k12.wr
  have h0₂ : t₂.gpr .x0 = B := (k12.gpr .x0 (by decide)).trans h.x0
  have h12₂ : t₂.gpr .x12 = BitVec.ofNat 64 w := (k₂.gpr .x12 (by decide)).trans h12
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x4, .x5, .x9] (Q := fun t => t.gpr .x9 = 0 ∧ t.gpr .x16 = off B (slot w aM) ∧
    t.gpr .x12 = BitVec.ofNat 64 w ∧ t.gpr .x0 = B ∧
    t.mem = (t₂.mem.writeW (off B (slot w aM)) (word t₂.mem B (slot w aM) -
        (word t₂.mem B (slot w aM) &&& BitVec.setWidth 64 1#16))).writeW
      (off B (8 * sC2)) (mask (decide ((word t₂.mem B (slot w aM)).toNat % 2 = 0)))) (by
      brun [h16, h0₂, h12₂, hdr_enc (show sC2 < 32 by decide), hs₂.ld (d := slot w aM) (by omega),
        hs₂.st (d := slot w aM) (by omega), hs₂.st (d := 8 * sC2) (by omega), low_sub_one]) (by decide) (by decide) (by decide +kernel)) fun t₃ ⟨⟨h9, h16₃, h12₃, h0₃, m₃⟩, k₃⟩ => ?_
  have hel₃ : word t₃.mem B (8 * Public.sElen) = BitVec.ofNat 64 el := by
    have e1 : 8 * Public.sElen = 160 := rfl
    have e2 : 8 * sC2 = 240 := rfl
    rw [m₃, (writeW_outside _ B _ (d := 8 * sC2) (by omega)).word (by omega) (by omega),
      (writeW_outside _ B _ (d := slot w aM) (by omega)).word (by
        have := hdr_lt_slot w aM (show Public.sElen < 32 by decide); omega) (by omega), m₂, m₁]
    exact hel
  refine WP.mono (bw_ok (h.scr.congr (k12.trans k₃).wr) h0₃ h256 hel₃ hel' h12₃) fun t ⟨⟨h14, mt, _⟩, k₄⟩ =>
    ⟨(k₄.gpr .x16 (by decide)).trans h16₃, (k₄.gpr .x9 (by decide)).trans h9, h14, (k₄.gpr .x0 (by decide)).trans h0₃,
      by rw [mt, m₃, m₂, m₁], ((k12.trans k₃).trans k₄).mono (by decide)⟩

/-- The loop of `orLoop`: `x9 = 0` iff the `N` words at `x16` are. -/
theorem orLoop_ok {s : State} {B : Addr} {Z N e : Nat} (hs : Scr s B Z) (h16 : s.gpr .x16 = off B e)
    (h14 : s.gpr .x14 = BitVec.ofNat 64 N) (h9 : s.gpr .x9 = 0) (hN1 : 1 ≤ N) (hN : N < 2 ^ 31)
    (he : e + 8 * N ≤ Z) :
    WP isa orLoop s fun t =>
      (t.gpr .x9 = 0 ↔ wv s.mem B e N = 0) ∧ t.mem = s.mem ∧ Keep [.x3, .x4, .x9, .x14, .x16, .x17] s t := by
  unfold orLoop countLoop
  refine WP.mono (wp_countdown (N := N) (by omega) (by omega)
    (fun j t => OrInv s B Z (fun j => True ∧ ∀ i < j, word s.mem B (e + 8 * i) = 0) j t ∧
      t.gpr .x16 = off B (e + 8 * j))
    (fun j hj t hI _ => orStep_ok he hj hI.1 hI.2)
    ⟨⟨hs, Keep.refl _ _, rfl, by
      rw [h9]; exact ⟨fun _ => ⟨trivial, fun i hi => absurd hi (Nat.not_lt_zero _)⟩, fun _ => rfl⟩⟩,
      by rw [h16]; rfl⟩ h14) fun t ⟨hI, _⟩ => ⟨?_, hI.mem, hI.keep⟩
  rw [hI.val, wv_eq_zero_iff]
  exact ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩

/-- `skipTest`: `x10 = 0` iff `m ≠ 0` and `M` is odd. -/
theorem skipTest_ok {s : State} {B : Addr} {Z : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (hZ : 8 * 32 ≤ Z)
    {z : Prop} [Decidable z] (hz : s.gpr .x9 = 0 ↔ z) {c : Bool} (hm : word s.mem B (8 * sC2) = mask c) :
    WP isa (.block skipTest) s fun t =>
      (t.gpr .x10 = 0 ↔ ¬ z ∧ c = false) ∧ t.mem = s.mem ∧ Keep [.x3, .x4, .x7, .x10, .x15] s t := by
  have hn := hs.nowrap
  have e : decide (s.gpr .x9 = 0) = decide z := by
    by_cases hz' : z
    · rw [decide_eq_true hz', decide_eq_true (hz.mpr hz')]
    · rw [decide_eq_false hz', decide_eq_false (fun h => hz' (hz.mp h))]
  unfold skipTest
  rw [WP.block_append_iff]
  refine WP.mono (zeroMask_ok s) fun t₁ ⟨⟨h15, _, m₁⟩, k₁⟩ => ?_
  have h0₁ : t₁.gpr .x0 = B := (k₁.gpr .x0 (by decide)).trans h0
  refine WP.mono (WP.keep [.x3, .x10] (Q := fun t => t.gpr .x10 = mask (decide z) ||| mask c ∧ t.mem = t₁.mem) (by
    brun [h0₁, h15, e, hdr_enc (show sC2 < 32 by decide), (hs.congr k₁.wr).ld (d := 8 * sC2) (by
      simp only [sC2, sFn]; omega), m₁, hm]) (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨h10, mt⟩, k₂⟩ => ⟨?_, mt.trans m₁, (k₁.trans k₂).mono (by decide)⟩
  rw [h10, mask_or_mask, mask_eq_zero_iff, Bool.or_eq_false_iff, decide_eq_false_iff_not]

/-- `M` with its low bit cleared: `M - M mod 2`. -/
theorem clearLow_wv (m : Mem) (B : Addr) {e n : Nat} (hn : 1 ≤ n) (hen : B.toNat + e + 8 * n ≤ 2 ^ 64) :
    wv (m.writeW (off B e) (word m B e - (word m B e &&& BitVec.setWidth 64 1#16))) B e n = wv m B e n - wv m B e n % 2 := by
  have o := writeW_outside m B (word m B e - (word m B e &&& BitVec.setWidth 64 1#16)) (d := e) (by omega)
  rw [wv_low hn, wv_low (m := m) hn, word_writeW_self, sub_low, o.wv (Or.inr (by omega)) (by omega)]
  have := (word m B e).isLt
  omega

/-- The test of `skip`: `x10 = 0` iff `M` is odd and above 1; then `M`'s
array holds `m = M - 1`. -/
theorem skip_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {el : Nat}
    (hel : word s.mem B (8 * Public.sElen) = BitVec.ofNat 64 el) (he1 : 1 ≤ el) (he2 : el ≤ 8 * w)
    (hM : wv s.mem B (slot w aM) (2 * (w + 2)) < 2 ^ (64 * (w + (el + 7) / 8))) :
    WP isa (seqs [.block skipBlk, orLoop, .block skipTest]) s fun t =>
      (t.gpr .x10 = 0 ↔ wv s.mem B (slot w aM) (2 * (w + 2)) % 2 = 1 ∧ 2 ≤ wv s.mem B (slot w aM) (2 * (w + 2))) ∧
      wv t.mem B (slot w aM) (2 * (w + 2)) =
        wv s.mem B (slot w aM) (2 * (w + 2)) - wv s.mem B (slot w aM) (2 * (w + 2)) % 2 ∧
      Frm B [(slot w aM, 8), (8 * sC2, 8)] s.mem t.mem ∧ t.gpr .x0 = B ∧
      Keep [.x11, .x12, .x16, .x3, .x4, .x5, .x9, .x14, .x7, .x10, .x15, .x17] s t := by
  have hn := h.scr.nowrap
  have h256 := h.h256
  have sM := slot_lt (w := w) (show aM + 1 < 16 by decide)
  have hZ := h.hZ
  have eM1 := slot_aM1 w
  have hM0 := hdr_lt_slot w aM (show sC2 < 32 by decide)
  have hw1 := h.w1
  have hw2 := h.w2
  have sMM : slot w aM + 16 * (w + 2) ≤ Z := by rw [eM1] at sM; omega
  simp only [seqs]
  refine WP.seq (WP.mono (skipBlk_ok h hel (by omega)) fun s₁ ⟨h16, h9, h14, h0, m₁, k₁⟩ => ?_)
  have hs₁ := h.scr.congr k₁.wr
  -- `m` in `M`'s arrays, and `M`'s parity in `sC2`.
  have o₂ := writeW_outside (s.mem.writeW (off B (slot w aM)) (word s.mem B (slot w aM) -
    (word s.mem B (slot w aM) &&& BitVec.setWidth 64 1#16))) B
    (mask (decide ((word s.mem B (slot w aM)).toNat % 2 = 0))) (d := 8 * sC2) (by omega)
  have hm : wv s₁.mem B (slot w aM) (2 * (w + 2)) =
      wv s.mem B (slot w aM) (2 * (w + 2)) - wv s.mem B (slot w aM) (2 * (w + 2)) % 2 := by
    rw [m₁, o₂.wv (Or.inr (by omega)) (by omega), clearLow_wv _ _ (by omega) (by omega)]
  have hpar : (word s.mem B (slot w aM)).toNat % 2 = wv s.mem B (slot w aM) (2 * (w + 2)) % 2 := by
    rw [wv_low (show 1 ≤ 2 * (w + 2) by omega)]; omega
  have hc : word s₁.mem B (8 * sC2) = mask (decide (wv s.mem B (slot w aM) (2 * (w + 2)) % 2 = 0)) := by
    rw [m₁, word_writeW_self, hpar]
  -- `m = 0`.
  refine WP.seq (WP.mono (orLoop_ok hs₁ h16 h14 h9 (by omega) (by omega) (by omega)) fun s₂ ⟨hz, m₂, k₂⟩ => ?_)
  have hlt : wv s₁.mem B (slot w aM) (2 * (w + 2)) < 2 ^ (64 * (w + (el + 7) / 8)) := by rw [hm]; omega
  rw [wv_low_of_lt (by omega) hlt, hm] at hz
  refine WP.mono (skipTest_ok (hs₁.congr k₂.wr) ((k₂.gpr .x0 (by decide)).trans h0) h256 hz
    (c := decide (wv s.mem B (slot w aM) (2 * (w + 2)) % 2 = 0)) (by rw [m₂]; exact hc))
    fun t ⟨h10, mt, k₃⟩ => ⟨?_, by rw [mt, m₂, hm], ?_,
      (k₃.gpr .x0 (by decide)).trans ((k₂.gpr .x0 (by decide)).trans h0), ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  · rw [h10, decide_eq_false_iff_not]
    omega
  · intro x hx
    have a := hx (slot w aM, 8) (by simp)
    have b := hx (8 * sC2, 8) (by simp)
    dsimp only at a b
    rw [mt, m₂, m₁, o₂ x b, writeW_outside s.mem B _ (d := slot w aM) (by omega) x a]

end VG.Proof.Rsa.AArch64
