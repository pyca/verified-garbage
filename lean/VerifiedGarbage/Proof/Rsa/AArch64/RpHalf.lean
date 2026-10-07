import VerifiedGarbage.Proof.Rsa.AArch64.RpSkip
import VerifiedGarbage.Proof.Rsa.RecoverMath

/-!
# `vg_rsa_recover_primes` on AArch64: `m = 2^t r`

`halving`: `64 Bw` times, `m := m / 2` and `t += 1` if `m` is even
(`halfStep_ok`), which leaves `r` in `M`'s arrays and `t` in `sT`
(`halving_ok`).
-/

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.Recover
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Spec.Rsa (splitTwos)

/-- The words of a number above its value's `n` words are zero. -/
theorem word_above_zero {mm : Mem} {B : Addr} {e n L : Nat} (hnL : n < L) (h : wv mm B e L < 2 ^ (64 * n)) :
    word mm B (e + 8 * n) = 0 := by
  have e1 := wv_add mm B e n (L - n)
  rw [show n + (L - n) = L by omega] at e1
  have hlow := wv_low_of_lt (m := mm) (B := B) (e := e) (Nat.le_of_lt hnL) h
  have hU : wv mm B (e + 8 * n) (L - n) = 0 := by
    rcases Nat.eq_zero_or_pos (wv mm B (e + 8 * n) (L - n)) with h0 | h0
    · exact h0
    · exfalso
      have : 2 ^ (64 * n) ≤ 2 ^ (64 * n) * wv mm B (e + 8 * n) (L - n) := Nat.le_mul_of_pos_right _ h0
      omega
  have := (wv_eq_zero_iff mm B (e + 8 * n) (L - n)).mp hU 0 (by omega)
  simpa using this

/-- `t - mask c`: `t + 1` if `c`. -/
theorem ofNat_sub_mask (c : Bool) {a : Nat} (_ha : a + 1 < 2 ^ 64) :
    BitVec.ofNat 64 a - mask c = BitVec.ofNat 64 (a + if c then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  cases c
  · simp [mask_false]
  · rw [show mask true = BitVec.allOnes 64 from rfl, BitVec.toNat_sub, BitVec.toNat_allOnes, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat]
    simp only [ite_true]
    omega

/-- The registers a halving writes. -/
def halfRegs : List Reg := [.x3, .x4, .x6, .x11, .x12, .x14, .x15, .x16, .x17]

/-- After `j` halvings of `m`, from `s₁`. -/
structure HalfInv (s₁ : State) (B : Addr) (Z w m : Nat) (j : Nat) (t : State) : Prop where
  ws : Ws t B Z w
  keep : Keep halfRegs s₁ t
  frm : Frm B [(slot w aM, 16 * (w + 2)), (slot w aH, 16 * (w + 2)), (8 * sT, 8)] s₁.mem t.mem
  val : wv t.mem B (slot w aM) (2 * (w + 2)) = (halveStep^[j] (m, 0)).1
  tv : word t.mem B (8 * sT) = BitVec.ofNat 64 (halveStep^[j] (m, 0)).2

theorem slot_aH (w : Nat) : slot w aH = slot w aM + 32 * (w + 2) := by
  simp only [slot, hdrBytes, aH, aM]; omega

theorem half_rmut (w : Nat) : ∀ r ∈ [(slot w aM, 16 * (w + 2)), (slot w aH, 16 * (w + 2)), (8 * sT, 8)], RMut r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact RMut.ofSlot _ _ _
  · exact RMut.ofSlot _ _ _
  · exact RMut.hdr (by decide)

/-- `ws`, `bw` and two bases. -/
theorem wsBw2_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {el : Nat}
    (hel : word s.mem B (8 * Public.sElen) = BitVec.ofNat 64 el) (hel' : el < 2 ^ 32) (i j : Nat) :
    WP isa (.block (ws ++ bw ++ base i .x16 ++ base j .x17)) s fun t =>
      (t.gpr .x16 = off B (slot w i) ∧ t.gpr .x17 = off B (slot w j) ∧
        t.gpr .x14 = BitVec.ofNat 64 (w + (el + 7) / 8) ∧ t.gpr .x12 = BitVec.ofNat 64 w ∧
        t.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2)) ∧ t.mem = s.mem) ∧ Keep [.x3, .x11, .x12, .x14, .x16, .x17] s t := by
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono h.ws_ok fun t₁ ⟨⟨h12, h11, m₁, _⟩, k₁⟩ => ?_
  have h0₁ : t₁.gpr .x0 = B := (k₁.gpr .x0 (by decide)).trans h.x0
  rw [WP.block_append_iff]
  refine WP.mono (bw_ok (h.scr.congr k₁.wr) h0₁ h.h256 (by rw [m₁]; exact hel) hel' h12) fun t₂ ⟨⟨h14, m₂, _⟩, k₂⟩ => ?_
  refine WP.mono (base2_ok i j .x16 .x17 ((k₂.gpr .x0 (by decide)).trans h0₁) ((k₂.gpr .x11 (by decide)).trans h11))
    fun t ⟨⟨h16, h17, m₃, _⟩, k₃⟩ => ⟨⟨h16, h17, (k₃.gpr .x14 (by decide)).trans h14,
      (k₃.gpr .x12 (by decide)).trans ((k₂.gpr .x12 (by decide)).trans h12),
      (k₃.gpr .x11 (by decide)).trans ((k₂.gpr .x11 (by decide)).trans h11), by rw [m₃, m₂, m₁]⟩,
      ((k₁.trans k₂).trans k₃).mono (by decide)⟩

/-- A halving. -/
theorem halfStep_ok {s₁ t : State} {B : Addr} {Z w m el j : Nat} (hI : HalfInv s₁ B Z w m j t)
    (hel : word s₁.mem B (8 * Public.sElen) = BitVec.ofNat 64 el) (he1 : 1 ≤ el)
    (he2 : el ≤ 8 * w) (hm : m < 2 ^ (64 * (w + (el + 7) / 8))) (hj : j < 64 * (w + (el + 7) / 8)) :
    WP isa (seqs (halfShift ++ [VG.Impl.Rsa.AArch64.Crt.selLoop, .block [.subImm .x .x6 .x6 1]])) t fun t' =>
      HalfInv s₁ B Z w m (j + 1) t' ∧ t'.gpr .x6 = t.gpr .x6 - BitVec.ofNat 64 1 := by
  have h := hI.ws
  have hn := h.scr.nowrap
  have hw1 := h.w1
  have hw2 := h.w2
  have hZ := h.hZ
  have h256 := h.h256
  have sH := slot_lt (w := w) (show aH + 1 < 16 by decide)
  have eHM := slot_aH w
  have eH1 : slot w (aH + 1) = slot w aH + 8 * (w + 2) := by simp only [slot, hdrBytes, aH]; omega
  have hT0 := hdr_lt_slot w aM (show sT < 32 by decide)
  have eT : 8 * sT = 216 := rfl
  have eE : 8 * Public.sElen = 160 := rfl
  -- The header's `e_len`.
  have hel₀ : word t.mem B (8 * Public.sElen) = BitVec.ofNat 64 el := by
    rw [hI.frm.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> dsimp only <;> omega) (by omega)]
    exact hel
  obtain ⟨Bw, hBw⟩ : ∃ Bw, w + (el + 7) / 8 = Bw := ⟨_, rfl⟩
  rw [hBw] at hm hj
  have hBw2 : Bw + 1 ≤ 2 * (w + 2) := by omega
  -- `m`'s current value and its words.
  have hmj : (halveStep^[j] (m, 0)).1 < 2 ^ (64 * Bw) := Nat.lt_of_le_of_lt (halve_le m j) hm
  have hlow : wv t.mem B (slot w aM) Bw = (halveStep^[j] (m, 0)).1 := by
    rw [wv_low_of_lt (v := Bw) (w := 2 * (w + 2)) (by omega) (by rw [hI.val]; exact hmj), hI.val]
  have htop : word t.mem B (slot w aM + 8 * Bw) = 0 := word_above_zero (L := 2 * (w + 2)) (by omega)
    (by rw [hI.val]; exact hmj)
  have hpar : (word t.mem B (slot w aM)).toNat % 2 = (halveStep^[j] (m, 0)).1 % 2 := by
    rw [← hlow, wv_low (show 1 ≤ Bw by omega)]; omega
  have htj : (halveStep^[j] (m, 0)).2 < 2 ^ 63 := by
    have : ∀ i, (halveStep^[i] (m, 0)).2 ≤ i := by
      intro i
      induction i with
      | zero => exact Nat.le_refl _
      | succ i ih =>
        rw [Function.iterate_succ_apply']
        generalize halveStep^[i] (m, 0) = st at ih ⊢
        unfold halveStep
        split <;> (try simp only) <;> omega
    have := this j
    omega
  simp only [halfShift, List.cons_append, List.nil_append, seqs]
  -- `[aH] := m / 2`.
  refine WP.seq (WP.mono (wsBw2_ok h hel₀ (by omega) aM aH) fun t₁ ⟨⟨h16, h17, h14, _, _, m₁⟩, k₁⟩ => ?_)
  rw [hBw] at h14
  have hs₁ := h.scr.congr k₁.wr
  refine WP.seq (WP.mono (shr_ok hs₁ h16 h17 h14 (by omega) (by omega) (by omega) (by omega) (Or.inr (Or.inl (by omega))))
    fun t₂ ⟨hv₂, _, o₂, k₂⟩ => ?_)
  rw [m₁, htop] at hv₂
  have h₂ : Ws t₂ B Z w := h.congrR (rs := [(slot w aH, 8 * Bw)]) (fun x hx => by
    rw [o₂ x (hx _ (List.mem_singleton_self _)), m₁]) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact RMut.ofSlot _ _ _) (k₁.trans k₂) (by decide)
  have hel₂ : word t₂.mem B (8 * Public.sElen) = BitVec.ofNat 64 el := by
    rw [o₂.word (Or.inl (by omega)) (by omega), m₁, hel₀]
  have hM₂ : word t₂.mem B (slot w aM) = word t.mem B (slot w aM) := by
    rw [o₂.word (Or.inl (by omega)) (by omega), m₁]
  have hT₂ : word t₂.mem B (8 * sT) = BitVec.ofNat 64 (halveStep^[j] (m, 0)).2 := by
    rw [o₂.word (Or.inl (by omega)) (by omega), m₁, hI.tv]
  -- The mask of `m` even, and `t`.
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (wsBw2_ok h₂ hel₂ (by omega) aH aM)
    fun t₃ ⟨⟨h16₃, h17₃, h14₃, _, _, m₃⟩, k₃⟩ => ?_))
  rw [hBw] at h14₃
  have hs₃ := h₂.scr.congr k₃.wr
  have h0₃ : t₃.gpr .x0 = B := (k₃.gpr .x0 (by decide)).trans h₂.x0
  refine WP.mono (WP.keep [.x3, .x4, .x15] (Q := fun u => u.gpr .x15 = mask (decide ((word t.mem B
      (slot w aM)).toNat % 2 = 0)) ∧ u.mem = t₃.mem.writeW (off B (8 * sT))
        (BitVec.ofNat 64 (halveStep^[j] (m, 0)).2 - mask (decide ((word t.mem B (slot w aM)).toNat % 2 = 0))))
    (by
      brun [h16₃, h17₃, h14₃, h0₃, hdr_enc (show sT < 32 by decide), hs₃.ld (d := slot w aM) (by omega),
        hs₃.ld (d := 8 * sT) (by omega), hs₃.st (d := 8 * sT) (by omega), m₃, hM₂, hT₂, low_sub_one])
    (by decide) (by decide) (by decide +kernel)) fun t₄ ⟨⟨h15, m₄⟩, k₄⟩ => ?_
  rw [ofNat_sub_mask _ (by omega)] at m₄
  simp only [decide_eq_true_eq] at m₄
  have hs₄ := hs₃.congr k₄.wr
  have o₄ := writeW_outside t₃.mem B (BitVec.ofNat 64 ((halveStep^[j] (m, 0)).2 +
    if (word t.mem B (slot w aM)).toNat % 2 = 0 then 1 else 0)) (d := 8 * sT) (by omega)
  rw [← m₄] at o₄
  -- `m := m / 2` if it was even.
  refine WP.seq (WP.mono (selLoop_ok hs₄ ((k₄.gpr .x16 (by decide)).trans h16₃) ((k₄.gpr .x17 (by decide)).trans h17₃)
    ((k₄.gpr .x14 (by decide)).trans h14₃) h15 (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega)))
    fun t₅ ⟨hv₅, o₅, k₅⟩ => ?_)
  refine WP.mono (dec_ok t₅ .x6) fun t' ⟨⟨h6, m₆, _⟩, k₆⟩ => ⟨?_, by
    rw [h6, (k₅.gpr .x6 (by decide)), (k₄.gpr .x6 (by decide)), (k₃.gpr .x6 (by decide)), (k₂.gpr .x6 (by decide)),
      (k₁.gpr .x6 (by decide))]⟩
  have hf : Frm B [(slot w aM, 16 * (w + 2)), (slot w aH, 16 * (w + 2)), (8 * sT, 8)] t.mem t'.mem := by
    intro x hx
    have a := hx _ (List.mem_cons_self)
    have b := hx _ (List.mem_cons_of_mem _ List.mem_cons_self)
    have c := hx _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    dsimp only at a b c
    rw [m₆, o₅ x (by omega), o₄ x c, m₃, o₂ x (by omega), m₁]
  have k06 := (((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k₆)
  refine ⟨h.congrR hf (half_rmut w) k06 (by decide), (hI.keep.trans k06).mono (by decide), hI.frm.trans hf, ?_, ?_⟩
  · -- `m`.
    have hfull : ∀ mm : Mem, wv mm B (slot w aM) (2 * (w + 2)) =
        wv mm B (slot w aM) Bw + 2 ^ (64 * Bw) * wv mm B (slot w aM + 8 * Bw) (2 * (w + 2) - Bw) := fun mm => by
      rw [← wv_add, show Bw + (2 * (w + 2) - Bw) = 2 * (w + 2) by omega]
    have hU : wv t'.mem B (slot w aM + 8 * Bw) (2 * (w + 2) - Bw) =
        wv t.mem B (slot w aM + 8 * Bw) (2 * (w + 2) - Bw) := by
      rw [m₆, o₅.wv (Or.inr (by omega)) (by omega), o₄.wv (Or.inr (by omega)) (by omega), m₃,
        o₂.wv (Or.inl (by omega)) (by omega), m₁]
    have hU0 : wv t.mem B (slot w aM + 8 * Bw) (2 * (w + 2) - Bw) = 0 := by
      have := hfull t.mem
      rw [hI.val, hlow] at this
      have := Nat.mul_eq_zero.mp (show 2 ^ (64 * Bw) * wv t.mem B (slot w aM + 8 * Bw) (2 * (w + 2) - Bw) = 0 by omega)
      exact this.resolve_left (Nat.ne_of_gt (Nat.pow_pos (by decide)))
    have hH₄ : wv t₄.mem B (slot w aH) Bw = wv t₂.mem B (slot w aH) Bw := by
      rw [o₄.wv (Or.inr (by omega)) (by omega), m₃]
    have hM₄ : wv t₄.mem B (slot w aM) Bw = wv t.mem B (slot w aM) Bw := by
      rw [o₄.wv (Or.inr (by omega)) (by omega), m₃, o₂.wv (Or.inl (by omega)) (by omega), m₁]
    rw [hfull, hU, hU0, Nat.mul_zero, Nat.add_zero, m₆, hv₅, hH₄, hM₄, hlow, Function.iterate_succ_apply']
    rw [hpar, hlow] at hv₂
    rw [show BitVec.toNat (0 : BitVec 64) = 0 from rfl, Nat.zero_mod, Nat.mul_zero, Nat.add_zero] at hv₂
    rw [hpar]
    generalize hst : halveStep^[j] (m, 0) = st at hv₂ hpar ⊢
    rcases st with ⟨mj, tj⟩
    dsimp only at hv₂ hpar ⊢
    unfold halveStep
    rcases Nat.mod_two_eq_zero_or_one mj with he | ho
    · simp [he]; omega
    · simp [ho]
  · -- `t`.
    rw [m₆, o₅.word (Or.inl (by omega)) (by omega), m₄, word_writeW_self, Function.iterate_succ_apply', hpar]
    generalize halveStep^[j] (m, 0) = st
    rcases st with ⟨mj, tj⟩
    unfold halveStep
    rcases Nat.mod_two_eq_zero_or_one mj with he | ho
    · simp [he]
    · simp [ho]

/-- `halfInit`: `x6 := 64 Bw` and `t := 0`. -/
theorem halfInit_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {el : Nat}
    (hel : word s.mem B (8 * Public.sElen) = BitVec.ofNat 64 el) (hel' : el < 2 ^ 32) :
    WP isa (.block halfInit) s fun t =>
      t.gpr .x6 = BitVec.ofNat 64 (64 * (w + (el + 7) / 8)) ∧
      t.mem = s.mem.writeW (off B (8 * sT)) (BitVec.ofNat 64 0) ∧ Keep [.x3, .x6, .x11, .x12, .x14] s t := by
  have hn := h.scr.nowrap
  have h256 := h.h256
  have hw2 := h.w2
  unfold halfInit
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono h.ws_ok fun t₁ ⟨⟨h12, _, m₁, _⟩, k₁⟩ => ?_
  have h0₁ : t₁.gpr .x0 = B := (k₁.gpr .x0 (by decide)).trans h.x0
  rw [WP.block_append_iff]
  refine WP.mono (bw_ok (h.scr.congr k₁.wr) h0₁ h256 (by rw [m₁]; exact hel) hel' h12) fun t₂ ⟨⟨h14, m₂, _⟩, k₂⟩ => ?_
  have h0₂ : t₂.gpr .x0 = B := (k₂.gpr .x0 (by decide)).trans h0₁
  refine WP.mono (WP.keep [.x3, .x6] (Q := fun t => t.gpr .x6 = BitVec.ofNat 64 (64 * (w + (el + 7) / 8)) ∧
      t.mem = s.mem.writeW (off B (8 * sT)) (BitVec.ofNat 64 0)) (by
    brun [h14, h0₂, hdr_enc (show sT < 32 by decide), (h.scr.congr (k₁.trans k₂).wr).st (d := 8 * sT) (by
      simp only [sT, sFn]; omega), m₂, m₁, shl_ofNat (show (w + (el + 7) / 8) * 2 ^ 6 < 2 ^ 64 by omega)]
    constructor
    · congr 1; omega
    · rfl) (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨h6, mt⟩, k₃⟩ => ⟨h6, mt, ((k₁.trans k₂).trans k₃).mono (by decide)⟩

/-- `halving`: `m = 2^t r` with `r` odd, for `0 < m < 2^(64 Bw)` in `M`. -/
theorem halving_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {el m : Nat}
    (hel : word s.mem B (8 * Public.sElen) = BitVec.ofNat 64 el) (he1 : 1 ≤ el)
    (he2 : el ≤ 8 * w) (hv : wv s.mem B (slot w aM) (2 * (w + 2)) = m) (hm0 : 0 < m)
    (hm : m < 2 ^ (64 * (w + (el + 7) / 8))) :
    WP isa halving s fun t => Ws t B Z w ∧
      wv t.mem B (slot w aM) (2 * (w + 2)) = (splitTwos m).2 ∧
      word t.mem B (8 * sT) = BitVec.ofNat 64 (splitTwos m).1 ∧
      Frm B [(slot w aM, 16 * (w + 2)), (slot w aH, 16 * (w + 2)), (8 * sT, 8)] s.mem t.mem ∧
      Keep halfRegs s t := by
  have hn := h.scr.nowrap
  have h256 := h.h256
  have hw2 := h.w2
  have hT0 := hdr_lt_slot w aM (show sT < 32 by decide)
  have eT : 8 * sT = 216 := rfl
  have eE : 8 * Public.sElen = 160 := rfl
  unfold halving
  refine WP.seq (WP.mono (halfInit_ok h hel (by omega)) fun s₁ ⟨h6, m₁, k₁⟩ => ?_)
  have hZ := h.hZ
  have o₁ := writeW_outside s.mem B (BitVec.ofNat 64 0) (d := 8 * sT) (by omega)
  rw [← m₁] at o₁
  have hf₁ : Frm B [(slot w aM, 16 * (w + 2)), (slot w aH, 16 * (w + 2)), (8 * sT, 8)] s.mem s₁.mem :=
    fun x hx => o₁ x (hx _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  have h₁ := h.congrR hf₁ (half_rmut w) k₁ (by decide)
  have hel₁ : word s₁.mem B (8 * Public.sElen) = BitVec.ofNat 64 el := by
    rw [o₁.word (Or.inl (by omega)) (by omega)]; exact hel
  have sM := slot_lt (w := w) (show aM + 1 < 16 by decide)
  have eM1 := slot_aM1 w
  refine WP.mono (wp_countdown (N := 64 * (w + (el + 7) / 8)) (by omega) (by omega) (HalfInv s₁ B Z w m)
    (fun j hj t hI _ => halfStep_ok hI hel₁ he1 he2 hm hj)
    ⟨h₁, Keep.refl _ _, Frm.refl _ _ _, by rw [o₁.wv (Or.inr (by omega)) (by omega), hv]; rfl,
      by rw [m₁, word_writeW_self]; rfl⟩ h6) fun t hI => ?_
  have hd := halve_done hm0 hm
  have hval := hI.val
  have htv := hI.tv
  rw [hd] at hval htv
  exact ⟨hI.ws, hval, htv, hf₁.trans hI.frm, (k₁.trans hI.keep).mono (by decide)⟩

end VG.Proof.Rsa.AArch64
