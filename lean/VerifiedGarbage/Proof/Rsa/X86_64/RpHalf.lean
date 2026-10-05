import VerifiedGarbage.Proof.Rsa.X86_64.RpSkip
import VerifiedGarbage.Proof.Rsa.X86_64.Inv
import VerifiedGarbage.Proof.Rsa.RecoverMath

/-!
# `vg_rsa_recover_primes` on x86-64: `m = 2^t r`

`halving`: `64 Bw` times, `m := m / 2` and `t += 1` if `m` is even
(`halving_ok`), which leaves `r` in `M`'s arrays and `t` in `sT`
(`halve_done`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64
open VG.Spec.Rsa (splitTwos)

/-- `bw`: `Bw` into `rax`. -/
theorem bw_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {el : Nat}
    (hel : word s.mem B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 el) (hel' : el < 2 ^ 32) :
    WP isa (.block bw) s fun t => t.gpr .rax = BitVec.ofNat 64 (w + (el + 7) / 8) ∧ t.mem = s.mem ∧ Keep [.rax] s t := by
  have hn := h.scr.nowrap
  have h256 := h.h256
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => h.scr.ld (by omega)
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 (w + (el + 7) / 8) ∧ t.mem = s.mem)
    (by
      unfold bw
      xrun [State.ea, hdr, h.rdi, hdrOff, hl _ (show sW < 32 by decide),
        hl _ (show Impl.Bignum.X86_64.Public.sElen < 32 by decide), h.hw, hel, bw_val w el hel']) rfl)
    fun t ⟨⟨a, b⟩, k⟩ => ⟨a, b, k⟩

/-- Halving never grows `m`. -/
theorem halve_le (m : Nat) : ∀ j, (halveStep^[j] (m, 0)).1 ≤ m
  | 0 => Nat.le_refl _
  | j + 1 => by
    rw [Function.iterate_succ_apply']
    have := halve_le m j
    generalize halveStep^[j] (m, 0) = st at this ⊢
    unfold halveStep
    split <;> (try simp only) <;> omega

/-- `halfHead`: the bases of `m` and the temporary, `r12 := Bw`, and `rbp`
the mask of `m` odd. -/
theorem halfHead_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {el : Nat}
    (hel : word s.mem B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 el) (hel' : el < 2 ^ 32) :
    WP isa (.block halfHead) s fun t =>
      t.gpr .r8 = off B (slot w aM) ∧ t.gpr .rsi = off B (slot w aH) ∧
      t.gpr .r12 = BitVec.ofNat 64 (w + (el + 7) / 8) ∧
      t.gpr .rbp = mask (decide ((word s.mem B (slot w aM)).toNat % 2 = 1)) ∧ t.gpr .rdi = B ∧ t.mem = s.mem ∧
      Keep [.r12, .r9, .r8, .rsi, .rax, .rbp] s t := by
  have hn := h.scr.nowrap
  have sM := h.sl (j := aM) (by decide)
  unfold halfHead
  rw [List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono h.ws_ok fun t₁ ⟨_, h9, m₁, k₁⟩ => WP.block_append_iff.mpr ?_
  have hdi₁ : t₁.gpr .rdi = B := (k₁.gpr (by decide)).trans h.rdi
  refine WP.mono (base_ok aM (r := .r8) (by decide) hdi₁ h9) fun t₂ ⟨h8, m₂, k₂⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (base_ok aH (r := .rsi) (by decide) ((k₂.gpr (by decide)).trans hdi₁)
    ((k₂.gpr (by decide)).trans h9)) fun t₃ ⟨hsi, m₃, k₃⟩ => WP.block_append_iff.mpr ?_
  have k13 := (k₁.trans k₂).trans k₃
  have hw₃ : Ws t₃ B Z w := h.congr (rs := []) (by rw [m₃, m₂, m₁]; exact Frm.refl _ _ _) (by simp) k13 (by decide)
  refine WP.mono (bw_ok hw₃ (by rw [m₃, m₂, m₁]; exact hel) hel') fun t₄ ⟨hax, m₄, k₄⟩ => ?_
  have hs₄ := h.scr.congr (k13.trans k₄).2.2
  have h8₄ : t₄.gpr .r8 = off B (slot w aM) := (k₄.gpr (by decide)).trans ((k₃.gpr (by decide)).trans h8)
  refine WP.mono (WP.keep [.r12, .rax, .rbp] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 (w + (el + 7) / 8) ∧
      t.gpr .rbp = mask (decide ((word s.mem B (slot w aM)).toNat % 2 = 1)) ∧ t.mem = t₄.mem) (by
    xrun [State.ea, at0, h8₄, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, hax,
      hs₄.ld (d := slot w aM) (by omega), m₄, m₃, m₂, m₁, mask_low]) rfl)
    fun t ⟨⟨h12, hbp, mt⟩, k₅⟩ => ⟨(k₅.gpr (by decide)).trans h8₄,
      (k₅.gpr (by decide)).trans ((k₄.gpr (by decide)).trans hsi), h12, hbp,
      (k₅.gpr (by decide)).trans ((k₄.gpr (by decide)).trans ((k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans hdi₁))),
      by rw [mt, m₄, m₃, m₂, m₁], ((k13.trans k₄).trans k₅).mono (by simp)⟩

/-- After `j` halvings of `m`, from `s₁`. -/
structure HalfInv (s₁ : State) (B : Addr) (Z w m : Nat) (j : Nat) (t : State) : Prop where
  ws : Ws t B Z w
  keep : Keep [.r12, .r9, .r8, .rsi, .rax, .rdx, .rbp, .r14, .r13] s₁ t
  r13 : t.gpr .r13 = BitVec.ofNat 64 j
  frm : Frm B [(slot w aM, 16 * (w + 2)), (slot w aH, 16 * (w + 2)), (8 * sT, 8)] s₁.mem t.mem
  val : wv t.mem B (slot w aM) (2 * (w + 2)) = (halveStep^[j] (m, 0)).1
  tv : word t.mem B (8 * sT) = BitVec.ofNat 64 (halveStep^[j] (m, 0)).2

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

theorem mask_add_ofNat (c : Bool) (a : Nat) :
    mask c + 1 + BitVec.ofNat 64 a = BitVec.ofNat 64 (a + if c then 0 else 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, mask_add_one, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  cases c <;> simp; omega

/-- A halving. -/
theorem halfStep_ok {s₁ t : State} {B : Addr} {Z w m el j : Nat} (hI : HalfInv s₁ B Z w m j t)
    (hel : word s₁.mem B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 el) (he1 : 1 ≤ el)
    (he2 : el ≤ 8 * w) (hm : m < 2 ^ (64 * (w + (el + 7) / 8)))
    (h11 : s₁.gpr .r11 = BitVec.ofNat 64 (64 * (w + (el + 7) / 8))) (hj : j < 64 * (w + (el + 7) / 8)) :
    WP isa (seqs [.block halfHead, wordLoop 0 shrBody, wordLoop 0 selBody, .block halfNext]) t fun t' =>
      t'.zf = some (decide (j + 1 = 64 * (w + (el + 7) / 8))) ∧ HalfInv s₁ B Z w m (j + 1) t' := by
  have h := hI.ws
  have hn := h.scr.nowrap
  have hw1 := h.w1
  have hw2 := h.w2
  have hZ := h.hZ
  have h256 := h.h256
  have sH := slot_lt (w := w) (show aH + 1 < 16 by decide)
  have eHM : slot w aH = slot w aM + 32 * (w + 2) := by simp only [slot, hdrBytes, aH, aM]; omega
  have eH1 : slot w (aH + 1) = slot w aH + 8 * (w + 2) := by simp only [slot, hdrBytes, aH]; omega
  have hT0 := hdr_lt_slot w aM (show sT < 32 by decide)
  have eT : sT = 27 := rfl
  -- The header's `e_len`.
  have hel₀ : word t.mem B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 el := by
    rw [hI.frm.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [Impl.Bignum.X86_64.Public.sElen, sFn] <;> omega)
      (by simp only [Impl.Bignum.X86_64.Public.sElen, sFn]; omega)]
    exact hel
  obtain ⟨Bw, hBw⟩ : ∃ Bw, w + (el + 7) / 8 = Bw := ⟨_, rfl⟩
  rw [hBw] at hm h11 hj ⊢
  have hBw2 : Bw + 1 ≤ 2 * (w + 2) := by omega
  -- `m`'s current value and its words.
  have hmj : (halveStep^[j] (m, 0)).1 < 2 ^ (64 * Bw) := Nat.lt_of_le_of_lt (halve_le m j) hm
  have hlow : wv t.mem B (slot w aM) Bw = (halveStep^[j] (m, 0)).1 := by
    rw [wv_low_of_lt (v := Bw) (w := 2 * (w + 2)) (by omega) (by rw [hI.val]; exact hmj), hI.val]
  have htop : word t.mem B (slot w aM + 8 * Bw) = 0 := word_above_zero (L := 2 * (w + 2)) (by omega)
    (by rw [hI.val]; exact hmj)
  have hpar : (word t.mem B (slot w aM)).toNat % 2 = (halveStep^[j] (m, 0)).1 % 2 := by
    rw [← hlow, wv_low (show 1 ≤ Bw by omega)]; omega
  simp only [seqs]
  refine WP.seq (WP.mono (halfHead_ok h hel₀ (by omega)) fun t₁ ⟨h8, hsi, h12, hbp, hdi₁, m₁, k₁⟩ => ?_)
  rw [hBw] at h12
  have hs₁ := h.scr.congr k₁.2.2
  refine WP.seq (WP.mono (shr_ok hs₁ hsi h8 h12 (by omega) (by omega) (by omega) (by omega) (Or.inr (by omega)))
    fun t₂ ⟨hv₂, o₂, k₂⟩ => ?_)
  rw [m₁, htop] at hv₂
  have hs₂ := hs₁.congr k₂.2.2
  have hM₂ : wv t₂.mem B (slot w aM) Bw = wv t.mem B (slot w aM) Bw := by
    rw [o₂.wv (Or.inl (by omega)) (by omega), m₁]
  refine WP.seq (WP.mono (sel_ok hs₂ ((k₂.gpr (by decide)).trans h8) ((k₂.gpr (by decide)).trans hsi)
    ((k₂.gpr (by decide)).trans hbp) ((k₂.gpr (by decide)).trans h12) (by omega) (by omega) (by omega) (by omega)
    (Or.inl (by omega))) fun t₃ ⟨hv₃, o₃, k₃⟩ => ?_)
  have hs₃ := hs₂.congr k₃.2.2
  have k03 := ((hI.keep.trans k₁).trans k₂).trans k₃
  have hT₃ : word t₃.mem B (8 * sT) = BitVec.ofNat 64 (halveStep^[j] (m, 0)).2 := by
    rw [o₃.word (Or.inl (by omega)) (by omega), o₂.word (Or.inl (by omega)) (by omega), m₁, hI.tv]
  have hdi₃ : t₃.gpr .rdi = B := (k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans hdi₁)
  have hbp₃ : t₃.gpr .rbp = mask (decide ((word t.mem B (slot w aM)).toNat % 2 = 1)) :=
    (k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans hbp)
  have h13₃ : t₃.gpr .r13 = BitVec.ofNat 64 j := (k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans
    ((k₁.gpr (by decide)).trans hI.r13))
  have h11₃ : t₃.gpr .r11 = BitVec.ofNat 64 (64 * Bw) := (k03.gpr (by decide)).trans h11
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
  refine WP.mono (WP.keep [.rax, .r13] (Q := fun t' => t'.zf = some (decide (j + 1 = 64 * Bw)) ∧
      t'.gpr .r13 = BitVec.ofNat 64 (j + 1) ∧ t'.mem = t₃.mem.writeW (off B (8 * sT))
        (BitVec.ofNat 64 ((halveStep^[j] (m, 0)).2 +
          if decide ((word t.mem B (slot w aM)).toNat % 2 = 1) then 0 else 1))) (by
    unfold halfNext
    xrun [State.ea, hdr, hdi₃, hdrOff, hs₃.ld (d := 8 * sT) (by omega), hs₃.st (d := 8 * sT) (by omega), hbp₃,
      hT₃, h13₃, h11₃, ofNat_add_one, mask_add_ofNat,
      ofNat_sub_beq (show j + 1 < 2 ^ 64 by omega) (show 64 * Bw < 2 ^ 64 by omega)]) rfl)
    fun t' ⟨⟨hz, h13, mt⟩, k₄⟩ => ⟨hz, ?_⟩
  have o₄ := writeW_outside t₃.mem B (BitVec.ofNat 64 ((halveStep^[j] (m, 0)).2 +
    if decide ((word t.mem B (slot w aM)).toNat % 2 = 1) then 0 else 1)) (d := 8 * sT) (by omega)
  rw [← mt] at o₄
  have hf : Frm B [(slot w aM, 16 * (w + 2)), (slot w aH, 16 * (w + 2)), (8 * sT, 8)] t.mem t'.mem := by
    intro x hx
    have a := hx _ (List.mem_cons_self)
    have b := hx _ (List.mem_cons_of_mem _ List.mem_cons_self)
    have c := hx _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    dsimp only at a b c
    rw [o₄ x c, o₃ x (by omega), o₂ x (by omega), m₁]
  have hrm : ∀ r ∈ [(slot w aM, 16 * (w + 2)), (slot w aH, 16 * (w + 2)), (8 * sT, 8)], RMut r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact RMut.ofSlot _ _ _
    · exact RMut.ofSlot _ _ _
    · exact RMut.hdr (by decide)
  refine ⟨h.congrR hf hrm (((k₁.trans k₂).trans k₃).trans k₄) (by decide), (k03.trans k₄).mono (by simp), h13,
    hI.frm.trans hf, ?_, ?_⟩
  · -- `m`.
    have hfull : ∀ mm : Mem, wv mm B (slot w aM) (2 * (w + 2)) =
        wv mm B (slot w aM) Bw + 2 ^ (64 * Bw) * wv mm B (slot w aM + 8 * Bw) (2 * (w + 2) - Bw) := fun mm => by
      rw [← wv_add, show Bw + (2 * (w + 2) - Bw) = 2 * (w + 2) by omega]
    have hU : wv t'.mem B (slot w aM + 8 * Bw) (2 * (w + 2) - Bw) =
        wv t.mem B (slot w aM + 8 * Bw) (2 * (w + 2) - Bw) := by
      rw [o₄.wv (Or.inr (by omega)) (by omega), o₃.wv (Or.inr (by omega)) (by omega),
        o₂.wv (Or.inl (by omega)) (by omega), m₁]
    have hU0 : wv t.mem B (slot w aM + 8 * Bw) (2 * (w + 2) - Bw) = 0 := by
      have := hfull t.mem
      rw [hI.val, hlow] at this
      have := Nat.mul_eq_zero.mp (show 2 ^ (64 * Bw) * wv t.mem B (slot w aM + 8 * Bw) (2 * (w + 2) - Bw) = 0 by omega)
      exact this.resolve_left (Nat.ne_of_gt (Nat.pow_pos (by decide)))
    have hL : wv t'.mem B (slot w aM) Bw = wv t₃.mem B (slot w aM) Bw :=
      o₄.wv (Or.inr (by omega)) (by omega)
    rw [hfull, hU, hU0, Nat.mul_zero, Nat.add_zero, hL, hv₃, hM₂, hlow, Function.iterate_succ_apply']
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
    rw [mt, word_writeW_self, Function.iterate_succ_apply', hpar]
    generalize halveStep^[j] (m, 0) = st
    rcases st with ⟨mj, tj⟩
    unfold halveStep
    rcases Nat.mod_two_eq_zero_or_one mj with he | ho
    · simp [he]
    · simp [ho]

theorem dbl6 (x : Nat) : 2 * (2 * (2 * (2 * (2 * (2 * x))))) = 64 * x := by omega

/-- `halfInit`: `r11 := 64 Bw`, `r13 := 0` and `t := 0`. -/
theorem halfInit_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {el : Nat}
    (hel : word s.mem B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 el) (hel' : el < 2 ^ 32) :
    WP isa (.block halfInit) s fun t =>
      t.gpr .r11 = BitVec.ofNat 64 (64 * (w + (el + 7) / 8)) ∧ t.gpr .r13 = BitVec.ofNat 64 0 ∧
      t.mem = s.mem.writeW (off B (8 * sT)) (0 : BitVec 64) ∧ Keep [.rax, .r11, .r13] s t := by
  have h256 := h.h256
  unfold halfInit
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (bw_ok h hel hel') fun t₁ ⟨hax, m₁, k₁⟩ => ?_
  have hs₁ := h.scr.congr k₁.2.2
  have hdi₁ : t₁.gpr .rdi = B := (k₁.gpr (by decide)).trans h.rdi
  refine WP.mono (WP.keep [.r11, .r13, .rax] (Q := fun t => t.gpr .r11 = BitVec.ofNat 64 (64 * (w + (el + 7) / 8)) ∧
      t.gpr .r13 = BitVec.ofNat 64 0 ∧ t.mem = s.mem.writeW (off B (8 * sT)) (0 : BitVec 64)) (by
    simp only [List.replicate, List.cons_append, List.nil_append]
    xrun [State.ea, hdr, hdi₁, hdrOff, hs₁.st (d := 8 * sT) (by simp only [sT, sFn]; omega), hax, ofNat_dbl, dbl6,
      m₁]
    rfl) rfl)
    fun t ⟨q, k₂⟩ => ⟨q.1, q.2.1, q.2.2, (k₁.trans k₂).mono (by simp)⟩

/-- `halving`: `m = 2^t r` with `r` odd, for `0 < m < 2^(64 Bw)` in `M`. -/
theorem halving_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {el m : Nat}
    (hel : word s.mem B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 el) (he1 : 1 ≤ el)
    (he2 : el ≤ 8 * w) (hv : wv s.mem B (slot w aM) (2 * (w + 2)) = m) (hm0 : 0 < m)
    (hm : m < 2 ^ (64 * (w + (el + 7) / 8))) :
    WP isa halving s fun t => Ws t B Z w ∧
      wv t.mem B (slot w aM) (2 * (w + 2)) = (splitTwos m).2 ∧
      word t.mem B (8 * sT) = BitVec.ofNat 64 (splitTwos m).1 ∧
      Frm B [(slot w aM, 16 * (w + 2)), (slot w aH, 16 * (w + 2)), (8 * sT, 8)] s.mem t.mem ∧
      Keep [.r12, .r9, .r8, .rsi, .rax, .rdx, .rbp, .r14, .r13, .r11] s t := by
  have hn := h.scr.nowrap
  have h256 := h.h256
  have hw2 := h.w2
  have hT0 := hdr_lt_slot w aM (show sT < 32 by decide)
  have sH := slot_lt (w := w) (show aH + 1 < 16 by decide)
  have eHM : slot w aH = slot w aM + 32 * (w + 2) := by simp only [slot, hdrBytes, aH, aM]; omega
  have eH1 : slot w (aH + 1) = slot w aH + 8 * (w + 2) := by simp only [slot, hdrBytes, aH]; omega
  unfold halving
  refine WP.seq (WP.mono (halfInit_ok h hel (by omega)) fun s₁ ⟨h11, h13, m₁, k₁⟩ => ?_)
  have hZ := h.hZ
  have o₁ := writeW_outside s.mem B (0 : BitVec 64) (d := 8 * sT) (by simp only [sT, sFn]; omega)
  rw [← m₁] at o₁
  have hf₁ : Frm B [(slot w aM, 16 * (w + 2)), (slot w aH, 16 * (w + 2)), (8 * sT, 8)] s.mem s₁.mem :=
    fun x hx => o₁ x (hx _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  have hrm : ∀ r ∈ [(slot w aM, 16 * (w + 2)), (slot w aH, 16 * (w + 2)), (8 * sT, 8)], RMut r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact RMut.ofSlot _ _ _
    · exact RMut.ofSlot _ _ _
    · exact RMut.hdr (by decide)
  have h₁ := h.congrR hf₁ hrm k₁ (by decide)
  have hel₁ : word s₁.mem B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 el := by
    rw [o₁.word (Or.inl (by simp only [Impl.Bignum.X86_64.Public.sElen, sFn, sT]; omega))
      (by simp only [Impl.Bignum.X86_64.Public.sElen, sFn]; omega)]; exact hel
  refine wp_upto (a := 0) (N := 64 * (w + (el + 7) / 8)) (by omega) (HalfInv s₁ B Z w m)
    (fun j _ hj t hI => halfStep_ok hI hel₁ he1 he2 hm h11 hj) (fun t hI => ?_)
    ⟨h₁, Keep.refl _ _, h13, Frm.refl _ _ _, by rw [o₁.wv (Or.inr (by omega)) (by omega), hv]; rfl,
      by rw [m₁, word_writeW_self]; rfl⟩
  have hd := halve_done hm0 hm
  have hval := hI.val
  have htv := hI.tv
  rw [hd] at hval htv
  exact ⟨hI.ws, hval, htv, hf₁.trans hI.frm, (k₁.trans hI.keep).mono (by simp)⟩

end VG.Proof.Rsa.X86_64
