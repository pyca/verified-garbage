import VerifiedGarbage.Proof.Rsa.X86_64.CvVerified
import VerifiedGarbage.Proof.Rsa.RecoverMath
import VerifiedGarbage.Proof.Bignum.X86_64.CrtEntry
import VerifiedGarbage.Proof.Bignum.X86_64.PcVerified
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.Rsa.X86_64.RpHalf`. -/
section

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
    (hel : VG.Proof.Bignum.X86_64.word s.mem B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 el) (hel' : el < 2 ^ 32) :
    WP isa (.block bw) s fun t => t.gpr .rax = BitVec.ofNat 64 (w + (el + 7) / 8) ∧ t.mem = s.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax] s t := by
  have hn := h.scr.nowrap
  have h256 := h.h256
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi => h.scr.ld (by omega)
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
    have := VG.Proof.Rsa.X86_64.halve_le m j
    generalize halveStep^[j] (m, 0) = st at this ⊢
    unfold halveStep
    split <;> (try simp only) <;> omega

/-- `halfHead`: the bases of `m` and the temporary, `r12 := Bw`, and `rbp`
the mask of `m` odd. -/
theorem halfHead_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {el : Nat}
    (hel : VG.Proof.Bignum.X86_64.word s.mem B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 el) (hel' : el < 2 ^ 32) :
    WP isa (.block halfHead) s fun t =>
      t.gpr .r8 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w aM) ∧ t.gpr .rsi = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w aH) ∧
      t.gpr .r12 = BitVec.ofNat 64 (w + (el + 7) / 8) ∧
      t.gpr .rbp = VG.Proof.Bignum.X86_64.mask (decide ((VG.Proof.Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w aM)).toNat % 2 = 1)) ∧ t.gpr .rdi = B ∧ t.mem = s.mem ∧
      VG.Proof.MlKem.X86_64.Keep [.r12, .r9, .r8, .rsi, .rax, .rbp] s t := by
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
  refine WP.mono (VG.Proof.Rsa.X86_64.bw_ok hw₃ (by rw [m₃, m₂, m₁]; exact hel) hel') fun t₄ ⟨hax, m₄, k₄⟩ => ?_
  have hs₄ := h.scr.congr (k13.trans k₄).2.2
  have h8₄ : t₄.gpr .r8 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w aM) := (k₄.gpr (by decide)).trans ((k₃.gpr (by decide)).trans h8)
  refine WP.mono (WP.keep [.r12, .rax, .rbp] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 (w + (el + 7) / 8) ∧
      t.gpr .rbp = VG.Proof.Bignum.X86_64.mask (decide ((VG.Proof.Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w aM)).toNat % 2 = 1)) ∧ t.mem = t₄.mem) (by
    xrun [State.ea, at0, h8₄, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, hax,
      hs₄.ld (d := VG.Proof.Bignum.X86_64.slot w aM) (by omega), m₄, m₃, m₂, m₁, mask_low]) rfl)
    fun t ⟨⟨h12, hbp, mt⟩, k₅⟩ => ⟨(k₅.gpr (by decide)).trans h8₄,
      (k₅.gpr (by decide)).trans ((k₄.gpr (by decide)).trans hsi), h12, hbp,
      (k₅.gpr (by decide)).trans ((k₄.gpr (by decide)).trans ((k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans hdi₁))),
      by rw [mt, m₄, m₃, m₂, m₁], ((k13.trans k₄).trans k₅).mono (by simp)⟩

/-- After `j` halvings of `m`, from `s₁`. -/
structure HalfInv (s₁ : State) (B : Addr) (Z w m : Nat) (j : Nat) (t : State) : Prop where
  ws : Ws t B Z w
  keep : VG.Proof.MlKem.X86_64.Keep [.r12, .r9, .r8, .rsi, .rax, .rdx, .rbp, .r14, .r13] s₁ t
  r13 : t.gpr .r13 = BitVec.ofNat 64 j
  frm : Frm B [(VG.Proof.Bignum.X86_64.slot w aM, 16 * (w + 2)), (VG.Proof.Bignum.X86_64.slot w aH, 16 * (w + 2)), (8 * sT, 8)] s₁.mem t.mem
  val : wv t.mem B (VG.Proof.Bignum.X86_64.slot w aM) (2 * (w + 2)) = (halveStep^[j] (m, 0)).1
  tv : VG.Proof.Bignum.X86_64.word t.mem B (8 * sT) = BitVec.ofNat 64 (halveStep^[j] (m, 0)).2

/-- The words of a number above its value's `n` words are zero. -/
theorem word_above_zero {mm : Mem} {B : Addr} {e n L : Nat} (hnL : n < L) (h : wv mm B e L < 2 ^ (64 * n)) :
    VG.Proof.Bignum.X86_64.word mm B (e + 8 * n) = 0 := by
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
    VG.Proof.Bignum.X86_64.mask c + 1 + BitVec.ofNat 64 a = BitVec.ofNat 64 (a + if c then 0 else 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, mask_add_one, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  cases c <;> simp; omega

/-- A halving. -/
theorem halfStep_ok {s₁ t : State} {B : Addr} {Z w m el j : Nat} (hI : VG.Proof.Rsa.X86_64.HalfInv s₁ B Z w m j t)
    (hel : VG.Proof.Bignum.X86_64.word s₁.mem B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 el) (he1 : 1 ≤ el)
    (he2 : el ≤ 8 * w) (hm : m < 2 ^ (64 * (w + (el + 7) / 8)))
    (h11 : s₁.gpr .r11 = BitVec.ofNat 64 (64 * (w + (el + 7) / 8))) (hj : j < 64 * (w + (el + 7) / 8)) :
    WP isa (seqs [.block halfHead, wordLoop 0 shrBody, wordLoop 0 VG.Impl.Rsa.X86_64.Keys.selBody, .block halfNext]) t fun t' =>
      t'.zf = some (decide (j + 1 = 64 * (w + (el + 7) / 8))) ∧ VG.Proof.Rsa.X86_64.HalfInv s₁ B Z w m (j + 1) t' := by
  have h := hI.ws
  have hn := h.scr.nowrap
  have hw1 := h.w1
  have hw2 := h.w2
  have hZ := h.hZ
  have h256 := h.h256
  have sH := slot_lt (w := w) (show aH + 1 < 16 by decide)
  have eHM : VG.Proof.Bignum.X86_64.slot w aH = VG.Proof.Bignum.X86_64.slot w aM + 32 * (w + 2) := by simp only [VG.Proof.Bignum.X86_64.slot, hdrBytes, aH, aM]; omega
  have eH1 : VG.Proof.Bignum.X86_64.slot w (aH + 1) = VG.Proof.Bignum.X86_64.slot w aH + 8 * (w + 2) := by simp only [VG.Proof.Bignum.X86_64.slot, hdrBytes, aH]; omega
  have hT0 := hdr_lt_slot w aM (show sT < 32 by decide)
  have eT : sT = 27 := rfl
  -- The header's `e_len`.
  have hel₀ : VG.Proof.Bignum.X86_64.word t.mem B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 el := by
    rw [hI.frm.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [Impl.Bignum.X86_64.Public.sElen, sFn] <;> omega)
      (by simp only [Impl.Bignum.X86_64.Public.sElen, sFn]; omega)]
    exact hel
  obtain ⟨Bw, hBw⟩ : ∃ Bw, w + (el + 7) / 8 = Bw := ⟨_, rfl⟩
  rw [hBw] at hm h11 hj ⊢
  have hBw2 : Bw + 1 ≤ 2 * (w + 2) := by omega
  -- `m`'s current value and its words.
  have hmj : (halveStep^[j] (m, 0)).1 < 2 ^ (64 * Bw) := Nat.lt_of_le_of_lt (VG.Proof.Rsa.X86_64.halve_le m j) hm
  have hlow : wv t.mem B (VG.Proof.Bignum.X86_64.slot w aM) Bw = (halveStep^[j] (m, 0)).1 := by
    rw [wv_low_of_lt (v := Bw) (w := 2 * (w + 2)) (by omega) (by rw [hI.val]; exact hmj), hI.val]
  have htop : VG.Proof.Bignum.X86_64.word t.mem B (VG.Proof.Bignum.X86_64.slot w aM + 8 * Bw) = 0 := VG.Proof.Rsa.X86_64.word_above_zero (L := 2 * (w + 2)) (by omega)
    (by rw [hI.val]; exact hmj)
  have hpar : (VG.Proof.Bignum.X86_64.word t.mem B (VG.Proof.Bignum.X86_64.slot w aM)).toNat % 2 = (halveStep^[j] (m, 0)).1 % 2 := by
    rw [← hlow, VG.Proof.Rsa.X86_64.wv_low (show 1 ≤ Bw by omega)]; omega
  simp only [seqs]
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86_64.halfHead_ok h hel₀ (by omega)) fun t₁ ⟨h8, hsi, h12, hbp, hdi₁, m₁, k₁⟩ => ?_)
  rw [hBw] at h12
  have hs₁ := h.scr.congr k₁.2.2
  refine WP.seq (WP.mono (shr_ok hs₁ hsi h8 h12 (by omega) (by omega) (by omega) (by omega) (Or.inr (by omega)))
    fun t₂ ⟨hv₂, o₂, k₂⟩ => ?_)
  rw [m₁, htop] at hv₂
  have hs₂ := hs₁.congr k₂.2.2
  have hM₂ : wv t₂.mem B (VG.Proof.Bignum.X86_64.slot w aM) Bw = wv t.mem B (VG.Proof.Bignum.X86_64.slot w aM) Bw := by
    rw [o₂.wv (Or.inl (by omega)) (by omega), m₁]
  refine WP.seq (WP.mono (sel_ok hs₂ ((k₂.gpr (by decide)).trans h8) ((k₂.gpr (by decide)).trans hsi)
    ((k₂.gpr (by decide)).trans hbp) ((k₂.gpr (by decide)).trans h12) (by omega) (by omega) (by omega) (by omega)
    (Or.inl (by omega))) fun t₃ ⟨hv₃, o₃, k₃⟩ => ?_)
  have hs₃ := hs₂.congr k₃.2.2
  have k03 := ((hI.keep.trans k₁).trans k₂).trans k₃
  have hT₃ : VG.Proof.Bignum.X86_64.word t₃.mem B (8 * sT) = BitVec.ofNat 64 (halveStep^[j] (m, 0)).2 := by
    rw [o₃.word (Or.inl (by omega)) (by omega), o₂.word (Or.inl (by omega)) (by omega), m₁, hI.tv]
  have hdi₃ : t₃.gpr .rdi = B := (k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans hdi₁)
  have hbp₃ : t₃.gpr .rbp = VG.Proof.Bignum.X86_64.mask (decide ((VG.Proof.Bignum.X86_64.word t.mem B (VG.Proof.Bignum.X86_64.slot w aM)).toNat % 2 = 1)) :=
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
      t'.gpr .r13 = BitVec.ofNat 64 (j + 1) ∧ t'.mem = t₃.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * sT))
        (BitVec.ofNat 64 ((halveStep^[j] (m, 0)).2 +
          if decide ((VG.Proof.Bignum.X86_64.word t.mem B (VG.Proof.Bignum.X86_64.slot w aM)).toNat % 2 = 1) then 0 else 1))) (by
    unfold halfNext
    xrun [State.ea, hdr, hdi₃, hdrOff, hs₃.ld (d := 8 * sT) (by omega), hs₃.st (d := 8 * sT) (by omega), hbp₃,
      hT₃, h13₃, h11₃, ofNat_add_one, VG.Proof.Rsa.X86_64.mask_add_ofNat,
      ofNat_sub_beq (show j + 1 < 2 ^ 64 by omega) (show 64 * Bw < 2 ^ 64 by omega)]) rfl)
    fun t' ⟨⟨hz, h13, mt⟩, k₄⟩ => ⟨hz, ?_⟩
  have o₄ := VG.Proof.Bignum.X86_64.writeW_outside t₃.mem B (BitVec.ofNat 64 ((halveStep^[j] (m, 0)).2 +
    if decide ((VG.Proof.Bignum.X86_64.word t.mem B (VG.Proof.Bignum.X86_64.slot w aM)).toNat % 2 = 1) then 0 else 1)) (d := 8 * sT) (by omega)
  rw [← mt] at o₄
  have hf : Frm B [(VG.Proof.Bignum.X86_64.slot w aM, 16 * (w + 2)), (VG.Proof.Bignum.X86_64.slot w aH, 16 * (w + 2)), (8 * sT, 8)] t.mem t'.mem := by
    intro x hx
    have a := hx _ (List.mem_cons_self)
    have b := hx _ (List.mem_cons_of_mem _ List.mem_cons_self)
    have c := hx _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    dsimp only at a b c
    rw [o₄ x c, o₃ x (by omega), o₂ x (by omega), m₁]
  have hrm : ∀ r ∈ [(VG.Proof.Bignum.X86_64.slot w aM, 16 * (w + 2)), (VG.Proof.Bignum.X86_64.slot w aH, 16 * (w + 2)), (8 * sT, 8)], RMut r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact RMut.ofSlot _ _ _
    · exact RMut.ofSlot _ _ _
    · exact RMut.hdr (by decide)
  refine ⟨h.congrR hf hrm (((k₁.trans k₂).trans k₃).trans k₄) (by decide), (k03.trans k₄).mono (by simp), h13,
    hI.frm.trans hf, ?_, ?_⟩
  · -- `m`.
    have hfull : ∀ mm : Mem, wv mm B (VG.Proof.Bignum.X86_64.slot w aM) (2 * (w + 2)) =
        wv mm B (VG.Proof.Bignum.X86_64.slot w aM) Bw + 2 ^ (64 * Bw) * wv mm B (VG.Proof.Bignum.X86_64.slot w aM + 8 * Bw) (2 * (w + 2) - Bw) := fun mm => by
      rw [← wv_add, show Bw + (2 * (w + 2) - Bw) = 2 * (w + 2) by omega]
    have hU : wv t'.mem B (VG.Proof.Bignum.X86_64.slot w aM + 8 * Bw) (2 * (w + 2) - Bw) =
        wv t.mem B (VG.Proof.Bignum.X86_64.slot w aM + 8 * Bw) (2 * (w + 2) - Bw) := by
      rw [o₄.wv (Or.inr (by omega)) (by omega), o₃.wv (Or.inr (by omega)) (by omega),
        o₂.wv (Or.inl (by omega)) (by omega), m₁]
    have hU0 : wv t.mem B (VG.Proof.Bignum.X86_64.slot w aM + 8 * Bw) (2 * (w + 2) - Bw) = 0 := by
      have := hfull t.mem
      rw [hI.val, hlow] at this
      have := Nat.mul_eq_zero.mp (show 2 ^ (64 * Bw) * wv t.mem B (VG.Proof.Bignum.X86_64.slot w aM + 8 * Bw) (2 * (w + 2) - Bw) = 0 by omega)
      exact this.resolve_left (by positivity)
    have hL : wv t'.mem B (VG.Proof.Bignum.X86_64.slot w aM) Bw = wv t₃.mem B (VG.Proof.Bignum.X86_64.slot w aM) Bw :=
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
    rw [mt, VG.Proof.Bignum.X86_64.word_writeW_self, Function.iterate_succ_apply', hpar]
    generalize halveStep^[j] (m, 0) = st
    rcases st with ⟨mj, tj⟩
    unfold halveStep
    rcases Nat.mod_two_eq_zero_or_one mj with he | ho
    · simp [he]
    · simp [ho]

theorem dbl6 (x : Nat) : 2 * (2 * (2 * (2 * (2 * (2 * x))))) = 64 * x := by omega

/-- `halfInit`: `r11 := 64 Bw`, `r13 := 0` and `t := 0`. -/
theorem halfInit_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {el : Nat}
    (hel : VG.Proof.Bignum.X86_64.word s.mem B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 el) (hel' : el < 2 ^ 32) :
    WP isa (.block halfInit) s fun t =>
      t.gpr .r11 = BitVec.ofNat 64 (64 * (w + (el + 7) / 8)) ∧ t.gpr .r13 = BitVec.ofNat 64 0 ∧
      t.mem = s.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * sT)) (0 : BitVec 64) ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .r11, .r13] s t := by
  have h256 := h.h256
  unfold halfInit
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.Rsa.X86_64.bw_ok h hel hel') fun t₁ ⟨hax, m₁, k₁⟩ => ?_
  have hs₁ := h.scr.congr k₁.2.2
  have hdi₁ : t₁.gpr .rdi = B := (k₁.gpr (by decide)).trans h.rdi
  refine WP.mono (WP.keep [.r11, .r13, .rax] (Q := fun t => t.gpr .r11 = BitVec.ofNat 64 (64 * (w + (el + 7) / 8)) ∧
      t.gpr .r13 = BitVec.ofNat 64 0 ∧ t.mem = s.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * sT)) (0 : BitVec 64)) (by
    simp only [List.replicate, List.cons_append, List.nil_append]
    xrun [State.ea, hdr, hdi₁, hdrOff, hs₁.st (d := 8 * sT) (by simp only [sT, sFn]; omega), hax, VG.Proof.Rsa.X86_64.ofNat_dbl, VG.Proof.Rsa.X86_64.dbl6,
      m₁]
    rfl) rfl)
    fun t ⟨q, k₂⟩ => ⟨q.1, q.2.1, q.2.2, (k₁.trans k₂).mono (by simp)⟩

/-- `halving`: `m = 2^t r` with `r` odd, for `0 < m < 2^(64 Bw)` in `M`. -/
theorem halving_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {el m : Nat}
    (hel : VG.Proof.Bignum.X86_64.word s.mem B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 el) (he1 : 1 ≤ el)
    (he2 : el ≤ 8 * w) (hv : wv s.mem B (VG.Proof.Bignum.X86_64.slot w aM) (2 * (w + 2)) = m) (hm0 : 0 < m)
    (hm : m < 2 ^ (64 * (w + (el + 7) / 8))) :
    WP isa halving s fun t => Ws t B Z w ∧
      wv t.mem B (VG.Proof.Bignum.X86_64.slot w aM) (2 * (w + 2)) = (splitTwos m).2 ∧
      VG.Proof.Bignum.X86_64.word t.mem B (8 * sT) = BitVec.ofNat 64 (splitTwos m).1 ∧
      Frm B [(VG.Proof.Bignum.X86_64.slot w aM, 16 * (w + 2)), (VG.Proof.Bignum.X86_64.slot w aH, 16 * (w + 2)), (8 * sT, 8)] s.mem t.mem ∧
      VG.Proof.MlKem.X86_64.Keep [.r12, .r9, .r8, .rsi, .rax, .rdx, .rbp, .r14, .r13, .r11] s t := by
  have hn := h.scr.nowrap
  have h256 := h.h256
  have hw2 := h.w2
  have hT0 := hdr_lt_slot w aM (show sT < 32 by decide)
  have sH := slot_lt (w := w) (show aH + 1 < 16 by decide)
  have eHM : VG.Proof.Bignum.X86_64.slot w aH = VG.Proof.Bignum.X86_64.slot w aM + 32 * (w + 2) := by simp only [VG.Proof.Bignum.X86_64.slot, hdrBytes, aH, aM]; omega
  have eH1 : VG.Proof.Bignum.X86_64.slot w (aH + 1) = VG.Proof.Bignum.X86_64.slot w aH + 8 * (w + 2) := by simp only [VG.Proof.Bignum.X86_64.slot, hdrBytes, aH]; omega
  unfold halving
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86_64.halfInit_ok h hel (by omega)) fun s₁ ⟨h11, h13, m₁, k₁⟩ => ?_)
  have hZ := h.hZ
  have o₁ := VG.Proof.Bignum.X86_64.writeW_outside s.mem B (0 : BitVec 64) (d := 8 * sT) (by simp only [sT, sFn]; omega)
  rw [← m₁] at o₁
  have hf₁ : Frm B [(VG.Proof.Bignum.X86_64.slot w aM, 16 * (w + 2)), (VG.Proof.Bignum.X86_64.slot w aH, 16 * (w + 2)), (8 * sT, 8)] s.mem s₁.mem :=
    fun x hx => o₁ x (hx _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  have hrm : ∀ r ∈ [(VG.Proof.Bignum.X86_64.slot w aM, 16 * (w + 2)), (VG.Proof.Bignum.X86_64.slot w aH, 16 * (w + 2)), (8 * sT, 8)], RMut r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact RMut.ofSlot _ _ _
    · exact RMut.ofSlot _ _ _
    · exact RMut.hdr (by decide)
  have h₁ := h.congrR hf₁ hrm k₁ (by decide)
  have hel₁ : VG.Proof.Bignum.X86_64.word s₁.mem B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 el := by
    rw [o₁.word (Or.inl (by simp only [Impl.Bignum.X86_64.Public.sElen, sFn, sT]; omega))
      (by simp only [Impl.Bignum.X86_64.Public.sElen, sFn]; omega)]; exact hel
  refine wp_upto (a := 0) (N := 64 * (w + (el + 7) / 8)) (by omega) (VG.Proof.Rsa.X86_64.HalfInv s₁ B Z w m)
    (fun j _ hj t hI => VG.Proof.Rsa.X86_64.halfStep_ok hI hel₁ he1 he2 hm h11 hj) (fun t hI => ?_)
    ⟨h₁, Keep.refl _ _, h13, Frm.refl _ _ _, by rw [o₁.wv (Or.inr (by omega)) (by omega), hv]; rfl,
      by rw [m₁, VG.Proof.Bignum.X86_64.word_writeW_self]; rfl⟩
  have hd := halve_done hm0 hm
  have hval := hI.val
  have htv := hI.tv
  rw [hd] at hval htv
  exact ⟨hI.ws, hval, htv, hf₁.trans hI.frm, (k₁.trans hI.keep).mono (by simp)⟩

end VG.Proof.Rsa.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rsa.X86_64.RpFrame`. -/
section

/-!
# `vg_rsa_recover_primes` on x86-64: what the pieces change

`rg w js hs`: the arrays `js` and the header slots `hs`, as ranges of the
working space. A piece changes only some of them (`Frm B (rg w js hs)`), and
an array or a slot that is not listed keeps its value (`Frm.rg_wv`,
`Frm.rg_word`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64

/-- The ranges of the arrays `js` and the header slots `hs`. -/
def rg (w : Nat) (js hs : List Nat) : List (Nat × Nat) :=
  js.map (fun j => (VG.Proof.Bignum.X86_64.slot w j, 8 * (w + 2))) ++ hs.map (fun i => (8 * i, 8))

theorem rg_mem_arr {w j : Nat} {js : List Nat} (hs : List Nat) (hj : j ∈ js) :
    (VG.Proof.Bignum.X86_64.slot w j, 8 * (w + 2)) ∈ VG.Proof.Rsa.X86_64.rg w js hs :=
  List.mem_append_left _ (List.mem_map_of_mem hj)

theorem rg_mem_hdr {w i : Nat} (js : List Nat) {hs : List Nat} (hi : i ∈ hs) : (8 * i, 8) ∈ VG.Proof.Rsa.X86_64.rg w js hs :=
  List.mem_append_right _ (List.mem_map_of_mem (f := fun i => (8 * i, 8)) hi)

theorem rg_rmut {w : Nat} {js hs : List Nat} (h : ∀ i ∈ hs, rSlot i = true) : ∀ r ∈ VG.Proof.Rsa.X86_64.rg w js hs, RMut r := by
  intro r hr
  simp only [VG.Proof.Rsa.X86_64.rg, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨j, _, rfl⟩ | ⟨i, hi, rfl⟩
  · exact RMut.ofSlot _ _ _
  · exact RMut.hdr (h i hi)

theorem slot_mono {w j k : Nat} (h : j ≤ k) : VG.Proof.Bignum.X86_64.slot w j ≤ VG.Proof.Bignum.X86_64.slot w k := by
  unfold VG.Proof.Bignum.X86_64.slot
  have := Nat.mul_le_mul_right (8 * (w + 2)) h
  omega

theorem slot_add (w j k : Nat) : VG.Proof.Bignum.X86_64.slot w (j + k) = VG.Proof.Bignum.X86_64.slot w j + k * (8 * (w + 2)) := by
  unfold VG.Proof.Bignum.X86_64.slot; rw [Nat.add_mul]; omega

/-- A range within the arrays `j` to `j + K - 1`, none of them in `js`, is
outside `rg w js hs`. -/
theorem rg_sep {w : Nat} {js hs : List Nat} (hhs : ∀ i ∈ hs, i < 32) {j K : Nat}
    (hjs : ∀ k ∈ js, k < j ∨ j + K ≤ k) {d n : Nat} (hd : VG.Proof.Bignum.X86_64.slot w j ≤ d) (hdn : d + 8 * n ≤ VG.Proof.Bignum.X86_64.slot w (j + K)) :
    ∀ r ∈ VG.Proof.Rsa.X86_64.rg w js hs, d + 8 * n ≤ r.1 ∨ r.1 + r.2 ≤ d := by
  intro r hr
  simp only [VG.Proof.Rsa.X86_64.rg, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨k, hk, rfl⟩ | ⟨i, hi, rfl⟩
  · dsimp only
    rcases hjs k hk with h | h
    · have := slot_lt (w := w) h; omega
    · have := VG.Proof.Rsa.X86_64.slot_mono (w := w) h; omega
  · have := hdr_lt_slot w j (hhs i hi); dsimp only; omega

/-- An array not in `js` keeps its value. -/
theorem _root_.VG.Proof.Bignum.X86_64.Frm.rg_wv {B : Addr} {w : Nat} {js hs : List Nat} {m m' : Mem} (h : Frm B (VG.Proof.Rsa.X86_64.rg w js hs) m m')
    (hZ : VG.Proof.Bignum.X86_64.slot w 16 ≤ 2 ^ 64) (hhs : ∀ i ∈ hs, i < 32) {j : Nat} (hj : j < 16) (hjs : j ∉ js) {n : Nat}
    (hn : n ≤ w + 2) : wv m' B (VG.Proof.Bignum.X86_64.slot w j) n = wv m B (VG.Proof.Bignum.X86_64.slot w j) n := by
  have h1 := slot_lt (w := w) hj
  have h2 := VG.Proof.Rsa.X86_64.slot_add w j 1
  exact h.wv_eq (VG.Proof.Rsa.X86_64.rg_sep hhs (K := 1) (fun k hk => by
    have : k ≠ j := fun e => hjs (e ▸ hk); omega) (Nat.le_refl _) (by omega)) (by omega)

/-- Two arrays `j` and `j + 1` not in `js` keep their value. -/
theorem _root_.VG.Proof.Bignum.X86_64.Frm.rg_wv2 {B : Addr} {w : Nat} {js hs : List Nat} {m m' : Mem} (h : Frm B (VG.Proof.Rsa.X86_64.rg w js hs) m m')
    (hZ : VG.Proof.Bignum.X86_64.slot w 16 ≤ 2 ^ 64) (hhs : ∀ i ∈ hs, i < 32) {j : Nat} (hj : j + 1 < 16) (hjs : j ∉ js)
    (hjs' : j + 1 ∉ js) {n : Nat} (hn : n ≤ 2 * (w + 2)) : wv m' B (VG.Proof.Bignum.X86_64.slot w j) n = wv m B (VG.Proof.Bignum.X86_64.slot w j) n := by
  have h1 := slot_lt (w := w) hj
  have h2 := VG.Proof.Rsa.X86_64.slot_add w j 1
  have h3 := VG.Proof.Rsa.X86_64.slot_add w j 2
  exact h.wv_eq (VG.Proof.Rsa.X86_64.rg_sep hhs (K := 2) (fun k hk => by
    have : k ≠ j := fun e => hjs (e ▸ hk)
    have : k ≠ j + 1 := fun e => hjs' (e ▸ hk)
    omega) (Nat.le_refl _) (by omega)) (by omega)

/-- A word of an array not in `js` keeps its value. -/
theorem _root_.VG.Proof.Bignum.X86_64.Frm.rg_wordA {B : Addr} {w : Nat} {js hs : List Nat} {m m' : Mem} (h : Frm B (VG.Proof.Rsa.X86_64.rg w js hs) m m')
    (hZ : VG.Proof.Bignum.X86_64.slot w 16 ≤ 2 ^ 64) (hhs : ∀ i ∈ hs, i < 32) {j : Nat} (hj : j < 16) (hjs : j ∉ js) {i : Nat}
    (hi : i < w + 2) : VG.Proof.Bignum.X86_64.word m' B (VG.Proof.Bignum.X86_64.slot w j + 8 * i) = VG.Proof.Bignum.X86_64.word m B (VG.Proof.Bignum.X86_64.slot w j + 8 * i) := by
  have h1 := slot_lt (w := w) hj
  have h2 := VG.Proof.Rsa.X86_64.slot_add w j 1
  have := VG.Proof.Rsa.X86_64.rg_sep (w := w) (js := js) hhs (K := 1) (j := j) (fun k hk => by
    have : k ≠ j := fun e => hjs (e ▸ hk); omega) (d := VG.Proof.Bignum.X86_64.slot w j + 8 * i) (n := 1) (by omega) (by omega)
  exact h.word_eq this (by omega)

/-- The low word of an array not in `js` keeps its value. -/
theorem _root_.VG.Proof.Bignum.X86_64.Frm.rg_word0 {B : Addr} {w : Nat} {js hs : List Nat} {m m' : Mem} (h : Frm B (VG.Proof.Rsa.X86_64.rg w js hs) m m')
    (hZ : VG.Proof.Bignum.X86_64.slot w 16 ≤ 2 ^ 64) (hhs : ∀ i ∈ hs, i < 32) {j : Nat} (hj : j < 16) (hjs : j ∉ js) :
    VG.Proof.Bignum.X86_64.word m' B (VG.Proof.Bignum.X86_64.slot w j) = VG.Proof.Bignum.X86_64.word m B (VG.Proof.Bignum.X86_64.slot w j) := by
  have := h.rg_wordA hZ hhs hj hjs (i := 0) (by omega)
  simpa using this

/-- A header slot not in `hs` keeps its value. -/
theorem _root_.VG.Proof.Bignum.X86_64.Frm.rg_word {B : Addr} {w : Nat} {js hs : List Nat} {m m' : Mem} (h : Frm B (VG.Proof.Rsa.X86_64.rg w js hs) m m')
    {i : Nat} (hi : i < 32) (his : i ∉ hs) : VG.Proof.Bignum.X86_64.word m' B (8 * i) = VG.Proof.Bignum.X86_64.word m B (8 * i) := by
  refine h.word_eq (fun r hr => ?_) (by omega)
  simp only [VG.Proof.Rsa.X86_64.rg, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨k, _, rfl⟩ | ⟨k, hk, rfl⟩
  · have := hdr_lt_slot w k hi; dsimp only; omega
  · have : k ≠ i := fun e => his (e ▸ hk); dsimp only; omega

theorem _root_.VG.Proof.Bignum.X86_64.Frm.rg_mono {B : Addr} {w : Nat} {js hs js' hs' : List Nat} {m m' : Mem} (h : Frm B (VG.Proof.Rsa.X86_64.rg w js hs) m m')
    (hj : ∀ j ∈ js, j ∈ js') (hh : ∀ i ∈ hs, i ∈ hs') : Frm B (VG.Proof.Rsa.X86_64.rg w js' hs') m m' :=
  h.mono fun r hr => by
    simp only [VG.Proof.Rsa.X86_64.rg, List.mem_append, List.mem_map] at hr
    rcases hr with ⟨j, hj', rfl⟩ | ⟨i, hi, rfl⟩
    · exact VG.Proof.Rsa.X86_64.rg_mem_arr _ (hj j hj')
    · exact VG.Proof.Rsa.X86_64.rg_mem_hdr _ (hh i hi)

theorem _root_.VG.Proof.Bignum.X86_64.Frm.rg_trans {B : Addr} {w : Nat} {js hs js' hs' : List Nat} {m₁ m₂ m₃ : Mem}
    (h₁ : Frm B (VG.Proof.Rsa.X86_64.rg w js hs) m₁ m₂) (h₂ : Frm B (VG.Proof.Rsa.X86_64.rg w js' hs') m₂ m₃) :
    Frm B (VG.Proof.Rsa.X86_64.rg w (js ++ js') (hs ++ hs')) m₁ m₃ :=
  Frm.trans (h₁.rg_mono (fun _ hj => List.mem_append_left _ hj) (fun _ hi => List.mem_append_left _ hi))
    (h₂.rg_mono (fun _ hj => List.mem_append_right _ hj) (fun _ hi => List.mem_append_right _ hi))

/-- A change within array `j`. -/
theorem _root_.VG.Proof.Bignum.X86_64.Frm.rg_of_out {B : Addr} {w : Nat} {m m' : Mem} {j n : Nat} (h : VG.Proof.Bignum.X86_64.Outside B (VG.Proof.Bignum.X86_64.slot w j) n m m')
    (hn : n ≤ 8 * (w + 2)) (js hs : List Nat) (hj : j ∈ js) : Frm B (VG.Proof.Rsa.X86_64.rg w js hs) m m' :=
  fun x hx => h x (by have := hx _ (VG.Proof.Rsa.X86_64.rg_mem_arr hs hj); dsimp only at this; omega)

/-- A change within arrays `j` and `j + 1`. -/
theorem _root_.VG.Proof.Bignum.X86_64.Frm.rg_of_out2 {B : Addr} {w : Nat} {m m' : Mem} {j n : Nat} (h : VG.Proof.Bignum.X86_64.Outside B (VG.Proof.Bignum.X86_64.slot w j) n m m')
    (hn : n ≤ 16 * (w + 2)) (js hs : List Nat) (hj : j ∈ js) (hj' : j + 1 ∈ js) : Frm B (VG.Proof.Rsa.X86_64.rg w js hs) m m' :=
  fun x hx => h x (by
    have := hx _ (VG.Proof.Rsa.X86_64.rg_mem_arr hs hj)
    have := hx _ (VG.Proof.Rsa.X86_64.rg_mem_arr hs hj')
    have := VG.Proof.Rsa.X86_64.slot_add w j 1
    dsimp only at *; omega)

/-- A change within header slot `i`. -/
theorem _root_.VG.Proof.Bignum.X86_64.Frm.rg_of_hdr {B : Addr} {w : Nat} {m m' : Mem} {i : Nat} (h : VG.Proof.Bignum.X86_64.Outside B (8 * i) 8 m m')
    (js hs : List Nat) (hi : i ∈ hs) : Frm B (VG.Proof.Rsa.X86_64.rg w js hs) m m' :=
  Frm.of_outside h (VG.Proof.Rsa.X86_64.rg_mem_hdr js hi)

/-- A change within the arrays `js'` (of `Arrays`), all in `js`. -/
theorem _root_.VG.Proof.Bignum.X86_64.Frm.rg_of_arrays {B : Addr} {w : Nat} {js' : List Nat} {m m' : Mem} (h : Arrays B w js' m m')
    (js hs : List Nat) (hj : ∀ j ∈ js', j ∈ js) : Frm B (VG.Proof.Rsa.X86_64.rg w js hs) m m' :=
  Frm.of_arrays h fun j hj' => VG.Proof.Rsa.X86_64.rg_mem_arr hs (hj j hj')


theorem rg_cover_arr {w j n d : Nat} {js : List Nat} (hs : List Nat) (hj : j ∈ js) (hd : VG.Proof.Bignum.X86_64.slot w j ≤ d)
    (hn : d + n ≤ VG.Proof.Bignum.X86_64.slot w j + 8 * (w + 2)) : ∃ r' ∈ VG.Proof.Rsa.X86_64.rg w js hs, r'.1 ≤ d ∧ d + n ≤ r'.1 + r'.2 :=
  ⟨_, VG.Proof.Rsa.X86_64.rg_mem_arr hs hj, hd, hn⟩

theorem rg_cover_hdr {w i : Nat} (js : List Nat) {hs : List Nat} (hi : i ∈ hs) :
    ∃ r' ∈ VG.Proof.Rsa.X86_64.rg w js hs, r'.1 ≤ 8 * i ∧ 8 * i + 8 ≤ r'.1 + r'.2 :=
  ⟨_, VG.Proof.Rsa.X86_64.rg_mem_hdr js hi, Nat.le_refl _, Nat.le_refl _⟩

theorem Ws.congrG {s t : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {js hs : List Nat}
    (hf : Frm B (VG.Proof.Rsa.X86_64.rg w js hs) s.mem t.mem) (hhs : ∀ i ∈ hs, rSlot i = true) {regs : List Reg} (k : VG.Proof.MlKem.X86_64.Keep regs s t)
    (hr : .rdi ∉ regs) : Ws t B Z w :=
  h.congrR hf (VG.Proof.Rsa.X86_64.rg_rmut hhs) k hr

end VG.Proof.Rsa.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rsa.X86_64.RpMont`. -/
section

/-!
# `vg_rsa_recover_primes` on x86-64: Montgomery form

`minvBlk`: `-n⁻¹ mod 2⁶⁴` into its slot (`minvBlk_ok`). `mont`: `R² mod n`
as `vg_rsa_public` computes it, 1, `R mod n` and `n - R mod n`, the
Montgomery forms of 1 and `-1` (`mont_ok`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aR2 aXm aY aOne sCnt)
open VG.Proof.Bignum (mont_cancel)

/-- `minvBlk`: `-n⁻¹ mod 2⁶⁴` into `sMinv`, for an odd `n`. -/
theorem minvBlk_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w)
    (hodd : (VG.Proof.Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w aN)).toNat % 2 = 1) :
    WP isa (.block minvBlk) s fun t =>
      ((VG.Proof.Bignum.X86_64.word t.mem B (VG.Proof.Bignum.X86_64.slot w aN)).toNat * (VG.Proof.Bignum.X86_64.word t.mem B (8 * sMinv)).toNat + 1) % 2 ^ 64 = 0 ∧
      Frm B (VG.Proof.Rsa.X86_64.rg w [] [sMinv]) s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs s t := by
  have hn := h.scr.nowrap
  have h256 := h.h256
  have sN := h.sl (j := aN) (by decide)
  have hN0 := hdr_lt_slot w aN (show sMinv < 32 by decide)
  unfold minvBlk
  rw [List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono h.ws_ok fun t₁ ⟨_, h9, m₁, k₁⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (base_ok aN (r := .r10) (by decide) ((k₁.gpr (by decide)).trans h.rdi) h9)
    fun t₂ ⟨h10, m₂, k₂⟩ => WP.block_append_iff.mpr ?_
  have hs₂ := h.scr.congr (k₁.trans k₂).2.2
  refine WP.mono (WP.keep [.rbx] (Q := fun t => t.gpr .rbx = VG.Proof.Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w aN) ∧ t.mem = s.mem) (by
    xrun [State.ea, at0, h10, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
      hs₂.ld (d := VG.Proof.Bignum.X86_64.slot w aN) (by omega), m₂, m₁]) rfl) fun t₃ ⟨⟨hbx, m₃⟩, k₃⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (minv_ok t₃ (by rw [hbx]; exact hodd)) fun t₄ ⟨hi, k₄, m₄⟩ => ?_
  have k14 := ((k₁.trans k₂).trans k₃).trans k₄
  have hdi₄ : t₄.gpr .rdi = B := (k14.gpr (by decide)).trans h.rdi
  have hs₄ := h.scr.congr k14.2.2
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = t₄.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * sMinv)) (t₄.gpr .r15)) (by
    xrun [State.ea, hdr, hdi₄, hdrOff, hs₄.st (d := 8 * sMinv) (by simp only [sMinv]; omega)]) rfl)
    fun t ⟨mt, k₅⟩ => ?_
  have o := VG.Proof.Bignum.X86_64.writeW_outside t₄.mem B (t₄.gpr .r15) (d := 8 * sMinv) (by simp only [sMinv]; omega)
  rw [← mt] at o
  have m4 : t₄.mem = s.mem := m₄.trans m₃
  refine ⟨?_, by rw [← m4]; exact Frm.rg_of_hdr o _ _ (List.mem_singleton_self _), (k14.trans k₅).mono (by decide)⟩
  rw [o.word (Or.inr (by omega)) (by omega), mt, VG.Proof.Bignum.X86_64.word_writeW_self, m4, ← hbx]
  exact hi

/-- The bases of a subtraction `[c] := [a] - [b]`, `w` and no borrow. -/
theorem subSet_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) (a b c : Nat) :
    WP isa (.block (VG.Impl.Rsa.X86_64.Keys.ws ++ base a .r8 ++ base b .r10 ++ base c .rsi ++ ([.mov32 .rbp (.imm 0)] : List Instr))) s fun t =>
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .r8 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w a) ∧ t.gpr .r10 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w b) ∧
      t.gpr .rsi = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w c) ∧ t.gpr .rbp = VG.Proof.Bignum.X86_64.mask false ∧ t.mem = s.mem ∧
      VG.Proof.MlKem.X86_64.Keep [.r12, .r9, .r8, .r10, .rsi, .rbp] s t := by
  rw [List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono h.ws_ok fun t₁ ⟨h12, h9, m₁, k₁⟩ => WP.block_append_iff.mpr ?_
  have hdi₁ : t₁.gpr .rdi = B := (k₁.gpr (by decide)).trans h.rdi
  refine WP.mono (base_ok a (r := .r8) (by decide) hdi₁ h9) fun t₂ ⟨h8, m₂, k₂⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (base_ok b (r := .r10) (by decide) ((k₂.gpr (by decide)).trans hdi₁)
    ((k₂.gpr (by decide)).trans h9)) fun t₃ ⟨h10, m₃, k₃⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (base_ok c (r := .rsi) (by decide) ((k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans hdi₁))
    ((k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans h9))) fun t₄ ⟨hsi, m₄, k₄⟩ => ?_
  refine WP.mono (WP.keep [.rbp] (Q := fun t => t.gpr .rbp = VG.Proof.Bignum.X86_64.mask false ∧ t.mem = t₄.mem) (by xrun) rfl)
    fun t ⟨⟨hbp, mt⟩, k₅⟩ => ⟨?_, ?_, ?_, (k₅.gpr (by decide)).trans hsi, hbp, by rw [mt, m₄, m₃, m₂, m₁],
      ((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).mono (by decide)⟩
  · exact (k₅.gpr (by decide)).trans ((k₄.gpr (by decide)).trans ((k₃.gpr (by decide)).trans
      ((k₂.gpr (by decide)).trans h12)))
  · exact (k₅.gpr (by decide)).trans ((k₄.gpr (by decide)).trans ((k₃.gpr (by decide)).trans h8))
  · exact (k₅.gpr (by decide)).trans ((k₄.gpr (by decide)).trans h10)

/-- `R` is invertible modulo `n`, and `R mod n`'s value. -/
theorem r_one {Y N R R2 : Nat} (hR : Nat.Coprime R N) (hY : Y < N) (hr2 : R2 % N = R * R % N)
    (h : Y * R % N = R2 * 1 % N) : Y = R % N := by
  rw [← Nat.mod_eq_of_lt hY]
  exact mont_cancel hR (by rw [h, Nat.mul_one, hr2])

/-- `mont`: `R² mod n`, 1, `R mod n` and `n - R mod n`, for the odd `n` in
its array, of `w` words with the top one not zero, and `-n⁻¹` in `sMinv`. -/
theorem mont_ok (M : Mont) {s : State} {B : Addr} {Z w N : Nat} (h : Ws s B Z w)
    (hinv : ((VG.Proof.Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w aN)).toNat * (VG.Proof.Bignum.X86_64.word s.mem B (8 * sMinv)).toNat + 1) % 2 ^ 64 = 0)
    (hn : wv s.mem B (VG.Proof.Bignum.X86_64.slot w aN) w = N) (hodd : N % 2 = 1) (hlo : 2 ^ (64 * (w - 1)) ≤ N) :
    WP isa (seqs (mont M.mm)) s fun t => Ws t B Z w ∧
      wv t.mem B (VG.Proof.Bignum.X86_64.slot w aR2) w < N ∧ wv t.mem B (VG.Proof.Bignum.X86_64.slot w aR2) w % N = 2 ^ (64 * w) * 2 ^ (64 * w) % N ∧
      wv t.mem B (VG.Proof.Bignum.X86_64.slot w aOne) w = 1 ∧ wv t.mem B (VG.Proof.Bignum.X86_64.slot w aO) w = 2 ^ (64 * w) % N ∧
      wv t.mem B (VG.Proof.Bignum.X86_64.slot w aNg) w = N - 2 ^ (64 * w) % N ∧
      Frm B (VG.Proof.Rsa.X86_64.rg w [aAcc, aTmp, aR2, aOne, aY, aO, aNg] [sCnt]) s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs s t := by
  have hn0 := h.scr.nowrap
  have h256 := h.h256
  have hZ := h.hZ
  have hw1 := h.w1
  have hw2 := h.w2
  have hZ16 : VG.Proof.Bignum.X86_64.slot w 16 ≤ 2 ^ 64 := by omega
  have hR : Nat.Coprime (2 ^ (64 * w)) N := VG.Proof.Bignum.coprime_pow2 hodd _
  have hN1 : 1 < N := by
    have : 1 ≤ 2 ^ (64 * (w - 1)) := Nat.one_le_two_pow
    have : 2 ^ 64 ≤ 2 ^ (64 * (w - 1)) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hNR : N < 2 ^ (64 * w) := hn ▸ wv_lt _ _ _ _
  obtain ⟨minv, hmv⟩ : ∃ v, VG.Proof.Bignum.X86_64.word s.mem B (8 * sMinv) = v := ⟨_, rfl⟩
  rw [hmv] at hinv
  rw [show mont M.mm = [.block [.mov .r12 (.mem (hdr sW)), .mov .r10 (.mem (hdr (sArr aN)))]] ++
    (r2Steps M ++ [.block [.mov32 .rdx (.imm 1), .mov32 .rcx (.imm 0), .mov .r12 (.mem (hdr sW))],
      setWord aOne .rcx, M.mm aY aR2 aOne, copyA aO aY,
      .block (VG.Impl.Rsa.X86_64.Keys.ws ++ base aN .r8 ++ base aO .r10 ++ base aNg .rsi ++ [.mov32 .rbp (.imm 0)]),
      wordLoop 0 subBody]) from rfl]
  refine wp_seqs_append (by simp) (by simp) ?_
  -- The bases of `n` and `w`.
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi => h.scr.ld (by omega)
  refine WP.mono (WP.keep [.r12, .r10] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .r10 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w aN) ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, h.rdi, hdrOff, hl _ (show sW < 32 by decide), hl _ (show sArr aN < 32 by decide), h.hw,
      h.harr aN (by decide)]) rfl) fun t₁ ⟨⟨h12, h10, m₁⟩, k₁⟩ => ?_
  have hw₁ : Ws t₁ B Z w := h.congrG (js := []) (hs := []) (by rw [m₁]; exact Frm.refl _ _ _) (by simp) k₁
    (by decide)
  have hg₁ := hw₁.good
  rw [m₁, hmv] at hg₁
  refine wp_seqs_append (by simp [r2Steps]) (by simp) (WP.mono (r2_ok M hg₁.1 hg₁.2 hw1 (by omega)
    (by rw [m₁]; exact hn) (by rw [m₁]; exact hinv) h12 h10 hodd hlo) fun t₂ ⟨hg₂, hlt, hc, hf₂, k₂⟩ => ?_)
  have hf₂' : Frm B (VG.Proof.Rsa.X86_64.rg w [aAcc, aTmp, aR2] [sCnt]) t₁.mem t₂.mem := hf₂
  have hw₂ : Ws t₂ B Z w := hw₁.congrG hf₂' (by decide) k₂ (by decide)
  have hN₂ : wv t₂.mem B (VG.Proof.Bignum.X86_64.slot w aN) w = N := by
    rw [hf₂'.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega), m₁, hn]
  have hi₂ : ((VG.Proof.Bignum.X86_64.word t₂.mem B (VG.Proof.Bignum.X86_64.slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [hf₂'.rg_word0 hZ16 (by decide) (by decide) (by decide), m₁]; exact hinv
  have hmv₂ : VG.Proof.Bignum.X86_64.word t₂.mem B (8 * sMinv) = minv := hg₂.hdr.hminv
  simp only [seqs]
  -- 1, 0 and `w`.
  refine WP.seq (WP.mono (WP.keep [.rdx, .rcx, .r12] (Q := fun t => t.gpr .rdx = BitVec.ofNat 64 1 ∧
      t.gpr .rcx = BitVec.ofNat 64 0 ∧ t.gpr .r12 = BitVec.ofNat 64 w ∧ t.mem = t₂.mem) (by
    xrun [State.ea, hdr, hw₂.rdi, hdrOff, hw₂.scr.ld (d := 8 * sW) (by simp only [sW]; omega), hw₂.hw]
    ) rfl) fun t₃ ⟨⟨hdx, hcx, h12₃, m₃⟩, k₃⟩ => ?_)
  have hw₃ : Ws t₃ B Z w := hw₂.congrG (js := []) (hs := []) (by rw [m₃]; exact Frm.refl _ _ _) (by simp) k₃
    (by decide)
  have hH₃ : Hdr t₃.mem B w minv := ⟨hw₃.hw, by rw [m₃]; exact hmv₂, fun j hj => hw₃.harr j hj⟩
  refine WP.seq (WP.mono (setWord_ok hw₃.scr hw₃.rdi hH₃ hg₁.2 h12₃ (by omega) (by omega)
    (o := aOne) (by decide) (ri := .rcx) (by decide) (i := 0) (by omega) hcx) fun t₄ ⟨hv₄, o₄, k₄⟩ => ?_)
  rw [hdx, BitVec.toNat_ofNat] at hv₄
  have hf₄ : Frm B (VG.Proof.Rsa.X86_64.rg w [aOne] []) t₃.mem t₄.mem := Frm.rg_of_out o₄ (Nat.le_refl _) _ _ (by decide)
  have hw₄ : Ws t₄ B Z w := hw₃.congrG hf₄ (by simp) k₄ (by decide)
  have hg₄ := hw₄.good
  have hmv₄ : VG.Proof.Bignum.X86_64.word t₄.mem B (8 * sMinv) = minv := by
    rw [hf₄.rg_word (by decide) (by simp), m₃, hmv₂]
  rw [hmv₄] at hg₄
  have hN₄ : wv t₄.mem B (VG.Proof.Bignum.X86_64.slot w aN) w = N := by
    rw [hf₄.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega), m₃, hN₂]
  have hi₄ : ((VG.Proof.Bignum.X86_64.word t₄.mem B (VG.Proof.Bignum.X86_64.slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [hf₄.rg_word0 hZ16 (by simp) (by decide) (by decide), m₃]; exact hi₂
  have hR2₄ : wv t₄.mem B (VG.Proof.Bignum.X86_64.slot w aR2) w = wv t₂.mem B (VG.Proof.Bignum.X86_64.slot w aR2) w := by
    rw [hf₄.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega), m₃]
  -- `Y = R mod n`.
  refine WP.seq (WP.mono (M.mm_ok hg₄.1 hg₄.2 hw1 (by omega) (o := aY) (a := aR2) (b := aOne) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hi₄
    (by rw [hv₄, hN₄]; simpa using hN1)) fun t₅ ⟨hg₅, hlt₅, hc₅, ha₅, k₅⟩ => ?_)
  rw [hN₄] at hlt₅
  rw [hN₄, hR2₄, hv₄] at hc₅
  have hY₅ : wv t₅.mem B (VG.Proof.Bignum.X86_64.slot w aY) w = 2 ^ (64 * w) % N := VG.Proof.Rsa.X86_64.r_one hR hlt₅ hc (by simpa using hc₅)
  have hf₅ : Frm B (VG.Proof.Rsa.X86_64.rg w [aAcc, aTmp, aY] []) t₄.mem t₅.mem := Frm.rg_of_arrays ha₅ _ _ (by decide)
  have hw₅ : Ws t₅ B Z w := hw₄.congrG hf₅ (by simp) k₅ (by decide)
  -- `R mod n` into its array.
  refine WP.seq (WP.mono (copyA_ok hw₅ (o := aO) (a := aY) (by decide) (by decide) (by decide))
    fun t₆ ⟨hv₆, o₆, k₆⟩ => ?_)
  have hf₆ : Frm B (VG.Proof.Rsa.X86_64.rg w [aO] []) t₅.mem t₆.mem := Frm.rg_of_out o₆ (by omega) _ _ (by decide)
  have hw₆ : Ws t₆ B Z w := hw₅.congrG hf₆ (by simp) k₆ (by decide)
  rw [hY₅] at hv₆
  -- `n - R mod n`.
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86_64.subSet_ok hw₆ aN aO aNg) fun t₇ ⟨h12₇, h8₇, h10₇, hsi₇, hbp₇, m₇, k₇⟩ => ?_)
  have hs₇ := hw₆.scr.congr k₇.2.2
  refine WP.mono (VG.Proof.Rsa.X86_64.sub_ok hs₇ h8₇ h10₇ hsi₇ h12₇ hbp₇ (by omega) (by omega) (by have := hw₆.sl (j := aN) (by decide); omega)
    (by have := hw₆.sl (j := aO) (by decide); omega) (by have := hw₆.sl (j := aNg) (by decide); omega)
    (by have := slot_far (w := w) (show aNg ≠ aN by decide); omega)
    (by have := slot_far (w := w) (show aNg ≠ aO by decide); omega))
    fun t ⟨c, _, hv, o₈, k₈⟩ => ?_
  have hf₈ : Frm B (VG.Proof.Rsa.X86_64.rg w [aNg] []) t₆.mem t.mem := by
    rw [← m₇]; exact Frm.rg_of_out o₈ (by omega) _ _ (by decide)
  have k68 := k₇.trans k₈
  have hw₈ : Ws t B Z w := hw₆.congrG hf₈ (by simp) k68 (by decide)
  -- The values, through the later pieces.
  have hO₇ : wv t₆.mem B (VG.Proof.Bignum.X86_64.slot w aO) w = 2 ^ (64 * w) % N := hv₆
  have hN₆ : wv t₆.mem B (VG.Proof.Bignum.X86_64.slot w aN) w = N := by
    rw [hf₆.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega),
      hf₅.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega), hN₄]
  rw [m₇, hO₇, hN₆] at hv
  have hRN : 2 ^ (64 * w) % N < N := Nat.mod_lt _ (by omega)
  have hc0 : c = false := by
    cases c
    · rfl
    · have := wv_lt t.mem B (VG.Proof.Bignum.X86_64.slot w aNg) w
      simp only [Bool.toNat_true, Nat.mul_one] at hv
      omega
  subst hc0
  simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at hv
  have hR2₆ : wv t₆.mem B (VG.Proof.Bignum.X86_64.slot w aR2) w = wv t₂.mem B (VG.Proof.Bignum.X86_64.slot w aR2) w := by
    rw [hf₆.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega),
      hf₅.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega), hR2₄]
  have hOne₆ : wv t₆.mem B (VG.Proof.Bignum.X86_64.slot w aOne) w = 1 := by
    rw [hf₆.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega),
      hf₅.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega), hv₄]
    rfl
  refine ⟨hw₈, ?_, ?_, ?_, ?_, by omega, ?_, ?_⟩
  · rw [hf₈.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega), hR2₆]; exact hlt
  · rw [hf₈.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega), hR2₆]; exact hc
  · rw [hf₈.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega), hOne₆]
  · rw [hf₈.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega), hO₇]
  · have hf₂s : Frm B (VG.Proof.Rsa.X86_64.rg w [aAcc, aTmp, aR2] [sCnt]) s.mem t₂.mem := by rw [← m₁]; exact hf₂'
    have hf₄s : Frm B (VG.Proof.Rsa.X86_64.rg w [aOne] []) t₂.mem t₄.mem := by rw [← m₃]; exact hf₄
    have := ((hf₂s.rg_trans hf₄s).rg_trans hf₅).rg_trans hf₆
    exact (this.rg_trans hf₈).rg_mono (by decide) (by decide)
  · exact ((((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k₆).trans k68).mono (by decide)

end VG.Proof.Rsa.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rsa.X86_64.RpCst`. -/
section

/-!
# `vg_rsa_recover_primes` on x86-64: the candidates' constants

`Cst`: what the candidates read and never change: the working space,
`-n⁻¹`, `n`, `R² mod n`, 1, `R mod n` and `n - R mod n` (the Montgomery forms
of 1 and `-1`), `e`'s length, `r` and `t`. A piece that changes other arrays
and slots keeps it (`Cst.congr`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aR2 aXm aY aOne sCnt)

/-- The constants of the candidates, for `n = N`, `e_len = el`, and `m = 2^t r`. -/
structure Cst (s : State) (B : Addr) (Z w : Nat) (minv : BitVec 64) (N el r t : Nat) : Prop where
  ws : Ws s B Z w
  hmv : VG.Proof.Bignum.X86_64.word s.mem B (8 * sMinv) = minv
  hinv : ((VG.Proof.Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0
  hn : wv s.mem B (VG.Proof.Bignum.X86_64.slot w aN) w = N
  hr2lt : wv s.mem B (VG.Proof.Bignum.X86_64.slot w aR2) w < N
  hr2 : wv s.mem B (VG.Proof.Bignum.X86_64.slot w aR2) w % N = 2 ^ (64 * w) * 2 ^ (64 * w) % N
  hone : wv s.mem B (VG.Proof.Bignum.X86_64.slot w aOne) w = 1
  ho : wv s.mem B (VG.Proof.Bignum.X86_64.slot w aO) w = 2 ^ (64 * w) % N
  hng : wv s.mem B (VG.Proof.Bignum.X86_64.slot w aNg) w = N - 2 ^ (64 * w) % N
  hel : VG.Proof.Bignum.X86_64.word s.mem B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 el
  hm : wv s.mem B (VG.Proof.Bignum.X86_64.slot w aM) (w + (el + 7) / 8) = r
  ht : VG.Proof.Bignum.X86_64.word s.mem B (8 * sT) = BitVec.ofNat 64 t
  odd : N % 2 = 1
  lo : 2 ^ (64 * (w - 1)) ≤ N
  e1 : 1 ≤ el
  e2 : el ≤ 8 * w
  t1 : 1 ≤ t
  t2 : t < 64 * (w + (el + 7) / 8)

/-- The arrays the candidates keep. -/
def cArr : List Nat := [aN, aR2, aOne, aO, aNg, aM, aM + 1]

theorem Cst.congr {s u : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N el r t : Nat}
    (h : VG.Proof.Rsa.X86_64.Cst s B Z w minv N el r t) {js hs : List Nat} (hf : Frm B (VG.Proof.Rsa.X86_64.rg w js hs) s.mem u.mem)
    (hjs : ∀ j ∈ VG.Proof.Rsa.X86_64.cArr, j ∉ js) (hhs : ∀ i ∈ hs, rSlot i = true ∧ i ≠ sMinv ∧ i ≠ sT) {regs : List Reg}
    (k : VG.Proof.MlKem.X86_64.Keep regs s u) (hr : .rdi ∉ regs) : VG.Proof.Rsa.X86_64.Cst u B Z w minv N el r t := by
  have hw := h.ws
  have hZ16 : VG.Proof.Bignum.X86_64.slot w 16 ≤ 2 ^ 64 := by have := hw.scr.nowrap; have := hw.hZ; omega
  have h32 : ∀ i ∈ hs, i < 32 := fun i hi => by
    have := (hhs i hi).1; simp only [rSlot, Bool.or_eq_true, beq_iff_eq] at this; omega
  have hwv : ∀ j ∈ VG.Proof.Rsa.X86_64.cArr, j < 16 → wv u.mem B (VG.Proof.Bignum.X86_64.slot w j) w = wv s.mem B (VG.Proof.Bignum.X86_64.slot w j) w := fun j hj hj' =>
    hf.rg_wv hZ16 h32 hj' (hjs j hj) (by omega)
  have hsl : ∀ i, i < 32 → rSlot i = false → VG.Proof.Bignum.X86_64.word u.mem B (8 * i) = VG.Proof.Bignum.X86_64.word s.mem B (8 * i) := fun i hi hr =>
    hf.rg_word hi fun hm => by have := (hhs i hm).1; rw [hr] at this; cases this
  refine ⟨hw.congrG hf (fun i hi => (hhs i hi).1) k hr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    h.odd, h.lo, h.e1, h.e2, h.t1, h.t2⟩
  · rw [hf.rg_word (by decide) fun hm => (hhs _ hm).2.1 rfl]; exact h.hmv
  · rw [hf.rg_word0 hZ16 h32 (by decide) (hjs aN (by decide))]; exact h.hinv
  · rw [hwv aN (by decide) (by decide)]; exact h.hn
  · rw [hwv aR2 (by decide) (by decide)]; exact h.hr2lt
  · rw [hwv aR2 (by decide) (by decide)]; exact h.hr2
  · rw [hwv aOne (by decide) (by decide)]; exact h.hone
  · rw [hwv aO (by decide) (by decide)]; exact h.ho
  · rw [hwv aNg (by decide) (by decide)]; exact h.hng
  · rw [hsl _ (by decide) (by decide)]; exact h.hel
  · rw [hf.rg_wv2 hZ16 h32 (by decide) (hjs aM (by decide)) (hjs (aM + 1) (by decide))
      (by have := h.e2; omega)]; exact h.hm
  · rw [hf.rg_word (by decide) fun hm => (hhs _ hm).2.2 rfl]; exact h.ht

theorem Cst.hZ16 {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N el r t : Nat}
    (h : VG.Proof.Rsa.X86_64.Cst s B Z w minv N el r t) : VG.Proof.Bignum.X86_64.slot w 16 ≤ 2 ^ 64 := by
  have := h.ws.scr.nowrap; have := h.ws.hZ; omega

theorem Cst.good {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N el r t : Nat}
    (h : VG.Proof.Rsa.X86_64.Cst s B Z w minv N el r t) : VG.Proof.Bignum.X86_64.Good s B Z w minv ∧ VG.Proof.Bignum.X86_64.slot w 8 ≤ Z := by
  have := h.ws.good; rw [h.hmv] at this; exact this

theorem Cst.n1 {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N el r t : Nat}
    (h : VG.Proof.Rsa.X86_64.Cst s B Z w minv N el r t) : 2 ^ 64 ≤ N := by
  have := h.ws.w1
  have : 2 ^ 64 ≤ 2 ^ (64 * (w - 1)) := Nat.pow_le_pow_right (by decide) (by omega)
  have := h.lo
  omega

theorem Cst.coprime {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N el r t : Nat}
    (h : VG.Proof.Rsa.X86_64.Cst s B Z w minv N el r t) : Nat.Coprime (2 ^ (64 * w)) N :=
  VG.Proof.Bignum.coprime_pow2 h.odd _

end VG.Proof.Rsa.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rsa.X86_64.RpExp`. -/
section

/-!
# `vg_rsa_recover_primes` on x86-64: `y = g^r`

`expLoop`: for each word of `r` from the top, and each of its bits from the
top, `Y := Y² · (bit ? G : O)` in Montgomery form, the multiplicand chosen
by a mask: `Y ≡ g^r R` (`expLoop_ok`), for `G ≡ g R` and `Y ≡ R` on entry.
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aR2 aXm aY aOne sCnt)
open VG.Proof.Bignum (mont_cancel mont_sq)

/-! ## Bits -/

/-- The top bit of a word shifted left by `j`. -/
theorem top_bit {W j : Nat} (hj : j < 64) : W * 2 ^ j % 2 ^ 64 / 2 ^ 63 = W / 2 ^ (63 - j) % 2 := by
  have e1 : 2 ^ 64 = 2 ^ (64 - j) * 2 ^ j := by rw [← Nat.pow_add]; congr 1; omega
  have e2 : 2 ^ 63 = 2 ^ (63 - j) * 2 ^ j := by rw [← Nat.pow_add]; congr 1; omega
  have e3 : 2 ^ (64 - j) = 2 ^ (63 - j) * 2 := by rw [← Nat.pow_succ]; congr 1; omega
  rw [e1, Nat.mul_mod_mul_right, e2, Nat.mul_div_mul_right _ _ (Nat.two_pow_pos j), e3,
    Nat.mod_mul_right_div_self]

/-- Bit `63 - j` of word `i` of `r`. -/
theorem word_bit (r i : Nat) {j : Nat} (hj : j < 64) :
    r / 2 ^ (64 * i) % 2 ^ 64 / 2 ^ (63 - j) % 2 = r / 2 ^ (64 * i + (63 - j)) % 2 := by
  have e : 2 ^ 64 = 2 ^ (63 - j) * 2 ^ (j + 1) := by rw [← Nat.pow_add]; congr 1; omega
  rw [e, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (show 1 ≤ j + 1 by omega)),
    Nat.pow_one, Nat.div_div_eq_div_mul, ← Nat.pow_add]

/-- One more bit of `r`. -/
theorem prefix_step (r a : Nat) : r / 2 ^ a = 2 * (r / 2 ^ (a + 1)) + r / 2 ^ a % 2 := by
  rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]; omega

/-- One more bit of a word's prefix. -/
theorem prefix_step' (e : Nat) {j : Nat} (hj : j < 64) :
    e / 2 ^ (64 - (j + 1)) = 2 * (e / 2 ^ (64 - j)) + e / 2 ^ (63 - j) % 2 := by
  have := VG.Proof.Rsa.X86_64.prefix_step e (63 - j)
  rw [show 63 - j + 1 = 64 - j by omega, show 63 - j = 64 - (j + 1) by omega] at this
  rw [show 63 - j = 64 - (j + 1) by omega]
  exact this

/-- A Montgomery multiplication of `Y ≡ x^E R` by `X ≡ x^b R`. -/
theorem mont_mulp {Y Y' X x E b R m : Nat} (hR : Nat.Coprime R m) (hY : Y % m = x ^ E * R % m)
    (hX : X % m = x ^ b * R % m) (h : Y' * R % m = Y * X % m) : Y' % m = x ^ (E + b) * R % m := by
  apply mont_cancel hR
  rw [h, Nat.mul_mod, hY, hX, ← Nat.mul_mod, Nat.pow_add, Nat.mul_mul_mul_comm, Nat.mul_assoc (x ^ E * x ^ b)]

theorem shr63 (x : BitVec 64) : x >>> 63 = BitVec.ofNat 64 (x.toNat / 2 ^ 63) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (by have := x.isLt; omega)]

theorem bit_sub_one {b : Nat} (hb : b ≤ 1) : BitVec.ofNat 64 b - 1 = VG.Proof.Bignum.X86_64.mask (decide (b = 0)) := by
  rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl <;> decide

theorem dbl_mod (V : Nat) : BitVec.ofNat 64 V + BitVec.ofNat 64 V = BitVec.ofNat 64 (V * 2 % 2 ^ 64) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-! ## A bit -/

/-- `bitSel`: the top bit of `sC2` out of it, `rbp` the mask of it clear,
and the bases of the multiplicand and of `G`. -/
theorem bitSel_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {V : Nat}
    (hc2 : VG.Proof.Bignum.X86_64.word s.mem B (8 * sC2) = BitVec.ofNat 64 V) (hV : V < 2 ^ 64) :
    WP isa (.block bitSel) s fun t =>
      t.gpr .rbp = VG.Proof.Bignum.X86_64.mask (decide (V / 2 ^ 63 = 0)) ∧ t.gpr .r8 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w aXm) ∧
      t.gpr .rsi = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w aG) ∧ t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.mem = s.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * sC2)) (BitVec.ofNat 64 (V * 2 % 2 ^ 64)) ∧
      VG.Proof.MlKem.X86_64.Keep [.rax, .rdx, .rbp, .r12, .r9, .r8, .rsi] s t := by
  have h256 := h.h256
  have hn := h.scr.nowrap
  unfold bitSel
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rdx, .rbp] (Q := fun t => t.gpr .rbp = VG.Proof.Bignum.X86_64.mask (decide (V / 2 ^ 63 = 0)) ∧
      t.mem = s.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * sC2)) (BitVec.ofNat 64 (V * 2 % 2 ^ 64))) (by
    xrun [State.ea, hdr, h.rdi, hdrOff, h.scr.ld (d := 8 * sC2) (by simp only [sC2, sFn]; omega),
      h.scr.st (d := 8 * sC2) (by simp only [sC2, sFn]; omega), hc2, VG.Proof.Rsa.X86_64.shr63, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hV, VG.Proof.Rsa.X86_64.bit_sub_one (show V / 2 ^ 63 ≤ 1 by omega), VG.Proof.Rsa.X86_64.dbl_mod]) rfl)
    fun t₁ ⟨⟨hbp, m₁⟩, k₁⟩ => ?_
  have hw₁ : Ws t₁ B Z w := h.congrG (js := []) (hs := [sC2]) (by
    rw [m₁]; exact Frm.rg_of_hdr (VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (by simp only [sC2, sFn]; omega)) _ _
      (List.mem_singleton_self _)) (by decide) k₁ (by decide)
  refine WP.block_append_iff.mpr (WP.mono hw₁.ws_ok fun t₂ ⟨h12, h9, m₂, k₂⟩ => WP.block_append_iff.mpr ?_)
  have hdi₂ : t₂.gpr .rdi = B := (k₂.gpr (by decide)).trans hw₁.rdi
  refine WP.mono (base_ok aXm (r := .r8) (by decide) hdi₂ h9) fun t₃ ⟨h8, m₃, k₃⟩ => ?_
  refine WP.mono (base_ok aG (r := .rsi) (by decide) ((k₃.gpr (by decide)).trans hdi₂)
    ((k₃.gpr (by decide)).trans h9)) fun t ⟨hsi, m₄, k₄⟩ => ?_
  exact ⟨(k₄.gpr (by decide)).trans ((k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans hbp)),
    (k₄.gpr (by decide)).trans h8, hsi, (k₄.gpr (by decide)).trans ((k₃.gpr (by decide)).trans h12),
    by rw [m₄, m₃, m₂, m₁], (((k₁.trans k₂).trans k₃).trans k₄).mono (by decide)⟩

/-- Bit `63 - j` of a number's low word. -/
theorem low_bit (e : Nat) {j : Nat} (hj : j < 64) : e % 2 ^ 64 / 2 ^ (63 - j) % 2 = e / 2 ^ (63 - j) % 2 := by
  have := VG.Proof.Rsa.X86_64.word_bit e 0 hj
  simpa using this

/-- A counter in header slot `i`, decremented: `ZF` set when it reaches 0. -/
theorem ctrDec_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {i a : Nat} (hi : 16 ≤ i) (hi' : i < 32)
    (hc : VG.Proof.Bignum.X86_64.word s.mem B (8 * i) = BitVec.ofNat 64 a) (ha : 1 ≤ a) (ha' : a < 2 ^ 63) :
    WP isa (.block [.mov .rax (.mem (hdr i)), .alu .sub .rax (.imm 1), .store (hdr i) .rax]) s fun t =>
      t.zf = some (decide (a = 1)) ∧ t.mem = s.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * i)) (BitVec.ofNat 64 (a - 1)) ∧
      VG.Proof.MlKem.X86_64.Keep [.rax] s t := by
  have h256 := h.h256
  have e1 : BitVec.ofNat 64 a - 1 = BitVec.ofNat 64 (a - 1) := ofNat64_pred ha (by omega)
  have e2 : (BitVec.ofNat 64 a - 1 == 0) = decide (a = 1) := ofNat_sub_beq (N := 1) (by omega) (by omega)
  rw [e1] at e2
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.zf = some (decide (a = 1)) ∧
      t.mem = s.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * i)) (BitVec.ofNat 64 (a - 1))) (by
    xrun [State.ea, hdr, h.rdi, hdrOff, h.scr.ld (d := 8 * i) (by omega), h.scr.st (d := 8 * i) (by omega), hc,
      e2, e1]) rfl) fun t ⟨⟨hz, mt⟩, k⟩ => ⟨hz, mt, k⟩

/-- After `j` bits of `e`'s low word `V`, from `t₀`. -/
structure BitInv (t₀ : State) (B : Addr) (w N g e V j : Nat) (u : State) : Prop where
  frm : Frm B (VG.Proof.Rsa.X86_64.rg w [aAcc, aTmp, aXm, aY] [sC2, sC3]) t₀.mem u.mem
  keep : VG.Proof.MlKem.X86_64.Keep mmRegs t₀ u
  ylt : wv u.mem B (VG.Proof.Bignum.X86_64.slot w aY) w < N
  y : wv u.mem B (VG.Proof.Bignum.X86_64.slot w aY) w % N = g ^ (e / 2 ^ (64 - j)) * 2 ^ (64 * w) % N
  c2 : VG.Proof.Bignum.X86_64.word u.mem B (8 * sC2) = BitVec.ofNat 64 (V * 2 ^ j % 2 ^ 64)
  c3 : VG.Proof.Bignum.X86_64.word u.mem B (8 * sC3) = BitVec.ofNat 64 (64 - j)

theorem bit_hs : ∀ i ∈ [sC2, sC3], rSlot i = true ∧ i ≠ sMinv ∧ i ≠ sT := by decide

/-- A bit. -/
theorem bitBody_ok (M : Mont) {t₀ u : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N el r t g e V j : Nat}
    (hc : VG.Proof.Rsa.X86_64.Cst t₀ B Z w minv N el r t) (hGlt : wv t₀.mem B (VG.Proof.Bignum.X86_64.slot w aG) w < N)
    (hG : wv t₀.mem B (VG.Proof.Bignum.X86_64.slot w aG) w % N = g * 2 ^ (64 * w) % N) (hV : V = e % 2 ^ 64) (hj : j < 64)
    (hI : VG.Proof.Rsa.X86_64.BitInv t₀ B w N g e V j u) :
    WP isa (bitBody M.mm) u fun u' => u'.zf = some (decide (j + 1 = 64)) ∧ VG.Proof.Rsa.X86_64.BitInv t₀ B w N g e V (j + 1) u' := by
  have hZ16 := hc.hZ16
  have hw1 := hc.ws.w1
  have hw2 := hc.ws.w2
  have hR := hc.coprime
  have hcu : VG.Proof.Rsa.X86_64.Cst u B Z w minv N el r t := hc.congr hI.frm (by decide) VG.Proof.Rsa.X86_64.bit_hs hI.keep (by decide)
  have hGu : wv u.mem B (VG.Proof.Bignum.X86_64.slot w aG) w = wv t₀.mem B (VG.Proof.Bignum.X86_64.slot w aG) w :=
    hI.frm.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega)
  simp only [bitBody, seqs]
  -- The multiplicand `1`.
  refine WP.seq (WP.mono (copyA_ok hcu.ws (o := aXm) (a := aO) (by decide) (by decide) (by decide))
    fun u₁ ⟨hx₁, o₁, k₁⟩ => ?_)
  have hf₁ : Frm B (VG.Proof.Rsa.X86_64.rg w [aXm] []) u.mem u₁.mem := Frm.rg_of_out o₁ (by omega) _ _ (by decide)
  have hc₁ := hcu.congr hf₁ (by decide) (by simp) k₁ (by decide)
  rw [hcu.ho] at hx₁
  have hc2₁ : VG.Proof.Bignum.X86_64.word u₁.mem B (8 * sC2) = BitVec.ofNat 64 (V * 2 ^ j % 2 ^ 64) := by
    rw [hf₁.rg_word (by decide) (by simp)]; exact hI.c2
  -- The bit.
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86_64.bitSel_ok hc₁.ws hc2₁ (Nat.mod_lt _ (by decide)))
    fun u₂ ⟨hbp, h8, hsi, h12, m₂, k₂⟩ => ?_)
  have hf₂ : Frm B (VG.Proof.Rsa.X86_64.rg w [] [sC2]) u₁.mem u₂.mem := by
    rw [m₂]; exact Frm.rg_of_hdr (VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (by simp only [sC2, sFn]; omega)) _ _
      (List.mem_singleton_self _)
  have hc₂ := hc₁.congr hf₂ (by decide) (by decide) k₂ (by decide)
  have hs₂ := hc₂.ws.scr
  have sXm := hc₂.ws.sl (j := aXm) (by decide)
  have sG := hc₂.ws.sl (j := aG) (by decide)
  refine WP.seq (WP.mono (sel_ok hs₂ h8 hsi hbp h12 (by omega) (by omega) (by omega) (by omega)
    (by have := slot_far (w := w) (show aXm ≠ aG by decide); omega)) fun u₃ ⟨hx₃, o₃, k₃⟩ => ?_)
  have hf₃ : Frm B (VG.Proof.Rsa.X86_64.rg w [aXm] []) u₂.mem u₃.mem := Frm.rg_of_out o₃ (by omega) _ _ (by decide)
  have hc₃ := hc₂.congr hf₃ (by decide) (by simp) k₃ (by decide)
  -- The multiplicand: `G ≡ g R` or `R mod n ≡ g^0 R`.
  have hb : V * 2 ^ j % 2 ^ 64 / 2 ^ 63 = e / 2 ^ (63 - j) % 2 := by rw [VG.Proof.Rsa.X86_64.top_bit hj, hV, VG.Proof.Rsa.X86_64.low_bit e hj]
  have hX : wv u₃.mem B (VG.Proof.Bignum.X86_64.slot w aXm) w % N = g ^ (e / 2 ^ (63 - j) % 2) * 2 ^ (64 * w) % N ∧
      wv u₃.mem B (VG.Proof.Bignum.X86_64.slot w aXm) w < N := by
    rw [hx₃, hf₂.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega), hx₁,
      hf₂.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega),
      hf₁.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega), hGu, hb]
    have hNp : 0 < N := by have := hc.n1; omega
    rcases Nat.mod_two_eq_zero_or_one (e / 2 ^ (63 - j)) with h0 | h1
    · simp only [h0, decide_true, ite_true, Nat.pow_zero, Nat.one_mul, Nat.mod_mod]
      exact ⟨trivial, Nat.mod_lt _ hNp⟩
    · simp only [h1, Nat.one_ne_zero, decide_false, Bool.false_eq_true, ite_false, Nat.pow_one]
      exact ⟨hG, hGlt⟩
  have hY₃ : wv u₃.mem B (VG.Proof.Bignum.X86_64.slot w aY) w = wv u.mem B (VG.Proof.Bignum.X86_64.slot w aY) w := by
    rw [hf₃.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega),
      hf₂.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega),
      hf₁.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega)]
  -- `Y := Y²`.
  have hg₃ := hc₃.good
  refine WP.seq (WP.mono (M.mm_ok hg₃.1 hg₃.2 hw1 (by omega) (o := aY) (a := aY) (b := aY) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc₃.hinv
    (by rw [hY₃, hc₃.hn]; exact hI.ylt)) fun u₄ ⟨hg₄, hlt₄, hm₄, ha₄, k₄⟩ => ?_)
  rw [hc₃.hn] at hlt₄ hm₄
  have hf₄ : Frm B (VG.Proof.Rsa.X86_64.rg w [aAcc, aTmp, aY] []) u₃.mem u₄.mem := Frm.rg_of_arrays ha₄ _ _ (by decide)
  have hc₄ := hc₃.congr hf₄ (by decide) (by simp) k₄ (by decide)
  have hY₄ : wv u₄.mem B (VG.Proof.Bignum.X86_64.slot w aY) w % N = g ^ (2 * (e / 2 ^ (64 - j))) * 2 ^ (64 * w) % N :=
    mont_sq hR (by rw [hY₃]; exact hI.y) hm₄
  -- `Y := Y · X`.
  have hX₄ : wv u₄.mem B (VG.Proof.Bignum.X86_64.slot w aXm) w = wv u₃.mem B (VG.Proof.Bignum.X86_64.slot w aXm) w :=
    hf₄.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega)
  have hg₄' := hc₄.good
  refine WP.seq (WP.mono (M.mm_ok hg₄'.1 hg₄'.2 hw1 (by omega) (o := aY) (a := aY) (b := aXm) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc₄.hinv
    (by rw [hX₄, hc₄.hn]; exact hX.2)) fun u₅ ⟨hg₅, hlt₅, hm₅, ha₅, k₅⟩ => ?_)
  rw [hc₄.hn] at hlt₅ hm₅
  have hf₅ : Frm B (VG.Proof.Rsa.X86_64.rg w [aAcc, aTmp, aY] []) u₄.mem u₅.mem := Frm.rg_of_arrays ha₅ _ _ (by decide)
  have hc₅ := hc₄.congr hf₅ (by decide) (by simp) k₅ (by decide)
  have hY₅ := VG.Proof.Rsa.X86_64.mont_mulp hR hY₄ (by rw [hX₄]; exact hX.1) hm₅
  rw [← VG.Proof.Rsa.X86_64.prefix_step' e hj] at hY₅
  -- The bits left.
  have hc3₅ : VG.Proof.Bignum.X86_64.word u₅.mem B (8 * sC3) = BitVec.ofNat 64 (64 - j) := by
    rw [hf₅.rg_word (by decide) (by simp), hf₄.rg_word (by decide) (by simp), hf₃.rg_word (by decide) (by simp),
      hf₂.rg_word (by decide) (by decide), hf₁.rg_word (by decide) (by simp)]; exact hI.c3
  refine WP.mono (VG.Proof.Rsa.X86_64.ctrDec_ok hc₅.ws (i := sC3) (by decide) (by decide) hc3₅ (by omega) (by omega))
    fun u' ⟨hz, m₆, k₆⟩ => ⟨by rw [hz]; congr 1; exact decide_eq_decide.mpr (by omega), ?_⟩
  have hf₆ : Frm B (VG.Proof.Rsa.X86_64.rg w [] [sC3]) u₅.mem u'.mem := by
    rw [m₆]; exact Frm.rg_of_hdr (VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (by simp only [sC3, sFn]; omega)) _ _
      (List.mem_singleton_self _)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (((((((hI.frm.rg_trans hf₁).rg_trans hf₂).rg_trans hf₃).rg_trans hf₄).rg_trans hf₅).rg_trans
      hf₆).rg_mono (by decide) (by decide))
  · exact ((((((hI.keep.trans k₁).trans k₂).trans k₃).trans k₄).trans k₅).trans k₆).mono (by decide)
  · rw [hf₆.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega)]; exact hlt₅
  · rw [hf₆.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega)]; exact hY₅
  · rw [hf₆.rg_word (by decide) (by decide), hf₅.rg_word (by decide) (by simp),
      hf₄.rg_word (by decide) (by simp), hf₃.rg_word (by decide) (by simp), m₂, VG.Proof.Bignum.X86_64.word_writeW_self]
    congr 1
    rw [show 2 ^ (j + 1) = 2 ^ j * 2 from Nat.pow_succ .., ← Nat.mul_assoc, Nat.mod_mul_mod]
  · rw [m₆, VG.Proof.Bignum.X86_64.word_writeW_self]; congr 1

/-! ## A word -/

/-- `wordHead`: word `i` of `M` into `sC2`, for `sC1 = i + 1`, and 64 bits
left in `sC3`. -/
theorem wordHead_ok {u : State} {B : Addr} {Z w : Nat} (h : Ws u B Z w) {i : Nat}
    (hc1 : VG.Proof.Bignum.X86_64.word u.mem B (8 * sC1) = BitVec.ofNat 64 (i + 1)) (hi : VG.Proof.Bignum.X86_64.slot w aM + 8 * i + 8 ≤ Z) (hi' : i + 1 < 2 ^ 63) :
    WP isa (.block wordHead) u fun u' =>
      u'.mem = (u.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * sC2)) (VG.Proof.Bignum.X86_64.word u.mem B (VG.Proof.Bignum.X86_64.slot w aM + 8 * i))).writeW (VG.Proof.Bignum.X86_64.off B (8 * sC3))
        (BitVec.ofNat 64 64) ∧ VG.Proof.MlKem.X86_64.Keep [.r12, .r9, .rbx, .rax] u u' := by
  have h256 := h.h256
  unfold wordHead
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono h.ws_ok fun u₁ ⟨_, h9, m₁, k₁⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (base_ok aM (r := .rbx) (by decide) ((k₁.gpr (by decide)).trans h.rdi) h9)
    fun u₂ ⟨hbx, m₂, k₂⟩ => ?_
  have k12 := k₁.trans k₂
  have hs₂ := h.scr.congr k12.2.2
  have hdi₂ : u₂.gpr .rdi = B := (k12.gpr (by decide)).trans h.rdi
  have e1 : BitVec.ofNat 64 (i + 1) - 1 = BitVec.ofNat 64 i := by
    rw [ofNat64_pred (by omega) (by omega)]; rfl
  refine WP.mono (WP.keep [.rax] (Q := fun u' => u'.mem =
      (u.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * sC2)) (VG.Proof.Bignum.X86_64.word u.mem B (VG.Proof.Bignum.X86_64.slot w aM + 8 * i))).writeW (VG.Proof.Bignum.X86_64.off B (8 * sC3))
        (BitVec.ofNat 64 64)) (by
    xrun [State.ea, hdr, hdi₂, hdrOff, hs₂.ld (d := 8 * sC1) (by simp only [sC1, sCnt, sFn]; omega),
      hs₂.st (d := 8 * sC2) (by simp only [sC2, sFn]; omega), hs₂.st (d := 8 * sC3) (by simp only [sC3, sFn]; omega),
      m₂, m₁, hc1, e1, ix, addr0 hbx rfl, hs₂.ld (d := VG.Proof.Bignum.X86_64.slot w aM + 8 * i) hi]
    rfl) rfl) fun u' ⟨mt, k₃⟩ => ⟨mt, (k12.trans k₃).mono (by decide)⟩

/-- After `k` words of `r` (from the top), from `t₀`. -/
structure WordInv (t₀ : State) (B : Addr) (w N g r Bw k : Nat) (u : State) : Prop where
  frm : Frm B (VG.Proof.Rsa.X86_64.rg w [aAcc, aTmp, aXm, aY] [sC1, sC2, sC3]) t₀.mem u.mem
  keep : VG.Proof.MlKem.X86_64.Keep mmRegs t₀ u
  ylt : wv u.mem B (VG.Proof.Bignum.X86_64.slot w aY) w < N
  y : wv u.mem B (VG.Proof.Bignum.X86_64.slot w aY) w % N = g ^ (r / 2 ^ (64 * (Bw - k))) * 2 ^ (64 * w) % N
  c1 : VG.Proof.Bignum.X86_64.word u.mem B (8 * sC1) = BitVec.ofNat 64 (Bw - k)

theorem word_hs : ∀ i ∈ [sC1, sC2, sC3], rSlot i = true ∧ i ≠ sMinv ∧ i ≠ sT := by decide

/-- A word. -/
theorem wordStep_ok (M : Mont) {t₀ u : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N el r t g k : Nat}
    (hc : VG.Proof.Rsa.X86_64.Cst t₀ B Z w minv N el r t) (hGlt : wv t₀.mem B (VG.Proof.Bignum.X86_64.slot w aG) w < N)
    (hG : wv t₀.mem B (VG.Proof.Bignum.X86_64.slot w aG) w % N = g * 2 ^ (64 * w) % N) (hk : k < w + (el + 7) / 8)
    (hI : VG.Proof.Rsa.X86_64.WordInv t₀ B w N g r (w + (el + 7) / 8) k u) :
    WP isa (.seq (.block wordHead) (.seq (.loop (bitBody M.mm) .ne) (.block wordNext))) u fun u' =>
      u'.zf = some (decide (k + 1 = w + (el + 7) / 8)) ∧ VG.Proof.Rsa.X86_64.WordInv t₀ B w N g r (w + (el + 7) / 8) (k + 1) u' := by
  have hZ16 := hc.hZ16
  have he2 := hc.e2
  have hw2 := hc.ws.w2
  obtain ⟨Bw, hBw⟩ : ∃ Bw, w + (el + 7) / 8 = Bw := ⟨_, rfl⟩
  have hm := hc.hm
  rw [hBw] at hk hI hm ⊢
  have hBw2 : Bw ≤ 2 * (w + 2) := by omega
  have hcu : VG.Proof.Rsa.X86_64.Cst u B Z w minv N el r t := hc.congr hI.frm (by decide) VG.Proof.Rsa.X86_64.word_hs hI.keep (by decide)
  obtain ⟨i, hi⟩ : ∃ i, Bw - k = i + 1 := ⟨Bw - k - 1, by omega⟩
  have hc1 := hI.c1
  rw [hi] at hc1
  have sM := slot_lt (w := w) (show aM + 1 < 16 by decide)
  have eM1 : VG.Proof.Bignum.X86_64.slot w (aM + 1) = VG.Proof.Bignum.X86_64.slot w aM + 8 * (w + 2) := by simp only [VG.Proof.Bignum.X86_64.slot, hdrBytes, aM]; omega
  have hZ := hcu.ws.hZ
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86_64.wordHead_ok hcu.ws hc1 (by omega) (by omega)) fun u₁ ⟨m₁, k₁⟩ => ?_)
  -- The word.
  have hW : (VG.Proof.Bignum.X86_64.word u.mem B (VG.Proof.Bignum.X86_64.slot w aM + 8 * i)).toNat = r / 2 ^ (64 * i) % 2 ^ 64 := by
    have := word_of_wv u.mem B (VG.Proof.Bignum.X86_64.slot w aM) Bw (q := i) (by omega)
    have hmu := hcu.hm
    rw [hBw] at hmu
    rw [hmu] at this
    exact this
  have hf₁ : Frm B (VG.Proof.Rsa.X86_64.rg w [] [sC2, sC3]) u.mem u₁.mem := by
    rw [m₁]
    exact (Frm.rg_of_hdr (VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (by simp only [sC2, sFn]; omega)) [] [sC2, sC3] (by decide)).trans
      (Frm.rg_of_hdr (VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (by simp only [sC3, sFn]; omega)) [] [sC2, sC3] (by decide))
  have hc₁ := hcu.congr hf₁ (by decide) (by decide) k₁ (by decide)
  have hGu : wv u₁.mem B (VG.Proof.Bignum.X86_64.slot w aG) w = wv t₀.mem B (VG.Proof.Bignum.X86_64.slot w aG) w := by
    rw [hf₁.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega),
      hI.frm.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega)]
  -- The bits of the word.
  have hpow : r / 2 ^ (64 * i) / 2 ^ (64 - 0) = r / 2 ^ (64 * (Bw - k)) := by
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, hi, Nat.sub_zero, Nat.mul_succ]
  have hW' : VG.Proof.Bignum.X86_64.word u.mem B (VG.Proof.Bignum.X86_64.slot w aM + 8 * i) = BitVec.ofNat 64 (r / 2 ^ (64 * i) % 2 ^ 64 * 2 ^ 0 % 2 ^ 64) := by
    rw [← hW, Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt (BitVec.isLt _), BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hB0 : VG.Proof.Rsa.X86_64.BitInv u₁ B w N g (r / 2 ^ (64 * i)) (r / 2 ^ (64 * i) % 2 ^ 64) 0 u₁ := by
    refine ⟨Frm.refl _ _ _, Keep.refl _ _, ?_, ?_, ?_, ?_⟩
    · rw [hf₁.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega)]; exact hI.ylt
    · rw [hf₁.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega), hpow]; exact hI.y
    · rw [m₁, (VG.Proof.Bignum.X86_64.writeW_outside _ B _ (d := 8 * sC3) (by simp only [sC3, sFn]; omega)).word
        (Or.inl (by simp only [sC2, sC3, sFn]; omega)) (by simp only [sC2, sFn]; omega), VG.Proof.Bignum.X86_64.word_writeW_self, hW']
    · rw [m₁, VG.Proof.Bignum.X86_64.word_writeW_self]
  refine WP.seq (wp_upto (a := 0) (N := 64) (by decide) (VG.Proof.Rsa.X86_64.BitInv u₁ B w N g (r / 2 ^ (64 * i)) (r / 2 ^ (64 * i) % 2 ^ 64))
    (fun j _ hj v hv => VG.Proof.Rsa.X86_64.bitBody_ok M hc₁ (by rw [hGu]; exact hGlt) (by rw [hGu]; exact hG) rfl hj hv)
    (fun v hv => ?_) hB0)
  have hc₂ := hc₁.congr hv.frm (by decide) VG.Proof.Rsa.X86_64.bit_hs hv.keep (by decide)
  have hc1₂ : VG.Proof.Bignum.X86_64.word v.mem B (8 * sC1) = BitVec.ofNat 64 (i + 1) := by
    rw [hv.frm.rg_word (by decide) (by decide), hf₁.rg_word (by decide) (by decide)]; exact hc1
  refine WP.mono (VG.Proof.Rsa.X86_64.ctrDec_ok hc₂.ws (i := sC1) (by decide) (by decide) hc1₂ (by omega) (by omega))
    fun u' ⟨hz, m₃, k₃⟩ => ⟨by rw [hz]; congr 1; exact decide_eq_decide.mpr (by omega), ?_⟩
  have hf₃ : Frm B (VG.Proof.Rsa.X86_64.rg w [] [sC1]) v.mem u'.mem := by
    rw [m₃]; exact Frm.rg_of_hdr (VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (by simp only [sC1, sCnt, sFn]; omega)) _ _
      (List.mem_singleton_self _)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (((hI.frm.rg_trans hf₁).rg_trans hv.frm).rg_trans hf₃).rg_mono (by decide) (by decide)
  · exact (((hI.keep.trans k₁).trans hv.keep).trans k₃).mono (by decide)
  · rw [hf₃.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega)]; exact hv.ylt
  · rw [hf₃.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega), show Bw - (k + 1) = i by omega]
    have := hv.y
    rwa [Nat.sub_self, Nat.pow_zero, Nat.div_one] at this
  · rw [m₃, VG.Proof.Bignum.X86_64.word_writeW_self, show Bw - (k + 1) = i by omega, Nat.add_sub_cancel]

/-! ## The exponentiation -/

/-- `expLoop`: `Y ≡ g^r R`, from `Y = R mod n` and `G ≡ g R`. -/
theorem expLoop_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N el r t g : Nat}
    (hc : VG.Proof.Rsa.X86_64.Cst s B Z w minv N el r t) (hGlt : wv s.mem B (VG.Proof.Bignum.X86_64.slot w aG) w < N)
    (hG : wv s.mem B (VG.Proof.Bignum.X86_64.slot w aG) w % N = g * 2 ^ (64 * w) % N) (hY : wv s.mem B (VG.Proof.Bignum.X86_64.slot w aY) w = 2 ^ (64 * w) % N) :
    WP isa (VG.Impl.Rsa.X86_64.Keys.Recover.expLoop M.mm) s fun u => Frm B (VG.Proof.Rsa.X86_64.rg w [aAcc, aTmp, aXm, aY] [sC1, sC2, sC3]) s.mem u.mem ∧
      VG.Proof.MlKem.X86_64.Keep mmRegs s u ∧ wv u.mem B (VG.Proof.Bignum.X86_64.slot w aY) w < N ∧
      wv u.mem B (VG.Proof.Bignum.X86_64.slot w aY) w % N = g ^ r * 2 ^ (64 * w) % N := by
  have hZ16 := hc.hZ16
  have he2 := hc.e2
  have hw1 := hc.ws.w1
  have hw2 := hc.ws.w2
  have h256 := hc.ws.h256
  have hN : 0 < N := by have := hc.n1; omega
  unfold VG.Impl.Rsa.X86_64.Keys.Recover.expLoop VG.Impl.Rsa.X86_64.Keys.Recover.expInit
  refine WP.seq (WP.mono (Q := fun (u : State) => u.mem = s.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * sC1))
      (BitVec.ofNat 64 (w + (el + 7) / 8)) ∧ VG.Proof.MlKem.X86_64.Keep mmRegs s u)
    (WP.block_append_iff.mpr (WP.mono (VG.Proof.Rsa.X86_64.bw_ok hc.ws hc.hel (by omega)) fun s₁ ⟨hax, m₁, k₁⟩ => ?_))
    fun s₁ ⟨m₁, k₁⟩ => ?_)
  · have hs₁ := hc.ws.scr.congr k₁.2.2
    have hdi₁ : s₁.gpr .rdi = B := (k₁.gpr (by decide)).trans hc.ws.rdi
    refine WP.mono (WP.keep [] (Q := fun u => u.mem = s.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * sC1))
        (BitVec.ofNat 64 (w + (el + 7) / 8))) (by
      xrun [State.ea, hdr, hdi₁, hdrOff, hs₁.st (d := 8 * sC1) (by simp only [sC1, sCnt, sFn]; omega), hax, m₁])
      rfl) fun u ⟨mu, k₂⟩ => ⟨mu, (k₁.trans k₂).mono (by decide)⟩
  have hf₁ : Frm B (VG.Proof.Rsa.X86_64.rg w [] [sC1]) s.mem s₁.mem := by
    rw [m₁]; exact Frm.rg_of_hdr (VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (by simp only [sC1, sCnt, sFn]; omega)) _ _
      (List.mem_singleton_self _)
  have hr : r < 2 ^ (64 * (w + (el + 7) / 8)) := hc.hm ▸ wv_lt _ _ _ _
  have h0 : VG.Proof.Rsa.X86_64.WordInv s B w N g r (w + (el + 7) / 8) 0 s₁ := by
    refine ⟨hf₁.rg_mono (by decide) (by decide), k₁, ?_, ?_, ?_⟩
    · rw [hf₁.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega), hY]; exact Nat.mod_lt _ hN
    · rw [hf₁.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega), hY, Nat.sub_zero,
        Nat.div_eq_of_lt hr, Nat.pow_zero, Nat.one_mul, Nat.mod_mod]
    · rw [m₁, VG.Proof.Bignum.X86_64.word_writeW_self, Nat.sub_zero]
  refine wp_upto (a := 0) (N := w + (el + 7) / 8) (by omega) (VG.Proof.Rsa.X86_64.WordInv s B w N g r (w + (el + 7) / 8))
    (fun k _ hk u hu => VG.Proof.Rsa.X86_64.wordStep_ok M hc hGlt hG hk hu) (fun u hu => ?_) h0
  refine ⟨hu.frm, hu.keep, hu.ylt, ?_⟩
  have := hu.y
  rwa [Nat.sub_self, Nat.mul_zero, Nat.pow_zero, Nat.div_one] at this

end VG.Proof.Rsa.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rsa.X86_64.RpSq`. -/
section

/-!
# `vg_rsa_recover_primes` on x86-64: the squarings

`sqBody`: `x = y²` (in Montgomery form), the masks of `x = 1` and `x = -1`,
and `sqLogic` updates `done`, `ok` and `y` as `RecoverMath.sqStep` does
(`sqBody_ok`); the loop of `64 Bw` of them gives `sqIter` (`sqLoop_ok`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aR2 aXm aY aOne sCnt sMask)
open VG.Proof.Bignum (mont_cancel mont_sq)

theorem mask_or (a b : Bool) : VG.Proof.Bignum.X86_64.mask a ||| mask b = VG.Proof.Bignum.X86_64.mask (a || b) := by
  cases a <;> cases b <;> rfl

theorem mask_not (a : Bool) : VG.Proof.Bignum.X86_64.mask a ^^^ BitVec.signExtend 64 (BitVec.ofInt 32 (-1)) = VG.Proof.Bignum.X86_64.mask (!a) := by
  cases a <;> rfl

theorem sbb_mask (c : Bool) : 0#64 - BitVec.setWidth 64 (BitVec.ofBool c) = VG.Proof.Bignum.X86_64.mask c := rfl

theorem xor_lt_one (a b : BitVec 64) : decide ((a ^^^ b).toNat < (1 : BitVec 64).toNat) = decide (a = b) := by
  rw [decide_lt_one']
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_iff]
  constructor
  · intro h; exact BitVec.xor_eq_zero_iff.mp h
  · intro h; rw [h, BitVec.xor_self]; rfl

/-- `eqStore i`: the mask of `rbp = 0` into header slot `i`. -/
theorem eqStore_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {i : Nat} (hi : 16 ≤ i) (hi' : i < 32) :
    WP isa (.block (eqStore i)) s fun u =>
      u.mem = s.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * i)) (VG.Proof.Bignum.X86_64.mask (decide (s.gpr .rbp = 0))) ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rbp] s u := by
  have h256 := h.h256
  refine WP.mono (WP.keep [.rax, .rbp] (Q := fun u => u.mem = s.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * i))
      (VG.Proof.Bignum.X86_64.mask (decide (s.gpr .rbp = 0)))) (by
    unfold eqStore
    xrun [State.ea, hdr, h.rdi, hdrOff, h.scr.st (d := 8 * i) (by omega), decide_lt_one', VG.Proof.Rsa.X86_64.sbb_mask]) rfl)
    fun u ⟨a, b⟩ => ⟨a, b⟩

/-- `sqNext`: `k += 1` in `sC1`, against `64 Bw`. -/
theorem sqNext_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {el k : Nat}
    (hel : VG.Proof.Bignum.X86_64.word s.mem B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 el) (hel' : el < 2 ^ 32)
    (hc1 : VG.Proof.Bignum.X86_64.word s.mem B (8 * sC1) = BitVec.ofNat 64 k) (hk : k < 64 * (w + (el + 7) / 8)) :
    WP isa (.block sqNext) s fun u =>
      u.zf = some (decide (k + 1 = 64 * (w + (el + 7) / 8))) ∧
      u.mem = s.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * sC1)) (BitVec.ofNat 64 (k + 1)) ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rdx] s u := by
  have h256 := h.h256
  have hw2 := h.w2
  unfold sqNext
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun u => u.gpr .rdx = BitVec.ofNat 64 (k + 1) ∧
      u.mem = s.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * sC1)) (BitVec.ofNat 64 (k + 1))) (by
    xrun [State.ea, hdr, h.rdi, hdrOff, h.scr.ld (d := 8 * sC1) (by simp only [sC1, sCnt, sFn]; omega),
      h.scr.st (d := 8 * sC1) (by simp only [sC1, sCnt, sFn]; omega), hc1, ofNat_add_one]) rfl)
    fun u₁ ⟨⟨hdx, m₁⟩, k₁⟩ => WP.block_append_iff.mpr ?_
  have hf₁ : Frm B (VG.Proof.Rsa.X86_64.rg w [] [sC1]) s.mem u₁.mem := by
    rw [m₁]; exact Frm.rg_of_hdr (VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (by simp only [sC1, sCnt, sFn]; omega)) _ _
      (List.mem_singleton_self _)
  have hw₁ : Ws u₁ B Z w := h.congrG hf₁ (by decide) k₁ (by decide)
  refine WP.mono (VG.Proof.Rsa.X86_64.bw_ok hw₁ (by rw [hf₁.rg_word (by decide) (by decide)]; exact hel) hel')
    fun u₂ ⟨hax, m₂, k₂⟩ => ?_
  have hdx₂ : u₂.gpr .rdx = BitVec.ofNat 64 (k + 1) := (k₂.gpr (by decide)).trans hdx
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun u => u.zf = some (decide (k + 1 = 64 * (w + (el + 7) / 8))) ∧
      u.mem = u₂.mem) (by
    simp only [List.replicate, List.cons_append, List.nil_append]
    xrun [hax, hdx₂, VG.Proof.Rsa.X86_64.ofNat_dbl, VG.Proof.Rsa.X86_64.dbl6, ofNat_sub_beq (show k + 1 < 2 ^ 64 by omega)
      (show 64 * (w + (el + 7) / 8) < 2 ^ 64 by omega)]) rfl)
    fun u ⟨⟨hz, mu⟩, k₃⟩ => ⟨hz, by rw [mu, m₂, m₁], ((k₁.trans k₂).trans k₃).mono (by decide)⟩

/-! ## The squaring's arithmetic -/

theorem mont_inj {x y R N : Nat} (hR : Nat.Coprime R N) (hx : x < N) (hy : y < N)
    (h : x * R % N = y * R % N) : x = y := by
  have := mont_cancel hR h
  rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this

theorem mod_ne_zero_of_coprime {R N : Nat} (hR : Nat.Coprime R N) (hN : 1 < N) : R % N ≠ 0 := by
  intro h
  have := Nat.Coprime.eq_one_of_dvd hR.symm (Nat.dvd_of_mod_eq_zero h)
  omega

/-- `-1` in Montgomery form. -/
theorem neg_one_mont {R N : Nat} (hR : Nat.Coprime R N) (hN : 1 < N) : (N - 1) * R % N = N - R % N := by
  have ha := VG.Proof.Rsa.X86_64.mod_ne_zero_of_coprime hR hN
  have hlt := Nat.mod_lt R (show 0 < N by omega)
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, R % (M + 1) = b + 1 := ⟨R % (M + 1) - 1, by omega⟩
  have hR' := Nat.div_add_mod R (M + 1)
  rw [hb] at hR' hlt ⊢
  have e : M * R = (M + 1) * (M * (R / (M + 1)) + b) + (M - b) := by
    conv => lhs; rw [← hR']
    rw [Nat.mul_add, Nat.mul_succ, Nat.mul_left_comm M (M + 1), Nat.mul_add (M + 1), Nat.succ_mul M b]
    omega
  rw [Nat.add_sub_cancel, e, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  omega

/-- `x = 1` and `x = -1` from Montgomery forms. -/
theorem eq_one_mont {X x R N : Nat} (hR : Nat.Coprime R N) (hN : 1 < N) (hx : x < N) (hX : X = x * R % N) :
    X = R % N ↔ x = 1 := by
  subst hX
  constructor
  · intro h; exact VG.Proof.Rsa.X86_64.mont_inj hR hx hN (by rw [h, Nat.one_mul])
  · intro h; rw [h, Nat.one_mul]

theorem eq_neg_mont {X x R N : Nat} (hR : Nat.Coprime R N) (hN : 1 < N) (hx : x < N) (hX : X = x * R % N) :
    X = N - R % N ↔ x = N - 1 := by
  subst hX
  rw [← VG.Proof.Rsa.X86_64.neg_one_mont hR hN]
  constructor
  · intro h; exact VG.Proof.Rsa.X86_64.mont_inj hR hx (by omega) h
  · intro h; rw [h]

/-- `sqLogic`'s masks, for `sC1 = k`, `t`, `done`, `ok`, `x = 1` (`e1`) and
`x = -1` (`em`, from `rbp`): `done` and `ok` updated, and `rbp` the mask of
not continuing. -/
theorem sqMasks_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {k t : Nat} {done ok e1 em : Bool}
    (hk : k < 2 ^ 62) (ht : t < 2 ^ 62)
    (hc1 : VG.Proof.Bignum.X86_64.word s.mem B (8 * sC1) = BitVec.ofNat 64 k) (hT : VG.Proof.Bignum.X86_64.word s.mem B (8 * sT) = BitVec.ofNat 64 t)
    (hc2 : VG.Proof.Bignum.X86_64.word s.mem B (8 * sC2) = VG.Proof.Bignum.X86_64.mask done) (hc3 : VG.Proof.Bignum.X86_64.word s.mem B (8 * sC3) = VG.Proof.Bignum.X86_64.mask ok)
    (hm : VG.Proof.Bignum.X86_64.word s.mem B (8 * sMask) = VG.Proof.Bignum.X86_64.mask e1) (hbp : decide (s.gpr .rbp = 0) = em) :
    WP isa (.block (sqLogic.take 29)) s fun u =>
      u.gpr .rbp = VG.Proof.Bignum.X86_64.mask (!((!done && decide (k < t)) && !e1 && !(em || decide (k + 1 = t)))) ∧
      u.mem = (s.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * sC2))
        (VG.Proof.Bignum.X86_64.mask (done || ((!done && decide (k < t)) && (e1 || (em || decide (k + 1 = t))))))).writeW
          (VG.Proof.Bignum.X86_64.off B (8 * sC3)) (VG.Proof.Bignum.X86_64.mask (ok || ((!done && decide (k < t)) && e1))) ∧
      VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rdx, .r15, .rbp] s u := by
  have h256 := h.h256
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi => h.scr.ld (by omega)
  have hs : ∀ i < 32, InRegions s.wr (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi => h.scr.st (by omega)
  have ek : (BitVec.ofNat 64 k).toNat = k := by rw [BitVec.toNat_ofNat]; omega
  have et : (BitVec.ofNat 64 t).toNat = t := by rw [BitVec.toNat_ofNat]; omega
  have ekt : decide (BitVec.ofNat 64 k + 1 ^^^ BitVec.ofNat 64 t = 0) = decide (k + 1 = t) := by
    rw [ofNat_add_one]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_iff]
    constructor
    · intro e
      have := congrArg BitVec.toNat (BitVec.xor_eq_zero_iff.mp e)
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this; omega
    · intro e; rw [e]; exact BitVec.xor_self
  have hr3 : ∀ v, (s.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * sC2)) v).readW (VG.Proof.Bignum.X86_64.off B (8 * sC3)) 64 = VG.Proof.Bignum.X86_64.mask ok := fun v => by
    have := (VG.Proof.Bignum.X86_64.writeW_outside s.mem B v (d := 8 * sC2) (by simp only [sC2, sFn]; omega)).word
      (d := 8 * sC3) (Or.inr (by simp only [sC2, sC3, sFn]; omega)) (by simp only [sC3, sFn]; omega)
    rw [hc3] at this
    exact this
  refine WP.mono (WP.keep [.rax, .rcx, .rdx, .r15, .rbp] (Q := fun u =>
      u.gpr .rbp = VG.Proof.Bignum.X86_64.mask (!((!done && decide (k < t)) && !e1 && !(em || decide (k + 1 = t)))) ∧
      u.mem = (s.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * sC2))
        (VG.Proof.Bignum.X86_64.mask (done || ((!done && decide (k < t)) && (e1 || (em || decide (k + 1 = t))))))).writeW
          (VG.Proof.Bignum.X86_64.off B (8 * sC3)) (VG.Proof.Bignum.X86_64.mask (ok || ((!done && decide (k < t)) && e1)))) ?_ (by decide))
    fun u ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩
  simp only [sqLogic, List.take, List.cons_append]
  xrun [State.ea, hdr, h.rdi, hdrOff, hl _ (show sC1 < 32 by decide), hl _ (show sT < 32 by decide),
    hl _ (show sC2 < 32 by decide), hl _ (show sC3 < 32 by decide), hl _ (show sMask < 32 by decide),
    hs _ (show sC2 < 32 by decide), hs _ (show sC3 < 32 by decide), hc1, hT, hc2, hc3, hm, decide_lt_one', hbp,
    VG.Proof.Rsa.X86_64.sbb_mask, mask_and', VG.Proof.Rsa.X86_64.mask_or, VG.Proof.Rsa.X86_64.mask_not, VG.Proof.Rsa.X86_64.xor_lt_one, ek, et, ekt, hr3]
  generalize decide (k < t) = a
  generalize decide (k + 1 = t) = b
  cases a <;> cases b <;> cases done <;> cases ok <;> cases e1 <;> cases em <;> exact ⟨rfl, rfl⟩

/-- `ws ++ base a .r8 ++ base b .rsi`. -/
theorem bases2_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) (a b : Nat) :
    WP isa (.block (VG.Impl.Rsa.X86_64.Keys.ws ++ base a .r8 ++ base b .rsi)) s fun t =>
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .r8 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w a) ∧ t.gpr .rsi = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w b) ∧
      t.mem = s.mem ∧ VG.Proof.MlKem.X86_64.Keep [.r12, .r9, .r8, .rsi] s t := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono h.ws_ok fun t₁ ⟨h12, h9, m₁, k₁⟩ => WP.block_append_iff.mpr ?_
  have hdi₁ : t₁.gpr .rdi = B := (k₁.gpr (by decide)).trans h.rdi
  refine WP.mono (base_ok a (r := .r8) (by decide) hdi₁ h9) fun t₂ ⟨h8, m₂, k₂⟩ => ?_
  refine WP.mono (base_ok b (r := .rsi) (by decide) ((k₂.gpr (by decide)).trans hdi₁)
    ((k₂.gpr (by decide)).trans h9)) fun t ⟨hsi, m₃, k₃⟩ => ⟨?_, ?_, hsi, by rw [m₃, m₂, m₁],
      ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  · exact (k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans h12)
  · exact (k₃.gpr (by decide)).trans h8

theorem sqLogic_eq : sqLogic = sqLogic.take 29 ++ (VG.Impl.Rsa.X86_64.Keys.ws ++ base aY .r8 ++ base aX .rsi) := rfl

/-- After `k` squarings from `st₀`, from `t₀`: `y` in Montgomery form in
`Y`, and `done` and `ok`. -/
structure SqI (t₀ : State) (B : Addr) (w N tt : Nat) (st₀ : Nat × Bool × Bool) (k : Nat) (u : State) : Prop where
  frm : Frm B (VG.Proof.Rsa.X86_64.rg w [aAcc, aTmp, aX, aY] [sMask, sC1, sC2, sC3]) t₀.mem u.mem
  keep : VG.Proof.MlKem.X86_64.Keep mmRegs t₀ u
  y : wv u.mem B (VG.Proof.Bignum.X86_64.slot w aY) w = (sqIter N tt k st₀).1 * 2 ^ (64 * w) % N
  ylt : (sqIter N tt k st₀).1 < N
  c1 : VG.Proof.Bignum.X86_64.word u.mem B (8 * sC1) = BitVec.ofNat 64 k
  c2 : VG.Proof.Bignum.X86_64.word u.mem B (8 * sC2) = VG.Proof.Bignum.X86_64.mask (sqIter N tt k st₀).2.1
  c3 : VG.Proof.Bignum.X86_64.word u.mem B (8 * sC3) = VG.Proof.Bignum.X86_64.mask (sqIter N tt k st₀).2.2

theorem sq_hs : ∀ i ∈ [sMask, sC1, sC2, sC3], rSlot i = true ∧ i ≠ sMinv ∧ i ≠ sT := by decide

/-- The square in Montgomery form. -/
theorem sq_mont {X Y y R N : Nat} (hR : Nat.Coprime R N) (hY : Y = y * R % N) (hX : X < N)
    (h : X * R % N = Y * Y % N) : X = y * y % N * R % N := by
  have e : X % N = y * y % N * R % N := by
    apply mont_cancel hR
    rw [h, hY, ← Nat.mul_mod, Nat.mul_assoc (y * y % N), Nat.mod_mul_mod, Nat.mul_mul_mul_comm]
  rwa [Nat.mod_eq_of_lt hX] at e

/-- A squaring. -/
theorem sqBody_ok (M : Mont) {t₀ u : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N el r t k : Nat}
    {st₀ : Nat × Bool × Bool} (hc : VG.Proof.Rsa.X86_64.Cst t₀ B Z w minv N el r t) (hk : k < 64 * (w + (el + 7) / 8))
    (hI : VG.Proof.Rsa.X86_64.SqI t₀ B w N t st₀ k u) :
    WP isa (sqBody M.mm) u fun u' =>
      u'.zf = some (decide (k + 1 = 64 * (w + (el + 7) / 8))) ∧ VG.Proof.Rsa.X86_64.SqI t₀ B w N t st₀ (k + 1) u' := by
  have hZ16 := hc.hZ16
  have hw1 := hc.ws.w1
  have hw2 := hc.ws.w2
  have he2 := hc.e2
  have ht2 := hc.t2
  have hR := hc.coprime
  have hN1 : 1 < N := by have := hc.n1; omega
  have hcu : VG.Proof.Rsa.X86_64.Cst u B Z w minv N el r t := hc.congr hI.frm (by decide) VG.Proof.Rsa.X86_64.sq_hs hI.keep (by decide)
  have hy := hI.y
  have hylt := hI.ylt
  have hc2 := hI.c2
  have hc3 := hI.c3
  have hc1 := hI.c1
  have hst : sqIter N t (k + 1) st₀ = sqStep N t k (sqIter N t k st₀) := rfl
  generalize sqIter N t k st₀ = st at hy hylt hc2 hc3 hst
  obtain ⟨y, done, ok⟩ := st
  dsimp only at hy hylt hc2 hc3
  have hYlt : wv u.mem B (VG.Proof.Bignum.X86_64.slot w aY) w < N := by rw [hy]; exact Nat.mod_lt _ (by omega)
  rw [show sqBody M.mm = seqs ([copyA aX aY, M.mm aX aX aY] ++ (eqA aX aO ++ ([.block (eqStore sMask)] ++
    (eqA aX aNg ++ [.block sqLogic, wordLoop 0 VG.Impl.Rsa.X86_64.Keys.selBody, .block sqNext])))) by
      simp only [sqBody, List.append_assoc]]
  refine wp_seqs_append (by simp) (by simp) ?_
  simp only [seqs]
  -- `x = y²`.
  refine WP.seq (WP.mono (copyA_ok hcu.ws (o := aX) (a := aY) (by decide) (by decide) (by decide))
    fun u₁ ⟨hx₁, o₁, k₁⟩ => ?_)
  have hf₁ : Frm B (VG.Proof.Rsa.X86_64.rg w [aX] []) u.mem u₁.mem := Frm.rg_of_out o₁ (by omega) _ _ (by decide)
  have hc₁ := hcu.congr hf₁ (by decide) (by simp) k₁ (by decide)
  have hY₁ : wv u₁.mem B (VG.Proof.Bignum.X86_64.slot w aY) w = wv u.mem B (VG.Proof.Bignum.X86_64.slot w aY) w :=
    hf₁.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega)
  have hg₁ := hc₁.good
  refine WP.mono (M.mm_ok hg₁.1 hg₁.2 hw1 (by omega) (o := aX) (a := aX) (b := aY) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc₁.hinv
    (by rw [hY₁, hc₁.hn]; exact hYlt)) fun u₂ ⟨_, hlt₂, hm₂, ha₂, k₂⟩ => ?_
  rw [hc₁.hn] at hlt₂ hm₂
  rw [hx₁, hY₁] at hm₂
  have hX₂ : wv u₂.mem B (VG.Proof.Bignum.X86_64.slot w aX) w = y * y % N * 2 ^ (64 * w) % N := VG.Proof.Rsa.X86_64.sq_mont hR hy hlt₂ hm₂
  have hf₂ : Frm B (VG.Proof.Rsa.X86_64.rg w [aAcc, aTmp, aX] []) u₁.mem u₂.mem := Frm.rg_of_arrays ha₂ _ _ (by decide)
  have hc₂ := hc₁.congr hf₂ (by decide) (by simp) k₂ (by decide)
  have hxN : y * y % N < N := Nat.mod_lt _ (by omega)
  -- `x = 1`.
  refine wp_seqs_append (by simp [eqA]) (by simp) (WP.mono (eqA_ok hc₂.ws (a := aX) (b := aO) (by decide)
    (by decide)) fun u₃ ⟨hz₃, m₃, k₃⟩ => ?_)
  rw [hX₂, hc₂.ho, VG.Proof.Rsa.X86_64.eq_one_mont hR hN1 hxN rfl] at hz₃
  have hc₃ := hc₂.congr (js := []) (hs := []) (by rw [m₃]; exact Frm.refl _ _ _) (by simp) (by simp) k₃ (by decide)
  refine wp_seqs_append (by simp) (by simp) (WP.mono (VG.Proof.Rsa.X86_64.eqStore_ok hc₃.ws (i := sMask) (by decide) (by decide))
    fun u₄ ⟨m₄, k₄⟩ => ?_)
  have he1 : decide (u₃.gpr .rbp = 0) = decide (y * y % N = 1) := decide_eq_decide.mpr hz₃
  rw [he1] at m₄
  have hf₄ : Frm B (VG.Proof.Rsa.X86_64.rg w [] [sMask]) u₃.mem u₄.mem := by
    rw [m₄]; exact Frm.rg_of_hdr (VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (by simp only [sMask, sFn]; omega)) _ _
      (List.mem_singleton_self _)
  have hc₄ := hc₃.congr hf₄ (by decide) (by decide) k₄ (by decide)
  -- `x = -1`.
  have hX₄ : wv u₄.mem B (VG.Proof.Bignum.X86_64.slot w aX) w = wv u₂.mem B (VG.Proof.Bignum.X86_64.slot w aX) w := by
    rw [hf₄.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega), m₃]
  refine wp_seqs_append (by simp [eqA]) (by simp) (WP.mono (eqA_ok hc₄.ws (a := aX) (b := aNg) (by decide)
    (by decide)) fun u₅ ⟨hz₅, m₅, k₅⟩ => ?_)
  rw [hX₄, hX₂, hc₄.hng, VG.Proof.Rsa.X86_64.eq_neg_mont hR hN1 hxN rfl] at hz₅
  have hc₅ := hc₄.congr (js := []) (hs := []) (by rw [m₅]; exact Frm.refl _ _ _) (by simp) (by simp) k₅ (by decide)
  have hem : decide (u₅.gpr .rbp = 0) = decide (y * y % N = N - 1) := decide_eq_decide.mpr hz₅
  -- The masks.
  have hw5 : ∀ i, i < 32 → i ≠ sMask → VG.Proof.Bignum.X86_64.word u₅.mem B (8 * i) = VG.Proof.Bignum.X86_64.word u.mem B (8 * i) := fun i hi hne => by
    rw [m₅, hf₄.rg_word hi (by simpa using hne), m₃, hf₂.rg_word hi (by simp), hf₁.rg_word hi (by simp)]
  have hm₅ : VG.Proof.Bignum.X86_64.word u₅.mem B (8 * sMask) = VG.Proof.Bignum.X86_64.mask (decide (y * y % N = 1)) := by rw [m₅, m₄, VG.Proof.Bignum.X86_64.word_writeW_self]
  simp only [seqs]
  rw [VG.Proof.Rsa.X86_64.sqLogic_eq]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (VG.Proof.Rsa.X86_64.sqMasks_ok hc₅.ws (k := k) (t := t) (done := done) (ok := ok) (by omega) (by omega)
    (by rw [hw5 _ (by decide) (by decide)]; exact hc1) hc₅.ht (by rw [hw5 _ (by decide) (by decide)]; exact hc2)
    (by rw [hw5 _ (by decide) (by decide)]; exact hc3) hm₅ hem) fun u₆ ⟨hbp₆, m₆, k₆⟩ => ?_))
  have hf₆ : Frm B (VG.Proof.Rsa.X86_64.rg w [] [sC2, sC3]) u₅.mem u₆.mem := by
    rw [m₆]
    exact (Frm.rg_of_hdr (VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (by simp only [sC2, sFn]; omega)) [] [sC2, sC3] (by decide)).trans
      (Frm.rg_of_hdr (VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (by simp only [sC3, sFn]; omega)) [] [sC2, sC3] (by decide))
  have hc₆ := hc₅.congr hf₆ (by decide) (by decide) k₆ (by decide)
  refine WP.mono (VG.Proof.Rsa.X86_64.bases2_ok hc₆.ws aY aX) fun u₇ ⟨h12, h8, hsi, m₇, k₇⟩ => ?_
  have hc₇ := hc₆.congr (js := []) (hs := []) (by rw [m₇]; exact Frm.refl _ _ _) (by simp) (by simp) k₇ (by decide)
  have hbp₇ : u₇.gpr .rbp = _ := (k₇.gpr (by decide)).trans hbp₆
  -- `y := x` if the squarings continue.
  have sY := hc₇.ws.sl (j := aY) (by decide)
  have sX := hc₇.ws.sl (j := aX) (by decide)
  refine WP.seq (WP.mono (sel_ok hc₇.ws.scr h8 hsi hbp₇ h12 (by omega) (by omega) (by omega) (by omega)
    (by have := slot_far (w := w) (show aY ≠ aX by decide); omega)) fun u₈ ⟨hy₈, o₈, k₈⟩ => ?_)
  have hf₈ : Frm B (VG.Proof.Rsa.X86_64.rg w [aY] []) u₇.mem u₈.mem := Frm.rg_of_out o₈ (by omega) _ _ (by decide)
  have hc₈ := hc₇.congr hf₈ (by decide) (by simp) k₈ (by decide)
  -- `k += 1`.
  have hc1₈ : VG.Proof.Bignum.X86_64.word u₈.mem B (8 * sC1) = BitVec.ofNat 64 k := by
    rw [hf₈.rg_word (by decide) (by simp), m₇, hf₆.rg_word (by decide) (by decide),
      hw5 _ (by decide) (by decide)]; exact hc1
  refine WP.mono (VG.Proof.Rsa.X86_64.sqNext_ok hc₈.ws hc₈.hel (by omega) hc1₈ hk) fun u' ⟨hz, m₉, k₉⟩ => ⟨hz, ?_⟩
  have hf₉ : Frm B (VG.Proof.Rsa.X86_64.rg w [] [sC1]) u₈.mem u'.mem := by
    rw [m₉]; exact Frm.rg_of_hdr (VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (by simp only [sC1, sCnt, sFn]; omega)) _ _
      (List.mem_singleton_self _)
  have hfu₅ : Frm B (VG.Proof.Rsa.X86_64.rg w [aX, aAcc, aTmp, aX] [sMask]) u.mem u₅.mem := by
    have := ((hf₁.rg_trans hf₂).rg_trans (js' := []) (hs' := [])
      (by rw [m₃]; exact Frm.refl _ _ _ : Frm B (rg w [] []) u₂.mem u₃.mem)).rg_trans hf₄
    rw [← m₅] at this
    exact this.rg_mono (by decide) (by decide)
  -- The values after the squaring.
  have hY₈ : wv u₈.mem B (VG.Proof.Bignum.X86_64.slot w aY) w = (if !((!done && decide (k < t)) && !decide (y * y % N = 1) &&
      !(decide (y * y % N = N - 1) || decide (k + 1 = t))) then y else y * y % N) * 2 ^ (64 * w) % N := by
    rw [hy₈, m₇, hf₆.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega),
      hf₆.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega), m₅, hX₄,
      hf₄.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega), m₃,
      hf₂.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega), hY₁, hy, hX₂]
    split <;> rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (((((hI.frm.rg_trans hfu₅).rg_trans hf₆).rg_trans (by rw [m₇]; exact Frm.refl _ _ _ :
      Frm B (rg w [] []) u₆.mem u₇.mem)).rg_trans hf₈).rg_trans hf₉).rg_mono (by decide) (by decide)
  · exact ((((((((((hI.keep.trans k₁).trans k₂).trans k₃).trans k₄).trans k₅).trans k₆).trans k₇).trans k₈).trans
      k₉).mono (by decide))
  · rw [hst, hf₉.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega), hY₈]
    simp only [sqStep]
    by_cases hcnd : ((!done && decide (k < t)) && !decide (y * y % N = 1) &&
        !(decide (y * y % N = N - 1) || decide (k + 1 = t))) = true
    · simp only [hcnd, Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
    · simp only [Bool.not_eq_true] at hcnd
      simp only [hcnd, Bool.not_false, ite_true, Bool.false_eq_true, ite_false]
  · rw [hst]
    simp only [sqStep]
    split <;> omega
  · rw [m₉, VG.Proof.Bignum.X86_64.word_writeW_self]
  · rw [hf₉.rg_word (by decide) (by decide), hf₈.rg_word (by decide) (by simp), m₇, m₆]
    rw [(VG.Proof.Bignum.X86_64.writeW_outside _ B _ (d := 8 * sC3) (by simp only [sC3, sFn]; omega)).word
      (Or.inl (by simp only [sC2, sC3, sFn]; omega)) (by simp only [sC2, sFn]; omega), VG.Proof.Bignum.X86_64.word_writeW_self, hst]
    simp only [sqStep]
  · rw [hf₉.rg_word (by decide) (by decide), hf₈.rg_word (by decide) (by simp), m₇, m₆, VG.Proof.Bignum.X86_64.word_writeW_self, hst]
    simp only [sqStep]

end VG.Proof.Rsa.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rsa.X86_64.RpCand`. -/
section

/-!
# `vg_rsa_recover_primes` on x86-64: a candidate

`candBody` for the candidate `g = c + 2`: `y = g^r mod n` (`candA_ok`), the
start of the squarings from it (`candB_ok`), the squarings and the count of
the candidates (`candBody_ok`): `recoverStep n t r g`, the mask of whether it
found `y`, `y` in Montgomery form if so, and `ZF` set to stop if it did or
if it was the last.
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aR2 aXm aY aOne sCnt sMask)
open VG.Proof.Bignum (mont_cancel mont_sq powMod_eq)
open VG.Spec.Rsa (powMod recoverStep)

/-- `gBlk`: `g = c + 2` into `rdx`, `rcx := 0` and `w` into `r12`. -/
theorem gBlk_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {c : Nat}
    (hcand : VG.Proof.Bignum.X86_64.word s.mem B (8 * sCand) = BitVec.ofNat 64 c) :
    WP isa (.block gBlk) s fun u =>
      u.gpr .rdx = BitVec.ofNat 64 (c + 2) ∧ u.gpr .rcx = BitVec.ofNat 64 0 ∧ u.gpr .r12 = BitVec.ofNat 64 w ∧
      u.mem = s.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rdx, .rcx, .r12] s u := by
  have h256 := h.h256
  have e2 : BitVec.ofNat 64 c + 2 = BitVec.ofNat 64 (c + 2) := by
    rw [show (2 : BitVec 64) = BitVec.ofNat 64 2 from rfl, BitVec.ofNat_add_ofNat]
  refine WP.mono (WP.keep [.rdx, .rcx, .r12] (Q := fun u => u.gpr .rdx = BitVec.ofNat 64 (c + 2) ∧
      u.gpr .rcx = BitVec.ofNat 64 0 ∧ u.gpr .r12 = BitVec.ofNat 64 w ∧ u.mem = s.mem) (by
    unfold gBlk
    xrun [State.ea, hdr, h.rdi, hdrOff, h.scr.ld (d := 8 * sCand) (by simp only [sCand, Impl.Bignum.X86_64.Public.sV, sFn]; omega),
      h.scr.ld (d := 8 * sW) (by simp only [sW]; omega), hcand, h.hw, e2]) rfl)
    fun u ⟨⟨a, b, c, d⟩, k⟩ => ⟨a, b, c, d, k⟩

/-- `g R` from `R² mod n`. -/
theorem g_mont {X g R R2 N : Nat} (hR : Nat.Coprime R N) (hr2 : R2 % N = R * R % N)
    (h : X * R % N = g * R2 % N) : X % N = g * R % N := by
  apply mont_cancel hR
  rw [h, Nat.mul_mod, hr2, ← Nat.mul_mod, Nat.mul_assoc]

/-- The candidate's `y = g^r mod n`, in Montgomery form in `Y`. -/
theorem candA_ok (M : Mont) {u : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N el r t c : Nat}
    (hc : VG.Proof.Rsa.X86_64.Cst u B Z w minv N el r t) (hcand : VG.Proof.Bignum.X86_64.word u.mem B (8 * sCand) = BitVec.ofNat 64 c) (hc100 : c < 100) :
    WP isa (seqs [.block gBlk, setWord aX .rcx, M.mm aXm aX aR2, copyA aG aXm, copyA aY aO, VG.Impl.Rsa.X86_64.Keys.Recover.expLoop M.mm]) u
      fun u' => Frm B (VG.Proof.Rsa.X86_64.rg w [aX, aAcc, aTmp, aXm, aG, aY] [sC1, sC2, sC3]) u.mem u'.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs u u' ∧
        wv u'.mem B (VG.Proof.Bignum.X86_64.slot w aY) w = powMod (c + 2) r N * 2 ^ (64 * w) % N := by
  have hZ16 := hc.hZ16
  have hw1 := hc.ws.w1
  have hw2 := hc.ws.w2
  have hR := hc.coprime
  have hN : 2 ^ 64 ≤ N := hc.n1
  simp only [seqs]
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86_64.gBlk_ok hc.ws hcand) fun u₁ ⟨hdx, hcx, h12, m₁, k₁⟩ => ?_)
  have hc₁ := hc.congr (js := []) (hs := []) (by rw [m₁]; exact Frm.refl _ _ _) (by simp) (by simp) k₁ (by decide)
  have hg₁ := hc₁.good
  refine WP.seq (WP.mono (setWord_ok hc₁.ws.scr hc₁.ws.rdi hg₁.1.hdr hg₁.2 h12 (by omega) (by omega)
    (o := aX) (by decide) (ri := .rcx) (by decide) (i := 0) (by omega) hcx) fun u₂ ⟨hx₂, o₂, k₂⟩ => ?_)
  rw [hdx, BitVec.toNat_ofNat, Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt (by omega)] at hx₂
  have hf₂ : Frm B (VG.Proof.Rsa.X86_64.rg w [aX] []) u₁.mem u₂.mem := Frm.rg_of_out o₂ (Nat.le_refl _) _ _ (by decide)
  have hc₂ := hc₁.congr hf₂ (by decide) (by simp) k₂ (by decide)
  have hg₂ := hc₂.good
  -- `g R mod n`.
  refine WP.seq (WP.mono (M.mm_ok hg₂.1 hg₂.2 hw1 (by omega) (o := aXm) (a := aX) (b := aR2) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc₂.hinv
    (by rw [hc₂.hn]; exact hc₂.hr2lt)) fun u₃ ⟨_, hlt₃, hm₃, ha₃, k₃⟩ => ?_)
  rw [hc₂.hn] at hlt₃ hm₃
  rw [hx₂] at hm₃
  have hXm : wv u₃.mem B (VG.Proof.Bignum.X86_64.slot w aXm) w % N = (c + 2) * 2 ^ (64 * w) % N := VG.Proof.Rsa.X86_64.g_mont hR hc₂.hr2 hm₃
  have hf₃ : Frm B (VG.Proof.Rsa.X86_64.rg w [aAcc, aTmp, aXm] []) u₂.mem u₃.mem := Frm.rg_of_arrays ha₃ _ _ (by decide)
  have hc₃ := hc₂.congr hf₃ (by decide) (by simp) k₃ (by decide)
  refine WP.seq (WP.mono (copyA_ok hc₃.ws (o := aG) (a := aXm) (by decide) (by decide) (by decide))
    fun u₄ ⟨hg₄, o₄, k₄⟩ => ?_)
  have hf₄ : Frm B (VG.Proof.Rsa.X86_64.rg w [aG] []) u₃.mem u₄.mem := Frm.rg_of_out o₄ (by omega) _ _ (by decide)
  have hc₄ := hc₃.congr hf₄ (by decide) (by simp) k₄ (by decide)
  refine WP.seq (WP.mono (copyA_ok hc₄.ws (o := aY) (a := aO) (by decide) (by decide) (by decide))
    fun u₅ ⟨hy₅, o₅, k₅⟩ => ?_)
  have hf₅ : Frm B (VG.Proof.Rsa.X86_64.rg w [aY] []) u₄.mem u₅.mem := Frm.rg_of_out o₅ (by omega) _ _ (by decide)
  have hc₅ := hc₄.congr hf₅ (by decide) (by simp) k₅ (by decide)
  rw [hc₄.ho] at hy₅
  have hG₅ : wv u₅.mem B (VG.Proof.Bignum.X86_64.slot w aG) w = wv u₃.mem B (VG.Proof.Bignum.X86_64.slot w aXm) w := by
    rw [hf₅.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega), hg₄]
  refine WP.mono (VG.Proof.Rsa.X86_64.expLoop_ok M hc₅ (g := c + 2) (by rw [hG₅]; exact hlt₃) (by rw [hG₅]; exact hXm) hy₅)
    fun u' ⟨hf₆, k₆, hlt₆, hy₆⟩ => ⟨?_, ?_, ?_⟩
  · have hf₁ : Frm B (VG.Proof.Rsa.X86_64.rg w [] []) u.mem u₁.mem := by rw [m₁]; exact Frm.refl _ _ _
    exact (((((hf₁.rg_trans hf₂).rg_trans hf₃).rg_trans hf₄).rg_trans hf₅).rg_trans hf₆).rg_mono
      (by decide) (by decide)
  · exact (((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k₆).mono (by decide)
  · rw [← Nat.mod_eq_of_lt hlt₆, hy₆, powMod_eq, Nat.mod_mul_mod]

/-- `chkBlk`: `done := y = -1 ∨ y = 1`, `ok := 0` and `k := 0`. -/
theorem chkBlk_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {e1 : Bool}
    (hc2 : VG.Proof.Bignum.X86_64.word s.mem B (8 * sC2) = VG.Proof.Bignum.X86_64.mask e1) :
    WP isa (.block chkBlk) s fun u =>
      u.mem = ((s.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * sC2)) (VG.Proof.Bignum.X86_64.mask (decide (s.gpr .rbp = 0) || e1))).writeW (VG.Proof.Bignum.X86_64.off B (8 * sC3))
        (VG.Proof.Bignum.X86_64.mask false)).writeW (VG.Proof.Bignum.X86_64.off B (8 * sC1)) (VG.Proof.Bignum.X86_64.mask false) ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rbp] s u := by
  have h256 := h.h256
  refine WP.mono (WP.keep [.rax, .rbp] (Q := fun u => u.mem = ((s.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * sC2))
      (VG.Proof.Bignum.X86_64.mask (decide (s.gpr .rbp = 0) || e1))).writeW (VG.Proof.Bignum.X86_64.off B (8 * sC3)) (VG.Proof.Bignum.X86_64.mask false)).writeW (VG.Proof.Bignum.X86_64.off B (8 * sC1))
        (VG.Proof.Bignum.X86_64.mask false)) (by
    unfold chkBlk
    xrun [State.ea, hdr, h.rdi, hdrOff, h.scr.ld (d := 8 * sC2) (by simp only [sC2, sFn]; omega),
      h.scr.st (d := 8 * sC2) (by simp only [sC2, sFn]; omega), h.scr.st (d := 8 * sC3) (by simp only [sC3, sFn]; omega),
      h.scr.st (d := 8 * sC1) (by simp only [sC1, sCnt, sFn]; omega), hc2, decide_lt_one', VG.Proof.Rsa.X86_64.sbb_mask, VG.Proof.Rsa.X86_64.mask_or]
    rfl) rfl) fun u ⟨a, b⟩ => ⟨a, b⟩

/-- The start of the squarings from `y` in Montgomery form in `Y`. -/
theorem candB_ok {u : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N el r t y : Nat}
    (hc : VG.Proof.Rsa.X86_64.Cst u B Z w minv N el r t) (hY : wv u.mem B (VG.Proof.Bignum.X86_64.slot w aY) w = y * 2 ^ (64 * w) % N) (hy : y < N) :
    WP isa (seqs (eqA aY aO ++ (([.block (eqStore sC2)] : List (Prog isa)) ++ (eqA aY aNg ++ ([.block chkBlk] : List (Prog isa)))))) u fun u' =>
      Frm B (VG.Proof.Rsa.X86_64.rg w [] [sC1, sC2, sC3]) u.mem u'.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs u u' ∧
      VG.Proof.Bignum.X86_64.word u'.mem B (8 * sC2) = VG.Proof.Bignum.X86_64.mask (sqStart N y).2.1 ∧ VG.Proof.Bignum.X86_64.word u'.mem B (8 * sC3) = VG.Proof.Bignum.X86_64.mask (sqStart N y).2.2 ∧
      VG.Proof.Bignum.X86_64.word u'.mem B (8 * sC1) = BitVec.ofNat 64 0 := by
  have hR := hc.coprime
  have hN1 : 1 < N := by have := hc.n1; omega
  have h256 := hc.ws.h256
  refine wp_seqs_append (by simp [eqA]) (by simp) (WP.mono (eqA_ok hc.ws (a := aY) (b := aO) (by decide)
    (by decide)) fun u₁ ⟨hz₁, m₁, k₁⟩ => ?_)
  rw [hY, hc.ho, VG.Proof.Rsa.X86_64.eq_one_mont hR hN1 hy rfl] at hz₁
  have hc₁ := hc.congr (js := []) (hs := []) (by rw [m₁]; exact Frm.refl _ _ _) (by simp) (by simp) k₁ (by decide)
  refine wp_seqs_append (by simp) (by simp) (WP.mono (VG.Proof.Rsa.X86_64.eqStore_ok hc₁.ws (i := sC2) (by decide) (by decide))
    fun u₂ ⟨m₂, k₂⟩ => ?_)
  rw [show decide (u₁.gpr .rbp = 0) = decide (y = 1) from decide_eq_decide.mpr hz₁] at m₂
  have hf₂ : Frm B (VG.Proof.Rsa.X86_64.rg w [] [sC2]) u₁.mem u₂.mem := by
    rw [m₂]; exact Frm.rg_of_hdr (VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (by simp only [sC2, sFn]; omega)) _ _
      (List.mem_singleton_self _)
  have hc₂ := hc₁.congr hf₂ (by decide) (by decide) k₂ (by decide)
  have hY₂ : wv u₂.mem B (VG.Proof.Bignum.X86_64.slot w aY) w = y * 2 ^ (64 * w) % N := by
    rw [hf₂.rg_wv hc.hZ16 (by decide) (by decide) (by decide) (by omega), m₁, hY]
  refine wp_seqs_append (by simp [eqA]) (by simp) (WP.mono (eqA_ok hc₂.ws (a := aY) (b := aNg) (by decide)
    (by decide)) fun u₃ ⟨hz₃, m₃, k₃⟩ => ?_)
  rw [hY₂, hc₂.hng, VG.Proof.Rsa.X86_64.eq_neg_mont hR hN1 hy rfl] at hz₃
  have hc₃ := hc₂.congr (js := []) (hs := []) (by rw [m₃]; exact Frm.refl _ _ _) (by simp) (by simp) k₃ (by decide)
  refine WP.mono (VG.Proof.Rsa.X86_64.chkBlk_ok hc₃.ws (e1 := decide (y = 1)) (by rw [m₃, m₂, VG.Proof.Bignum.X86_64.word_writeW_self]))
    fun u' ⟨m₄, k₄⟩ => ?_
  rw [show decide (u₃.gpr .rbp = 0) = decide (y = N - 1) from decide_eq_decide.mpr hz₃] at m₄
  have hf₄ : Frm B (VG.Proof.Rsa.X86_64.rg w [] [sC1, sC2, sC3]) u₃.mem u'.mem := by
    rw [m₄]
    exact ((Frm.rg_of_hdr (VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (by simp only [sC2, sFn]; omega)) [] [sC1, sC2, sC3] (by decide)).trans
      (Frm.rg_of_hdr (VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (by simp only [sC3, sFn]; omega)) [] [sC1, sC2, sC3] (by decide))).trans
      (Frm.rg_of_hdr (VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (by simp only [sC1, sCnt, sFn]; omega)) [] [sC1, sC2, sC3] (by decide))
  have hw3 : ∀ m : Mem, ∀ v₁ v₂ : BitVec 64, VG.Proof.Bignum.X86_64.word ((m.writeW (VG.Proof.Bignum.X86_64.off B (8 * sC3)) v₁).writeW (VG.Proof.Bignum.X86_64.off B (8 * sC1)) v₂) B
      (8 * sC2) = VG.Proof.Bignum.X86_64.word m B (8 * sC2) := fun m v₁ v₂ => by
    rw [(VG.Proof.Bignum.X86_64.writeW_outside _ B _ (d := 8 * sC1) (by simp only [sC1, sCnt, sFn]; omega)).word
      (Or.inr (by simp only [sC1, sC2, sCnt, sFn]; omega)) (by simp only [sC2, sFn]; omega),
      (VG.Proof.Bignum.X86_64.writeW_outside _ B _ (d := 8 * sC3) (by simp only [sC3, sFn]; omega)).word
      (Or.inl (by simp only [sC2, sC3, sFn]; omega)) (by simp only [sC2, sFn]; omega)]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hf₁ : Frm B (VG.Proof.Rsa.X86_64.rg w [] []) u.mem u₁.mem := by rw [m₁]; exact Frm.refl _ _ _
    have hf₃ : Frm B (VG.Proof.Rsa.X86_64.rg w [] []) u₂.mem u₃.mem := by rw [m₃]; exact Frm.refl _ _ _
    exact (((hf₁.rg_trans hf₂).rg_trans hf₃).rg_trans hf₄).rg_mono (by decide) (by decide)
  · exact (((k₁.trans k₂).trans k₃).trans k₄).mono (by decide)
  · rw [m₄, hw3, VG.Proof.Bignum.X86_64.word_writeW_self, sqStart, Bool.or_comm]
  · rw [m₄, (VG.Proof.Bignum.X86_64.writeW_outside _ B _ (d := 8 * sC1) (by simp only [sC1, sCnt, sFn]; omega)).word
      (Or.inr (by simp only [sC1, sC3, sCnt, sFn]; omega)) (by simp only [sC3, sFn]; omega), VG.Proof.Bignum.X86_64.word_writeW_self]
    rfl
  · rw [m₄, VG.Proof.Bignum.X86_64.word_writeW_self]; rfl

theorem sx100 : (BitVec.signExtend 64 (100 : BitVec 32)).toNat = 100 := by decide

theorem mask_beq_zero (b : Bool) : (VG.Proof.Bignum.X86_64.mask b == 0) = !b := by cases b <;> rfl

/-- `candNext`: the candidates tried `+= 1`, and `ZF` set to stop if `ok` or
if 100 are tried. -/
theorem candNext_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {c : Nat} {ok : Bool}
    (hcand : VG.Proof.Bignum.X86_64.word s.mem B (8 * sCand) = BitVec.ofNat 64 c) (hc3 : VG.Proof.Bignum.X86_64.word s.mem B (8 * sC3) = VG.Proof.Bignum.X86_64.mask ok)
    (hc : c < 100) :
    WP isa (.block candNext) s fun u =>
      u.zf = some (!(decide (c + 1 < 100) && !ok)) ∧
      u.mem = s.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * sCand)) (BitVec.ofNat 64 (c + 1)) ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rdx] s u := by
  have h256 := h.h256
  have ec : (BitVec.ofNat 64 (c + 1)).toNat = c + 1 := by rw [BitVec.toNat_ofNat]; omega
  have hr3 : ∀ v, (s.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * sCand)) v).readW (VG.Proof.Bignum.X86_64.off B (8 * sC3)) 64 = VG.Proof.Bignum.X86_64.mask ok := fun v => by
    have o := VG.Proof.Bignum.X86_64.writeW_outside s.mem B v (d := 8 * sCand)
      (by simp only [sCand, Impl.Bignum.X86_64.Public.sV, sFn]; omega)
    have := o.word (d := 8 * sC3) (Or.inr (by simp only [sCand, Impl.Bignum.X86_64.Public.sV, sC3, sFn]; omega))
      (by simp only [sC3, sFn]; omega)
    rw [hc3] at this
    exact this
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun u => u.zf = some (!(decide (c + 1 < 100) && !ok)) ∧
      u.mem = s.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * sCand)) (BitVec.ofNat 64 (c + 1))) (by
    unfold candNext
    xrun [State.ea, hdr, h.rdi, hdrOff,
      h.scr.ld (d := 8 * sCand) (by simp only [sCand, Impl.Bignum.X86_64.Public.sV, sFn]; omega),
      h.scr.st (d := 8 * sCand) (by simp only [sCand, Impl.Bignum.X86_64.Public.sV, sFn]; omega),
      h.scr.ld (d := 8 * sC3) (by simp only [sC3, sFn]; omega), hcand, ofNat_add_one, hr3, VG.Proof.Rsa.X86_64.sbb_mask,
      VG.Proof.Rsa.X86_64.mask_not, mask_and', ec, VG.Proof.Rsa.X86_64.sx100, Bool.and_self, VG.Proof.Rsa.X86_64.mask_beq_zero]) rfl) fun u ⟨a, b⟩ => ⟨a.1, a.2, b⟩

/-- The arrays and slots a candidate changes. -/
def candJs : List Nat := [aX, aAcc, aTmp, aXm, aG, aY]
def candHs : List Nat := [sMask, sC1, sC2, sC3, sCand]

theorem cand_hs : ∀ i ∈ VG.Proof.Rsa.X86_64.candHs, rSlot i = true ∧ i ≠ sMinv ∧ i ≠ sT := by decide

/-- A candidate, `g = c + 2`: `recoverStep n t r g`. -/
theorem candBody_ok (M : Mont) {u : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N el r t c : Nat}
    (hc : VG.Proof.Rsa.X86_64.Cst u B Z w minv N el r t) (hcand : VG.Proof.Bignum.X86_64.word u.mem B (8 * sCand) = BitVec.ofNat 64 c) (hc100 : c < 100) :
    WP isa (candBody M.mm) u fun u' =>
      u'.zf = some (!(decide (c + 1 < 100) && !(recoverStep N t r (c + 2)).isSome)) ∧
      Frm B (VG.Proof.Rsa.X86_64.rg w VG.Proof.Rsa.X86_64.candJs VG.Proof.Rsa.X86_64.candHs) u.mem u'.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs u u' ∧
      VG.Proof.Bignum.X86_64.word u'.mem B (8 * sCand) = BitVec.ofNat 64 (c + 1) ∧
      VG.Proof.Bignum.X86_64.word u'.mem B (8 * sC3) = VG.Proof.Bignum.X86_64.mask (recoverStep N t r (c + 2)).isSome ∧
      (∀ y, recoverStep N t r (c + 2) = some y →
        wv u'.mem B (VG.Proof.Bignum.X86_64.slot w aY) w = y * 2 ^ (64 * w) % N ∧ y < N) := by
  have hZ16 := hc.hZ16
  have hN : 0 < N := by have := hc.n1; omega
  have he2 := hc.e2
  have hw2 := hc.ws.w2
  have h256 := hc.ws.h256
  rw [show candBody M.mm = seqs ([.block gBlk, setWord aX .rcx, M.mm aXm aX aR2, copyA aG aXm, copyA aY aO,
      VG.Impl.Rsa.X86_64.Keys.Recover.expLoop M.mm] ++ ((eqA aY aO ++ ([.block (eqStore sC2)] ++ (eqA aY aNg ++ [.block chkBlk]))) ++
        [.loop (sqBody M.mm) .ne, .block candNext])) by
    simp only [candBody, List.append_assoc, List.cons_append, List.nil_append]]
  refine wp_seqs_append (by simp) (by simp) (WP.mono (VG.Proof.Rsa.X86_64.candA_ok M hc hcand hc100) fun u₁ ⟨hf₁, k₁, hY₁⟩ => ?_)
  have hc₁ := hc.congr hf₁ (by decide) (by decide) k₁ (by decide)
  have hy0 : powMod (c + 2) r N < N := by rw [powMod_eq]; exact Nat.mod_lt _ hN
  refine wp_seqs_append (by simp [eqA]) (by simp) (WP.mono (VG.Proof.Rsa.X86_64.candB_ok hc₁ hY₁ hy0)
    fun u₂ ⟨hf₂, k₂, hc2, hc3, hc1⟩ => ?_)
  have hc₂ := hc₁.congr hf₂ (by decide) (by decide) k₂ (by decide)
  have hY₂ : wv u₂.mem B (VG.Proof.Bignum.X86_64.slot w aY) w = powMod (c + 2) r N * 2 ^ (64 * w) % N := by
    rw [hf₂.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega), hY₁]
  simp only [seqs]
  refine WP.seq (wp_upto (a := 0) (N := 64 * (w + (el + 7) / 8)) (by have := hc.ws.w1; omega)
    (VG.Proof.Rsa.X86_64.SqI u₂ B w N t (sqStart N (powMod (c + 2) r N))) (fun k _ hk v hv => VG.Proof.Rsa.X86_64.sqBody_ok M hc₂ hk hv)
    (fun v hv => ?_) ⟨Frm.refl _ _ _, Keep.refl _ _, hY₂, hy0, hc1, hc2, hc3⟩)
  have hc₃ := hc₂.congr hv.frm (by decide) VG.Proof.Rsa.X86_64.sq_hs hv.keep (by decide)
  have hres := sq_result (n := N) (r := r) (g := c + 2) hc.t1 (Nat.le_of_lt hc.t2)
  have hy := hv.y
  have hylt := hv.ylt
  have hc3v := hv.c3
  generalize sqIter N t (64 * (w + (el + 7) / 8)) (sqStart N (powMod (c + 2) r N)) = st at hres hy hylt hc3v
  obtain ⟨yk, done, ok⟩ := st
  dsimp only at hy hylt hc3v
  have hcand₃ : VG.Proof.Bignum.X86_64.word v.mem B (8 * sCand) = BitVec.ofNat 64 c := by
    rw [hv.frm.rg_word (by decide) (by decide), hf₂.rg_word (by decide) (by decide),
      hf₁.rg_word (by decide) (by decide)]; exact hcand
  have hok : (recoverStep N t r (c + 2)).isSome = ok := by
    rw [← hres]; cases ok <;> rfl
  refine WP.mono (VG.Proof.Rsa.X86_64.candNext_ok hc₃.ws hcand₃ hc3v hc100) fun u' ⟨hz, m₄, k₄⟩ => ?_
  have hf₄ : Frm B (VG.Proof.Rsa.X86_64.rg w [] [sCand]) v.mem u'.mem := by
    rw [m₄]; exact Frm.rg_of_hdr (VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (by simp only [sCand, Impl.Bignum.X86_64.Public.sV, sFn]; omega))
      _ _ (List.mem_singleton_self _)
  refine ⟨by rw [hz, hok], ?_, ?_, by rw [m₄, VG.Proof.Bignum.X86_64.word_writeW_self], ?_, ?_⟩
  · exact (((hf₁.rg_trans hf₂).rg_trans hv.frm).rg_trans hf₄).rg_mono (by decide) (by decide)
  · exact (((k₁.trans k₂).trans hv.keep).trans k₄).mono (by decide)
  · rw [hf₄.rg_word (by decide) (by decide), hc3v, hok]
  · intro y hsome
    rw [← hres] at hsome
    cases ok
    · cases hsome
    · simp only [sqRes, ite_true, Option.some.injEq] at hsome
      subst hsome
      rw [hf₄.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega)]
      exact ⟨hy, hylt⟩

end VG.Proof.Rsa.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rsa.X86_64.RpCands`. -/
section

/-!
# `vg_rsa_recover_primes` on x86-64: the candidates

`candLoop`: the candidates `g = 2, 3, …` until one finds `y` or 100 are
tried: `recoverPrimes.go`'s result and the number of tries
(`candLoop_ok`), `ok` in `sC3` and `y` in Montgomery form.
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aR2 aXm aY aOne sCnt sMask)
open VG.Spec.Rsa (powMod recoverStep recoverPrimes recoverTries)

/-- Step 5's factors from `y`, the larger first. -/
def pqOf (N y : Nat) : Nat × Nat :=
  (max (Nat.gcd (y - 1) N) (N / Nat.gcd (y - 1) N), min (Nat.gcd (y - 1) N) (N / Nat.gcd (y - 1) N))

/-- The candidates `c` and on, from `s₀`. -/
structure CandI (s₀ : State) (B : Addr) (w N t r c : Nat) (u : State) : Prop where
  frm : Frm B (VG.Proof.Rsa.X86_64.rg w VG.Proof.Rsa.X86_64.candJs VG.Proof.Rsa.X86_64.candHs) s₀.mem u.mem
  keep : VG.Proof.MlKem.X86_64.Keep mmRegs s₀ u
  cand : VG.Proof.Bignum.X86_64.word u.mem B (8 * sCand) = BitVec.ofNat 64 c
  go : recoverPrimes.go N t r recoverTries = recoverPrimes.go N t r (recoverTries - c)

/-- `candLoop`: `recoverPrimes.go`'s result `(res.map (pqOf N), cnt)`. -/
theorem candLoop_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N el r t : Nat}
    (hc : VG.Proof.Rsa.X86_64.Cst s B Z w minv N el r t) :
    WP isa (candLoop M.mm) s fun u => ∃ res : Option Nat, ∃ cnt : Nat,
      recoverPrimes.go N t r recoverTries = (res.map (VG.Proof.Rsa.X86_64.pqOf N), cnt) ∧
      VG.Proof.Bignum.X86_64.word u.mem B (8 * sCand) = BitVec.ofNat 64 cnt ∧ VG.Proof.Bignum.X86_64.word u.mem B (8 * sC3) = VG.Proof.Bignum.X86_64.mask res.isSome ∧
      (∀ y, res = some y → wv u.mem B (VG.Proof.Bignum.X86_64.slot w aY) w = y * 2 ^ (64 * w) % N ∧ y < N ∧ y * y % N = 1) ∧
      Frm B (VG.Proof.Rsa.X86_64.rg w VG.Proof.Rsa.X86_64.candJs VG.Proof.Rsa.X86_64.candHs) s.mem u.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs s u := by
  have h256 := hc.ws.h256
  unfold candLoop
  refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun u => u.mem = s.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * sCand))
      (BitVec.ofNat 64 0)) (by
    xrun [State.ea, hdr, hc.ws.rdi, hdrOff,
      hc.ws.scr.st (d := 8 * sCand) (by simp only [sCand, Impl.Bignum.X86_64.Public.sV, sFn]; omega)]
    rfl) rfl) fun s₁ ⟨m₁, k₁⟩ => ?_)
  have hf₁ : Frm B (VG.Proof.Rsa.X86_64.rg w VG.Proof.Rsa.X86_64.candJs VG.Proof.Rsa.X86_64.candHs) s.mem s₁.mem := by
    rw [m₁]; exact Frm.rg_of_hdr (VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (by simp only [sCand, Impl.Bignum.X86_64.Public.sV, sFn]; omega))
      _ _ (by decide)
  refine WP.loop (M := isa) (fun n u => ∃ c, n = recoverTries - c ∧ c < recoverTries ∧ VG.Proof.Rsa.X86_64.CandI s B w N t r c u)
    ?_ (recoverTries - 0) s₁ ⟨0, rfl, by decide, hf₁, k₁.mono (by decide), by rw [m₁, VG.Proof.Bignum.X86_64.word_writeW_self], rfl⟩
  rintro n u ⟨c, rfl, hc100, hI⟩
  have hcu : VG.Proof.Rsa.X86_64.Cst u B Z w minv N el r t := hc.congr hI.frm (by decide) VG.Proof.Rsa.X86_64.cand_hs hI.keep (by decide)
  refine WP.mono (VG.Proof.Rsa.X86_64.candBody_ok M hcu hI.cand hc100) fun u' ⟨hz, hf, k, hcand, hc3, hy⟩ => ?_
  have hgo := VG.Proof.Rsa.go_eq N t r hc100
  have hfr : Frm B (VG.Proof.Rsa.X86_64.rg w VG.Proof.Rsa.X86_64.candJs VG.Proof.Rsa.X86_64.candHs) s.mem u'.mem := (hI.frm.rg_trans hf).rg_mono (by decide) (by decide)
  have hk : VG.Proof.MlKem.X86_64.Keep mmRegs s u' := (hI.keep.trans k).mono (by decide)
  cases hres : recoverStep N t r (c + 2) with
  | some y =>
    rw [hres] at hz hc3 hgo
    refine .inl ⟨by simp [VG.X86_64.eval, hz], some y, c + 1, ?_, hcand, hc3, fun y' hy' => ?_, hfr, hk⟩
    · rw [hI.go, hgo]; rfl
    · cases hy'; exact ⟨(hy y hres).1, (hy y hres).2, VG.Proof.Rsa.recoverStep_some hres⟩
  | none =>
    rw [hres] at hz hc3 hgo
    by_cases hlast : c + 1 < recoverTries
    · have hlast' : c + 1 < 100 := hlast
      refine .inr ⟨by simp [VG.X86_64.eval, hz, hlast'], recoverTries - (c + 1), by omega, c + 1, rfl, hlast,
        hfr, hk, hcand, by rw [hI.go, hgo]⟩
    · have hlast' : ¬ c + 1 < 100 := hlast
      refine .inl ⟨by simp [VG.X86_64.eval, hz, hlast'], none, c + 1, ?_, hcand, hc3, (fun y' hy' => by cases hy'),
        hfr, hk⟩
      rw [hI.go, hgo, show c + 1 = recoverTries by unfold recoverTries at *; omega, VG.Proof.Rsa.go_last]
      rfl

end VG.Proof.Rsa.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rsa.X86_64.RpLt`. -/
section

/-!
# `vg_rsa_recover_primes` on x86-64: comparing numbers

`wordLoop 0 ltBody`: the borrow of `[rbx] - [r10]` over `N` words, the mask
of `[rbx] < [r10]` in `rbp` (`lt_ok`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64

structure LtInv (s₀ : State) (B : Addr) (Z eX eY : Nat) (j : Nat) (t : State) : Prop where
  scr : VG.Proof.Bignum.X86_64.Scr t B Z
  keep : VG.Proof.MlKem.X86_64.Keep [.rax, .rbp, .r14] s₀ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  mem : t.mem = s₀.mem
  val : ∃ c : Bool, ∃ d : Nat, d < 2 ^ (64 * j) ∧ t.gpr .rbp = VG.Proof.Bignum.X86_64.mask c ∧
    d + wv s₀.mem B eY j = wv s₀.mem B eX j + 2 ^ (64 * j) * c.toNat

theorem ltStep_ok {s₀ : State} {B : Addr} {Z w eX eY : Nat}
    (hbx : s₀.gpr .rbx = VG.Proof.Bignum.X86_64.off B eX) (h10 : s₀.gpr .r10 = VG.Proof.Bignum.X86_64.off B eY) (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w)
    (hw : w < 2 ^ 32) (hX : eX + 8 * w ≤ Z) (hY : eY + 8 * w ≤ Z) {j : Nat} (hj : j < w) {t : State}
    (hI : VG.Proof.Rsa.X86_64.LtInv s₀ B Z eX eY j t) :
    WP isa (.block (ltBody ++ ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t
      fun t' => t'.zf = some (decide (j + 1 = w)) ∧ VG.Proof.Rsa.X86_64.LtInv s₀ B Z eX eY (j + 1) t' := by
  have hn := hI.scr.nowrap
  have tbx : t.gpr .rbx = VG.Proof.Bignum.X86_64.off B eX := (hI.keep.gpr (by decide)).trans hbx
  have t10 : t.gpr .r10 = VG.Proof.Bignum.X86_64.off B eY := (hI.keep.gpr (by decide)).trans h10
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  obtain ⟨c, d, hd, hbp, hval⟩ := hI.val
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rbp] (Q := fun t₁ =>
      ∃ c' : Bool, t₁.gpr .rbp = VG.Proof.Bignum.X86_64.mask c' ∧ t₁.mem = t.mem ∧ ∃ r : BitVec 64,
        r.toNat + (VG.Proof.Bignum.X86_64.word t.mem B (eY + 8 * j)).toNat + c.toNat =
          (VG.Proof.Bignum.X86_64.word t.mem B (eX + 8 * j)).toNat + 2 ^ 64 * c'.toNat) ?_ rfl) fun t₁ ⟨⟨c', h₁, hm, r, hr⟩, k₁⟩ => ?_
  · unfold ltBody cfFromRbp cfToRbp
    xrun [State.ea, ix, addr0 tbx hI.r14, addr0 t10 hI.r14, hbp, cf_mask,
      hI.scr.ld (show eX + 8 * j + 8 ≤ Z by omega), hI.scr.ld (show eY + 8 * j + 8 ≤ Z by omega)]
    exact ⟨_, rfl, _, sbb_toNat _ _ _⟩
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (count_ok t₁ t₁14 t₁12 (by omega) (by omega)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  rw [hI.mem] at hr
  have hrl := r.isLt
  refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), ((hI.keep.trans k₁).trans k').mono (by decide), h14,
    by rw [hm', hm, hI.mem], ⟨c', d + 2 ^ (64 * j) * r.toNat, ?_, (k'.gpr (by decide)).trans h₁, ?_⟩⟩
  · rw [pow64_succ]
    have : 2 ^ (64 * j) * r.toNat ≤ 2 ^ (64 * j) * (2 ^ 64 - 1) := Nat.mul_le_mul_left _ (by omega)
    rw [Nat.mul_sub, Nat.mul_one] at this
    omega
  · simp only [wv]
    rw [pow64_succ]
    grind

/-- `wordLoop 0 ltBody` over `N` words: `rbp` the mask of `[rbx] < [r10]`. -/
theorem lt_ok {s : State} {B : Addr} {Z N eX eY : Nat} (hs : VG.Proof.Bignum.X86_64.Scr s B Z)
    (hbx : s.gpr .rbx = VG.Proof.Bignum.X86_64.off B eX) (h10 : s.gpr .r10 = VG.Proof.Bignum.X86_64.off B eY) (h12 : s.gpr .r12 = BitVec.ofNat 64 N)
    (hbp : s.gpr .rbp = VG.Proof.Bignum.X86_64.mask false) (hN : 1 ≤ N) (hN' : N < 2 ^ 31) (hX : eX + 8 * N ≤ Z) (hY : eY + 8 * N ≤ Z) :
    WP isa (wordLoop 0 ltBody) s fun t =>
      t.gpr .rbp = VG.Proof.Bignum.X86_64.mask (decide (wv s.mem B eX N < wv s.mem B eY N)) ∧ t.mem = s.mem ∧
      VG.Proof.MlKem.X86_64.Keep [.rax, .rbp, .r14] s t := by
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s.mem → VG.Proof.MlKem.X86_64.Keep [.r14] s t → t.cf = s.cf →
      VG.Proof.Rsa.X86_64.LtInv s B Z eX eY 0 t := fun t h14 hm k _ =>
    ⟨hs.congr k.2.2, k.mono (by decide), h14, hm,
      ⟨false, 0, by simp, (k.gpr (by decide)).trans hbp, by simp [wv]⟩⟩
  refine WP.mono (wordLoop_ok (start := 0) (N := N) (by omega) hN' (VG.Proof.Rsa.X86_64.LtInv s B Z eX eY) h0
    (fun j _ hj t hI => VG.Proof.Rsa.X86_64.ltStep_ok hbx h10 h12 (by omega) hX hY hj hI)) fun t hI => ?_
  obtain ⟨c, d, hd, hb, hv⟩ := hI.val
  refine ⟨?_, hI.mem, hI.keep⟩
  rw [hb]
  congr 1
  have := wv_lt s.mem B eY N
  cases c
  · simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at hv
    exact (decide_eq_false (by omega)).symm
  · simp only [Bool.toNat_true, Nat.mul_one] at hv
    exact (decide_eq_true (by omega)).symm

end VG.Proof.Rsa.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rsa.X86_64.RpIn`. -/
section

/-!
# `vg_rsa_recover_primes` on x86-64: the arguments

`RpArgs`: the arguments `entry` leaves in the header, kept by the pieces;
`RpS`: what every piece of `main` keeps (the working space, the arguments,
the inputs' bytes, and memory outside the working space), from a frame of
arrays and slots of `rSlot` (`RpS.step`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN)

/-- The inputs of `vg_rsa_recover_primes` and where they are. -/
structure RpIn where
  B : Addr
  Z : Nat
  k : Nat
  el : Nat
  dl : Nat
  pP : Addr
  pQ : Addr
  pN : Addr
  pE : Addr
  pD : Addr
  sv : Nat → BitVec 64
  nb : List Byte
  eb : List Byte
  db : List Byte
  W : List Region
  sp : BitVec 64

/-- The arguments in the header: the outputs' pointers, `n`'s, `e`'s and
`d`'s pointers and lengths, and the saved registers `sv`. -/
structure RpArgs (m : Mem) (B : Addr) (k el dl : Nat) (pP pQ pN pE pD : Addr) (sv : Nat → BitVec 64) : Prop where
  p : VG.Proof.Bignum.X86_64.word m B (8 * sP) = pP
  q : VG.Proof.Bignum.X86_64.word m B (8 * sQ) = pQ
  n : VG.Proof.Bignum.X86_64.word m B (8 * Impl.Bignum.X86_64.Public.sN) = pN
  k : VG.Proof.Bignum.X86_64.word m B (8 * Impl.Bignum.X86_64.Public.sK) = BitVec.ofNat 64 k
  e : VG.Proof.Bignum.X86_64.word m B (8 * Impl.Bignum.X86_64.Public.sE) = pE
  el : VG.Proof.Bignum.X86_64.word m B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 el
  d : VG.Proof.Bignum.X86_64.word m B (8 * sD) = pD
  dl : VG.Proof.Bignum.X86_64.word m B (8 * sDl) = BitVec.ofNat 64 dl
  saved : ∀ i < 6, VG.Proof.Bignum.X86_64.word m B (8 * i) = sv i

/-- The header slots of `RpArgs`. -/
def rArg (i : Nat) : Prop := i < 6 ∨ (16 ≤ i ∧ i < 22) ∨ i = 23 ∨ i = 24

theorem RpArgs.congr {m m' : Mem} {B : Addr} {k el dl : Nat} {pP pQ pN pE pD : Addr} {sv : Nat → BitVec 64}
    (h : VG.Proof.Rsa.X86_64.RpArgs m B k el dl pP pQ pN pE pD sv) (hm : ∀ i, VG.Proof.Rsa.X86_64.rArg i → VG.Proof.Bignum.X86_64.word m' B (8 * i) = VG.Proof.Bignum.X86_64.word m B (8 * i)) :
    VG.Proof.Rsa.X86_64.RpArgs m' B k el dl pP pQ pN pE pD sv :=
  ⟨(hm _ (by simp [VG.Proof.Rsa.X86_64.rArg, sP, Impl.Bignum.X86_64.Public.sOut, sFn])).trans h.p,
    (hm _ (by simp [VG.Proof.Rsa.X86_64.rArg, sQ, Impl.Bignum.X86_64.Public.sIn, sFn])).trans h.q,
    (hm _ (by simp [VG.Proof.Rsa.X86_64.rArg, Impl.Bignum.X86_64.Public.sN, sFn])).trans h.n,
    (hm _ (by simp [VG.Proof.Rsa.X86_64.rArg, Impl.Bignum.X86_64.Public.sK, sFn])).trans h.k,
    (hm _ (by simp [VG.Proof.Rsa.X86_64.rArg, Impl.Bignum.X86_64.Public.sE, sFn])).trans h.e,
    (hm _ (by simp [VG.Proof.Rsa.X86_64.rArg, Impl.Bignum.X86_64.Public.sElen, sFn])).trans h.el,
    (hm _ (by simp [VG.Proof.Rsa.X86_64.rArg, sD, Impl.Bignum.X86_64.Public.sI, sFn])).trans h.d,
    (hm _ (by simp [VG.Proof.Rsa.X86_64.rArg, sDl, Impl.Bignum.X86_64.Public.sBit, sFn])).trans h.dl,
    fun i hi => (hm i (Or.inl hi)).trans (h.saved i hi)⟩

/-- An argument slot is not a slot of `rSlot`. -/
theorem rArg_rSlot {i : Nat} (hi : VG.Proof.Rsa.X86_64.rArg i) : rSlot i = false := by
  unfold VG.Proof.Rsa.X86_64.rArg at hi
  simp only [rSlot, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
  omega

/-- The argument slots, after code that changes only arrays and slots of
`rSlot`. -/
theorem rArg_frm {m m' : Mem} {B : Addr} {w : Nat} {js hs : List Nat} (hf : Frm B (VG.Proof.Rsa.X86_64.rg w js hs) m m')
    (hhs : ∀ i ∈ hs, rSlot i = true) : ∀ i, VG.Proof.Rsa.X86_64.rArg i → VG.Proof.Bignum.X86_64.word m' B (8 * i) = VG.Proof.Bignum.X86_64.word m B (8 * i) := fun i hi =>
  hf.rg_word (by unfold VG.Proof.Rsa.X86_64.rArg at hi; omega) fun hm => by have := hhs i hm; rw [VG.Proof.Rsa.X86_64.rArg_rSlot hi] at this; cases this

/-- What every piece of `main` keeps, from the memory `m₀` on entry to
`main`. -/
structure RpS (I : VG.Proof.Rsa.X86_64.RpIn) (m₀ : Mem) (s : State) : Prop where
  ws : Ws s I.B I.Z (wk I.k)
  args : VG.Proof.Rsa.X86_64.RpArgs s.mem I.B I.k I.el I.dl I.pP I.pQ I.pN I.pE I.pD I.sv
  n : Src s I.B I.Z I.pN I.nb
  e : Src s I.B I.Z I.pE I.eb
  d : Src s I.B I.Z I.pD I.db
  inScr : InScr I.B I.Z m₀ s.mem
  wr : s.wr = I.W
  rsp : s.gpr .rsp = I.sp

/-- The ranges of `rg` are in the working space. -/
theorem rg_le {w Z : Nat} (hZ : VG.Proof.Bignum.X86_64.slot w 16 ≤ Z) {js hs : List Nat} (hjs : ∀ j ∈ js, j < 16)
    (hhs : ∀ i ∈ hs, i < 32) : ∀ r ∈ VG.Proof.Rsa.X86_64.rg w js hs, r.1 + r.2 ≤ Z := by
  intro r hr
  simp only [VG.Proof.Rsa.X86_64.rg, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨j, hj, rfl⟩ | ⟨i, hi, rfl⟩
  · have := slot_lt (w := w) (hjs j hj); dsimp only; omega
  · have := hdr_lt_slot w 16 (hhs i hi); dsimp only; omega

theorem RpS.step {I : VG.Proof.Rsa.X86_64.RpIn} {m₀ : Mem} {s t : State} (h : VG.Proof.Rsa.X86_64.RpS I m₀ s) {js hs : List Nat}
    (hf : Frm I.B (VG.Proof.Rsa.X86_64.rg (wk I.k) js hs) s.mem t.mem) (hjs : ∀ j ∈ js, j < 16) (hhs : ∀ i ∈ hs, rSlot i = true)
    {regs : List Reg} (k : VG.Proof.MlKem.X86_64.Keep regs s t) (hr : .rdi ∉ regs ∧ .rsp ∉ regs) : VG.Proof.Rsa.X86_64.RpS I m₀ t :=
  have h32 : ∀ i ∈ hs, i < 32 := fun i hi => by
    have := hhs i hi; simp only [rSlot, Bool.or_eq_true, beq_iff_eq] at this; omega
  have hi : InScr I.B I.Z s.mem t.mem := InScr.of_frm hf (VG.Proof.Rsa.X86_64.rg_le h.ws.hZ hjs h32)
  ⟨h.ws.congrG hf hhs k hr.1, h.args.congr (VG.Proof.Rsa.X86_64.rArg_frm hf hhs), h.n.congrK hi k, h.e.congrK hi k,
    h.d.congrK hi k, h.inScr.trans hi, k.2.2.trans h.wr, (k.gpr hr.2).trans h.rsp⟩

/-- The lengths, as `vg_rsa_recover_primes`'s contract bounds them. -/
structure RpLens (I : VG.Proof.Rsa.X86_64.RpIn) : Prop where
  k1 : 64 ≤ I.k
  k2 : I.k ≤ 1024
  el1 : 1 ≤ I.el
  el2 : I.el ≤ I.k
  dl1 : 1 ≤ I.dl
  dl2 : I.dl ≤ I.k
  nbl : I.nb.length = I.k
  ebl : I.eb.length = I.el
  dbl : I.db.length = I.dl
  z : 128 * I.k ≤ I.Z

/-- The loads of `n`, `e` and `d`. -/
theorem rpLoads_ok {I : VG.Proof.Rsa.X86_64.RpIn} {m₀ : Mem} {s : State} (h : VG.Proof.Rsa.X86_64.RpS I m₀ s) (L : VG.Proof.Rsa.X86_64.RpLens I) :
    WP isa (seqs (loadA aN Impl.Bignum.X86_64.Public.sN Impl.Bignum.X86_64.Public.sK ++
      (loadA aE Impl.Bignum.X86_64.Public.sE Impl.Bignum.X86_64.Public.sElen ++ loadA aD sD sDl))) s fun t =>
      VG.Proof.Rsa.X86_64.RpS I m₀ t ∧ Frm I.B (VG.Proof.Rsa.X86_64.rg (wk I.k) [aN, aE, aD] []) s.mem t.mem ∧
      wv t.mem I.B (VG.Proof.Bignum.X86_64.slot (wk I.k) aN) (wk I.k) = Spec.Rsa.os2ip I.nb ∧
      wv t.mem I.B (VG.Proof.Bignum.X86_64.slot (wk I.k) aE) (wk I.k) = Spec.Rsa.os2ip I.eb ∧
      wv t.mem I.B (VG.Proof.Bignum.X86_64.slot (wk I.k) aD) (wk I.k) = Spec.Rsa.os2ip I.db ∧ VG.Proof.MlKem.X86_64.Keep mmRegs s t := by
  have hk1 := L.k1
  have hk2 := L.k2
  have hel := L.el2
  have hdl := L.dl2
  have hZ16 : VG.Proof.Bignum.X86_64.slot (wk I.k) 16 ≤ 2 ^ 64 := by have := h.ws.scr.nowrap; have := h.ws.hZ; omega
  refine wp_seqs_append (by simp [loadA]) (by simp [loadA]) (WP.mono (loadA_ok h.ws (j := aN) (by decide)
    (by decide) (by decide) h.args.n h.args.k h.n L.nbl (by omega) (by unfold wk; omega))
    fun s₁ ⟨v₁, o₁, k₁⟩ => ?_)
  have f₁ : Frm I.B (VG.Proof.Rsa.X86_64.rg (wk I.k) [aN] []) s.mem s₁.mem := Frm.rg_of_out o₁ (Nat.le_refl _) _ _ (by decide)
  have h₁ := h.step f₁ (by decide) (by simp) k₁ (by decide)
  refine wp_seqs_append (by simp [loadA]) (by simp [loadA]) (WP.mono (loadA_ok h₁.ws (j := aE) (by decide)
    (by decide) (by decide) h₁.args.e h₁.args.el h₁.e L.ebl L.el1 (by unfold wk; omega))
    fun s₂ ⟨v₂, o₂, k₂⟩ => ?_)
  have f₂ : Frm I.B (VG.Proof.Rsa.X86_64.rg (wk I.k) [aE] []) s₁.mem s₂.mem := Frm.rg_of_out o₂ (Nat.le_refl _) _ _ (by decide)
  have h₂ := h₁.step f₂ (by decide) (by simp) k₂ (by decide)
  refine WP.mono (loadA_ok h₂.ws (j := aD) (by decide) (by decide) (by decide) h₂.args.d h₂.args.dl h₂.d L.dbl
    L.dl1 (by unfold wk; omega)) fun t ⟨v₃, o₃, k₃⟩ => ?_
  have f₃ : Frm I.B (VG.Proof.Rsa.X86_64.rg (wk I.k) [aD] []) s₂.mem t.mem := Frm.rg_of_out o₃ (Nat.le_refl _) _ _ (by decide)
  refine ⟨h₂.step f₃ (by decide) (by simp) k₃ (by decide), ((f₁.rg_trans f₂).rg_trans f₃).rg_mono (by decide)
    (by decide), ?_, ?_, v₃, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  · rw [f₃.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega),
      f₂.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega), v₁]
  · rw [f₃.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega), v₂]

end VG.Proof.Rsa.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rsa.X86_64.RpFin`. -/
section

/-!
# `vg_rsa_recover_primes` on x86-64: the factors

`fin`, after the candidates: `y` out of Montgomery form and `u = y - 1`
(`finA_ok`), `p = gcd(u, n)` and `q = n / p` (`finB_ok`), the larger first
(`finC_ok`), both written masked by whether a candidate found `y`, and the
mask's low bit returned (`rpStores_ok`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aR2 aXm aY aOne sCnt sMask)
open VG.Proof.Bignum (mont_cancel)

/-- `u = y - 1` from `y` in Montgomery form, and the mask of `ok` into
`sMask`. -/
theorem finA_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N el r t : Nat}
    (hc : VG.Proof.Rsa.X86_64.Cst s B Z w minv N el r t) {res : Option Nat} (hc3 : VG.Proof.Bignum.X86_64.word s.mem B (8 * sC3) = VG.Proof.Bignum.X86_64.mask res.isSome)
    (hy : ∀ y, res = some y → wv s.mem B (VG.Proof.Bignum.X86_64.slot w aY) w = y * 2 ^ (64 * w) % N ∧ y < N ∧ 1 ≤ y) :
    WP isa (seqs [.block [.mov .rax (.mem (hdr sC3)), .store (hdr sMask) .rax], M.mm aY aY aOne, zeroA fU,
      .block (VG.Impl.Rsa.X86_64.Keys.ws ++ base aY .r8 ++ base aOne .r10 ++ base fU .rsi ++ ([.mov32 .rbp (.imm 0)] : List Instr)),
      wordLoop 0 subBody]) s fun u =>
      Frm B (VG.Proof.Rsa.X86_64.rg w [aAcc, aTmp, aY, fU] [sMask]) s.mem u.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs s u ∧
      VG.Proof.Bignum.X86_64.word u.mem B (8 * sMask) = VG.Proof.Bignum.X86_64.mask res.isSome ∧ VG.Proof.Bignum.X86_64.word u.mem B (VG.Proof.Bignum.X86_64.slot w fU + 8 * w) = 0 ∧
      (∀ y, res = some y → wv u.mem B (VG.Proof.Bignum.X86_64.slot w fU) w = y - 1) := by
  have hZ16 := hc.hZ16
  have hw1 := hc.ws.w1
  have hw2 := hc.ws.w2
  have h256 := hc.ws.h256
  have hR := hc.coprime
  have hN1 : 1 < N := by have := hc.n1; omega
  simp only [seqs]
  -- The mask.
  refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun u => u.mem = s.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * sMask))
      (VG.Proof.Bignum.X86_64.mask res.isSome)) (by
    xrun [State.ea, hdr, hc.ws.rdi, hdrOff, hc.ws.scr.ld (d := 8 * sC3) (by simp only [sC3, sFn]; omega),
      hc.ws.scr.st (d := 8 * sMask) (by simp only [sMask, sFn]; omega), hc3]) rfl) fun u₁ ⟨m₁, k₁⟩ => ?_)
  have hf₁ : Frm B (VG.Proof.Rsa.X86_64.rg w [] [sMask]) s.mem u₁.mem := by
    rw [m₁]; exact Frm.rg_of_hdr (VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (by simp only [sMask, sFn]; omega)) _ _
      (List.mem_singleton_self _)
  have hc₁ := hc.congr hf₁ (by decide) (by decide) k₁ (by decide)
  -- `y`.
  have hg₁ := hc₁.good
  have hY₁ : wv u₁.mem B (VG.Proof.Bignum.X86_64.slot w aY) w = wv s.mem B (VG.Proof.Bignum.X86_64.slot w aY) w :=
    hf₁.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega)
  refine WP.seq (WP.mono (M.mm_ok hg₁.1 hg₁.2 hw1 (by omega) (o := aY) (a := aY) (b := aOne) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc₁.hinv
    (by rw [hc₁.hone, hc₁.hn]; exact hN1)) fun u₂ ⟨_, hlt₂, hm₂, ha₂, k₂⟩ => ?_)
  rw [hc₁.hn] at hlt₂ hm₂
  rw [hc₁.hone, hY₁, Nat.mul_one] at hm₂
  have hf₂ : Frm B (VG.Proof.Rsa.X86_64.rg w [aAcc, aTmp, aY] []) u₁.mem u₂.mem := Frm.rg_of_arrays ha₂ _ _ (by decide)
  have hc₂ := hc₁.congr hf₂ (by decide) (by simp) k₂ (by decide)
  have hy₂ : ∀ y, res = some y → wv u₂.mem B (VG.Proof.Bignum.X86_64.slot w aY) w = y := fun y hres => by
    obtain ⟨e, hyN, _⟩ := hy y hres
    rw [e, Nat.mod_mod] at hm₂
    have := mont_cancel hR hm₂
    rwa [Nat.mod_eq_of_lt hlt₂, Nat.mod_eq_of_lt hyN] at this
  -- `u = 0`.
  refine WP.seq (WP.mono (zeroA_ok hc₂.ws (j := fU) (by decide)) fun u₃ ⟨z₃, o₃, k₃⟩ => ?_)
  have hf₃ : Frm B (VG.Proof.Rsa.X86_64.rg w [fU] []) u₂.mem u₃.mem := Frm.rg_of_out o₃ (Nat.le_refl _) _ _ (by decide)
  have hc₃ := hc₂.congr hf₃ (by decide) (by simp) k₃ (by decide)
  -- `u = y - 1`.
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86_64.subSet_ok hc₃.ws aY aOne fU) fun u₄ ⟨h12, h8, h10, hsi, hbp, m₄, k₄⟩ => ?_)
  have hs₄ := hc₃.ws.scr.congr k₄.2.2
  have sY := hc₃.ws.sl (j := aY) (by decide)
  have sO := hc₃.ws.sl (j := aOne) (by decide)
  have sU := hc₃.ws.sl (j := fU) (by decide)
  refine WP.mono (VG.Proof.Rsa.X86_64.sub_ok hs₄ h8 h10 hsi h12 hbp (by omega) (by omega) (by omega) (by omega) (by omega)
    (by have := slot_far (w := w) (show fU ≠ aY by decide); omega)
    (by have := slot_far (w := w) (show fU ≠ aOne by decide); omega)) fun u ⟨cb, _, hv, o₅, k₅⟩ => ?_
  have hf₅ : Frm B (VG.Proof.Rsa.X86_64.rg w [fU] []) u₄.mem u.mem := Frm.rg_of_out o₅ (by omega) _ _ (by decide)
  rw [m₄] at hv o₅
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hf₄ : Frm B (VG.Proof.Rsa.X86_64.rg w [] []) u₃.mem u₄.mem := by rw [m₄]; exact Frm.refl _ _ _
    exact ((((hf₁.rg_trans hf₂).rg_trans hf₃).rg_trans hf₄).rg_trans hf₅).rg_mono (by decide) (by decide)
  · exact ((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).mono (by decide)
  · rw [hf₅.rg_word (by decide) (by simp), m₄, hf₃.rg_word (by decide) (by simp),
      hf₂.rg_word (by decide) (by simp), m₁, VG.Proof.Bignum.X86_64.word_writeW_self]
  · rw [o₅.word (Or.inr (by omega)) (by have := hc.ws.scr.nowrap; omega)]
    exact VG.Proof.Rsa.X86_64.word_above_zero (n := w) (L := w + 2) (by omega) (by rw [z₃]; exact Nat.two_pow_pos _)
  · intro y hres
    obtain ⟨_, hyN, hy1⟩ := hy y hres
    have e3 : wv u₃.mem B (VG.Proof.Bignum.X86_64.slot w aY) w = y := by
      rw [hf₃.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega)]; exact hy₂ y hres
    rw [e3, hc₃.hone] at hv
    have := wv_lt u.mem B (VG.Proof.Bignum.X86_64.slot w fU) w
    have hyR : y < 2 ^ (64 * w) := by have := wv_lt u₂.mem B (VG.Proof.Bignum.X86_64.slot w aY) w; rw [hy₂ y hres] at this; exact this
    cases cb
    · simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at hv; omega
    · simp only [Bool.toNat_true, Nat.mul_one] at hv; omega

/-- `1` written over a zero number. -/
theorem wv_set_one {m : Mem} {B : Addr} {e w : Nat} (hw : 1 ≤ w) (hz : wv m B e (w + 2) = 0)
    (hn : e + 8 * (w + 2) ≤ 2 ^ 64) : wv (m.writeW (VG.Proof.Bignum.X86_64.off B e) (1 : BitVec 64)) B e w = 1 := by
  rw [VG.Proof.Rsa.X86_64.wv_low hw, VG.Proof.Bignum.X86_64.word_writeW_self, (VG.Proof.Bignum.X86_64.writeW_outside m B (1 : BitVec 64) (d := e) (by omega)).wv (Or.inr (by omega))
    (by omega)]
  have hz' : ∀ q < w + 2, VG.Proof.Bignum.X86_64.word m B (e + 8 * q) = 0 := (wv_eq_zero_iff _ _ _ _).mp hz
  rw [VG.Proof.Rsa.X86_64.wv_zero (n := w - 1) fun q hq => by
    have := hz' (1 + q) (by omega)
    rwa [show e + 8 * (1 + q) = e + 8 + 8 * q by omega] at this]
  rfl

/-- `p = gcd(u, n)` and `q = n / p`. -/
theorem finB_ok {s : State} {B : Addr} {Z w N : Nat} (h : Ws s B Z w) (hn : wv s.mem B (VG.Proof.Bignum.X86_64.slot w aN) w = N)
    (hodd : N % 2 = 1) (hN1 : 1 < N) (hU0 : VG.Proof.Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w fU + 8 * w) = 0) :
    WP isa (seqs [zeroA fV, copyA fV aN, zeroA fX₁, .block (setOneA fX₁), zeroA fX₂, inverse fU fV fX₁ fX₂ aN fT,
      zeroA fQ, copyA fQ aN, divmod fQ fR fV fT]) s fun u =>
      Frm B (VG.Proof.Rsa.X86_64.rg w [fV, fX₁, fX₂, fU, fT, fQ, fR] [sMo]) s.mem u.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs s u ∧ Ws u B Z w ∧
      wv u.mem B (VG.Proof.Bignum.X86_64.slot w fV) w = Nat.gcd (wv s.mem B (VG.Proof.Bignum.X86_64.slot w fU) w) N ∧
      wv u.mem B (VG.Proof.Bignum.X86_64.slot w fQ) w = N / Nat.gcd (wv s.mem B (VG.Proof.Bignum.X86_64.slot w fU) w) N ∧
      wv u.mem B (VG.Proof.Bignum.X86_64.slot w aN) w = N := by
  have hZ16 : VG.Proof.Bignum.X86_64.slot w 16 ≤ 2 ^ 64 := by have := h.scr.nowrap; have := h.hZ; omega
  have hw1 := h.w1
  have hw2 := h.w2
  have hZ := h.hZ
  have sV := h.sl (j := fV) (by decide)
  have hnw := h.scr.nowrap
  simp only [seqs]
  -- `v = n`.
  refine WP.seq (WP.mono (zeroA_ok h (j := fV) (by decide)) fun u₁ ⟨_, o₁, k₁⟩ => ?_)
  have f₁ : Frm B (VG.Proof.Rsa.X86_64.rg w [fV] []) s.mem u₁.mem := Frm.rg_of_out o₁ (Nat.le_refl _) _ _ (by decide)
  have h₁ := h.congrG f₁ (by simp) k₁ (by decide)
  refine WP.seq (WP.mono (copyA_ok h₁ (o := fV) (a := aN) (by decide) (by decide) (by decide))
    fun u₂ ⟨c₂, o₂, k₂⟩ => ?_)
  have f₂ : Frm B (VG.Proof.Rsa.X86_64.rg w [fV] []) u₁.mem u₂.mem := Frm.rg_of_out o₂ (by omega) _ _ (by decide)
  have h₂ := h₁.congrG f₂ (by simp) k₂ (by decide)
  -- `x₁ = 1`, `x₂ = 0`.
  refine WP.seq (WP.mono (zeroA_ok h₂ (j := fX₁) (by decide)) fun u₃ ⟨z₃, o₃, k₃⟩ => ?_)
  have f₃ : Frm B (VG.Proof.Rsa.X86_64.rg w [fX₁] []) u₂.mem u₃.mem := Frm.rg_of_out o₃ (Nat.le_refl _) _ _ (by decide)
  have h₃ := h₂.congrG f₃ (by simp) k₃ (by decide)
  refine WP.seq (WP.mono (setOneA_ok h₃ (j := fX₁) (by decide)) fun u₄ ⟨m₄, k₄⟩ => ?_)
  have sX₁ := h.sl (j := fX₁) (by decide)
  have f₄ : Frm B (VG.Proof.Rsa.X86_64.rg w [fX₁] []) u₃.mem u₄.mem := by
    rw [m₄]; exact Frm.rg_of_out (VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (by omega)) (by omega) _ _ (by decide)
  have h₄ := h₃.congrG f₄ (by simp) k₄ (by decide)
  have vX₁ : wv u₄.mem B (VG.Proof.Bignum.X86_64.slot w fX₁) w = 1 := by rw [m₄]; exact VG.Proof.Rsa.X86_64.wv_set_one (by omega) z₃ (by omega)
  refine WP.seq (WP.mono (zeroA_ok h₄ (j := fX₂) (by decide)) fun u₅ ⟨z₅, o₅, k₅⟩ => ?_)
  have f₅ : Frm B (VG.Proof.Rsa.X86_64.rg w [fX₂] []) u₄.mem u₅.mem := Frm.rg_of_out o₅ (Nat.le_refl _) _ _ (by decide)
  have h₅ := h₄.congrG f₅ (by simp) k₅ (by decide)
  have f15 : Frm B (VG.Proof.Rsa.X86_64.rg w [fV, fX₁, fX₂] []) s.mem u₅.mem :=
    ((((f₁.rg_trans f₂).rg_trans f₃).rg_trans f₄).rg_trans f₅).rg_mono (by decide) (by decide)
  have vN₅ : wv u₅.mem B (VG.Proof.Bignum.X86_64.slot w aN) w = N := by
    rw [f15.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega), hn]
  have vU₅ : wv u₅.mem B (VG.Proof.Bignum.X86_64.slot w fU) w = wv s.mem B (VG.Proof.Bignum.X86_64.slot w fU) w :=
    f15.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega)
  have vV₅ : wv u₅.mem B (VG.Proof.Bignum.X86_64.slot w fV) w = N := by
    rw [f₅.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega),
      f₄.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega),
      f₃.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega), c₂,
      f₁.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega), hn]
  have vX₁₅ : wv u₅.mem B (VG.Proof.Bignum.X86_64.slot w fX₁) w = 1 := by
    rw [f₅.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega), vX₁]
  have vX₂₅ : wv u₅.mem B (VG.Proof.Bignum.X86_64.slot w fX₂) w = 0 := by
    have := wv_add u₅.mem B (VG.Proof.Bignum.X86_64.slot w fX₂) w 2; omega
  have vU0₅ : VG.Proof.Bignum.X86_64.word u₅.mem B (VG.Proof.Bignum.X86_64.slot w fU + 8 * w) = 0 := by
    rw [f15.rg_wordA hZ16 (by simp) (by decide) (by decide) (by omega)]; exact hU0
  -- The inverse: `v = gcd(u, n)`.
  refine WP.seq (WP.mono (inverse_ok h₅.scr h₅.rdi h₅.hw h₅.hS (by omega) hw2 hZ
    (iU := fU) (iV := fV) (iX₁ := fX₁) (iX₂ := fX₂) (iM := aN) (iT := fT) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    vU0₅ (by rw [vV₅, vN₅]) vX₁₅ vX₂₅) fun u₆ ⟨_, f₆', k₆, hv₆⟩ => ?_)
  have f₆ : Frm B (VG.Proof.Rsa.X86_64.rg w [fU, fV, fX₁, fX₂, fT] [sMo]) u₅.mem u₆.mem := f₆'.widen (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact VG.Proof.Rsa.X86_64.rg_cover_arr _ (by decide) (Nat.le_refl _) (by omega)
    · exact VG.Proof.Rsa.X86_64.rg_cover_arr _ (by decide) (Nat.le_refl _) (by omega)
    · exact VG.Proof.Rsa.X86_64.rg_cover_arr _ (by decide) (Nat.le_refl _) (by omega)
    · exact VG.Proof.Rsa.X86_64.rg_cover_arr _ (by decide) (Nat.le_refl _) (by omega)
    · exact VG.Proof.Rsa.X86_64.rg_cover_arr _ (by decide) (Nat.le_refl _) (Nat.le_refl _)
    · exact VG.Proof.Rsa.X86_64.rg_cover_hdr _ (by decide))
  have h₆ := h₅.congrG f₆ (by decide) k₆ (by decide)
  rw [vN₅, vU₅] at hv₆
  obtain ⟨hg₆, -, -⟩ := hv₆ hodd hN1
  have vN₆ : wv u₆.mem B (VG.Proof.Bignum.X86_64.slot w aN) w = N := by
    rw [f₆.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega), vN₅]
  -- `q = n / v`.
  refine WP.seq (WP.mono (zeroA_ok h₆ (j := fQ) (by decide)) fun u₇ ⟨_, o₇, k₇⟩ => ?_)
  have f₇ : Frm B (VG.Proof.Rsa.X86_64.rg w [fQ] []) u₆.mem u₇.mem := Frm.rg_of_out o₇ (Nat.le_refl _) _ _ (by decide)
  have h₇ := h₆.congrG f₇ (by simp) k₇ (by decide)
  refine WP.seq (WP.mono (copyA_ok h₇ (o := fQ) (a := aN) (by decide) (by decide) (by decide))
    fun u₈ ⟨c₈, o₈, k₈⟩ => ?_)
  have f₈ : Frm B (VG.Proof.Rsa.X86_64.rg w [fQ] []) u₇.mem u₈.mem := Frm.rg_of_out o₈ (by omega) _ _ (by decide)
  have h₈ := h₇.congrG f₈ (by simp) k₈ (by decide)
  have vQ₈ : wv u₈.mem B (VG.Proof.Bignum.X86_64.slot w fQ) w = N := by
    rw [c₈, f₇.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega), vN₆]
  have vV₈ : wv u₈.mem B (VG.Proof.Bignum.X86_64.slot w fV) w = Nat.gcd (wv s.mem B (VG.Proof.Bignum.X86_64.slot w fU) w) N := by
    rw [f₈.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega),
      f₇.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega), hg₆]
  have hg0 : 0 < Nat.gcd (wv s.mem B (VG.Proof.Bignum.X86_64.slot w fU) w) N := Nat.gcd_pos_of_pos_right _ (by omega)
  refine WP.mono (divmod_ok h₈.scr h₈.rdi h₈.hw h₈.hS (by omega) hw2 hZ (iQ := fQ) (iR := fR) (iD := fV) (iT := fT)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)) fun u ⟨_, f₉', k₉, hv₉⟩ => ?_
  have f₉ : Frm B (VG.Proof.Rsa.X86_64.rg w [fQ, fR, fT] []) u₈.mem u.mem := f₉'.widen (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact VG.Proof.Rsa.X86_64.rg_cover_arr _ (by decide) (Nat.le_refl _) (Nat.le_refl _)
    · exact VG.Proof.Rsa.X86_64.rg_cover_arr _ (by decide) (Nat.le_refl _) (Nat.le_refl _)
    · exact VG.Proof.Rsa.X86_64.rg_cover_arr _ (by decide) (Nat.le_refl _) (Nat.le_refl _))
  rw [vV₈, vQ₈] at hv₉
  obtain ⟨-, hq₉⟩ := hv₉ hg0
  refine ⟨?_, ?_, h₈.congrG f₉ (by simp) k₉ (by decide), ?_, hq₉, ?_⟩
  · exact (((((f15.rg_trans f₆).rg_trans f₇).rg_trans f₈).rg_trans f₉)).rg_mono (by decide) (by decide)
  · exact ((((((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k₆).trans k₇).trans k₈).trans k₉).mono
      (by decide)
  · rw [f₉.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega), vV₈]
  · rw [f₉.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega),
      f₈.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega),
      f₇.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega), vN₆]

/-- The bases of a comparison of `[a]` and `[b]`, `w` and no borrow. -/
theorem ltSet_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) (a b : Nat) :
    WP isa (.block (VG.Impl.Rsa.X86_64.Keys.ws ++ base a .rbx ++ base b .r10 ++ ([.mov32 .rbp (.imm 0)] : List Instr))) s fun t =>
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .rbx = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w a) ∧ t.gpr .r10 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w b) ∧
      t.gpr .rbp = VG.Proof.Bignum.X86_64.mask false ∧ t.mem = s.mem ∧ VG.Proof.MlKem.X86_64.Keep [.r12, .r9, .rbx, .r10, .rbp] s t := by
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono h.ws_ok fun t₁ ⟨h12, h9, m₁, k₁⟩ => WP.block_append_iff.mpr ?_
  have hdi₁ : t₁.gpr .rdi = B := (k₁.gpr (by decide)).trans h.rdi
  refine WP.mono (base_ok a (r := .rbx) (by decide) hdi₁ h9) fun t₂ ⟨hbx, m₂, k₂⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (base_ok b (r := .r10) (by decide) ((k₂.gpr (by decide)).trans hdi₁)
    ((k₂.gpr (by decide)).trans h9)) fun t₃ ⟨h10, m₃, k₃⟩ => ?_
  refine WP.mono (WP.keep [.rbp] (Q := fun t => t.gpr .rbp = VG.Proof.Bignum.X86_64.mask false ∧ t.mem = t₃.mem) (by xrun) rfl)
    fun t ⟨⟨hbp, mt⟩, k₄⟩ => ⟨?_, ?_, (k₄.gpr (by decide)).trans h10, hbp, by rw [mt, m₃, m₂, m₁],
      (((k₁.trans k₂).trans k₃).trans k₄).mono (by decide)⟩
  · exact (k₄.gpr (by decide)).trans ((k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans h12))
  · exact (k₄.gpr (by decide)).trans ((k₃.gpr (by decide)).trans hbx)

/-- The larger of `[fV]` and `[fQ]` into `fV`, the smaller into `fQ`. -/
theorem finC_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) :
    WP isa (seqs [.block (VG.Impl.Rsa.X86_64.Keys.ws ++ base fV .rbx ++ base fQ .r10 ++ ([.mov32 .rbp (.imm 0)] : List Instr)), wordLoop 0 ltBody,
      .block [.mov .r15 (.reg .rbp)], wordLoop 0 cswapBody]) s fun u =>
      Frm B (VG.Proof.Rsa.X86_64.rg w [fV, fQ] []) s.mem u.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs s u ∧ Ws u B Z w ∧
      wv u.mem B (VG.Proof.Bignum.X86_64.slot w fV) w = max (wv s.mem B (VG.Proof.Bignum.X86_64.slot w fV) w) (wv s.mem B (VG.Proof.Bignum.X86_64.slot w fQ) w) ∧
      wv u.mem B (VG.Proof.Bignum.X86_64.slot w fQ) w = min (wv s.mem B (VG.Proof.Bignum.X86_64.slot w fV) w) (wv s.mem B (VG.Proof.Bignum.X86_64.slot w fQ) w) := by
  have hw1 := h.w1
  have hw2 := h.w2
  have sV := h.sl (j := fV) (by decide)
  have sQ := h.sl (j := fQ) (by decide)
  have sep := slot_far (w := w) (show fV ≠ fQ by decide)
  simp only [seqs]
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86_64.ltSet_ok h fV fQ) fun u₁ ⟨h12, hbx, h10, hbp, m₁, k₁⟩ => ?_)
  have hs₁ := h.scr.congr k₁.2.2
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86_64.lt_ok hs₁ hbx h10 h12 hbp (by omega) (by omega) (by omega) (by omega))
    fun u₂ ⟨hbp₂, m₂, k₂⟩ => ?_)
  rw [m₁] at hbp₂
  refine WP.seq (WP.mono (WP.keep [.r15] (Q := fun u => u.gpr .r15 = u₂.gpr .rbp ∧ u.mem = u₂.mem) (by xrun) rfl)
    fun u₃ ⟨⟨h15, m₃⟩, k₃⟩ => ?_)
  have k13 := (k₂.trans k₃)
  refine WP.mono (VG.Proof.Rsa.X86_64.cswap_ok (hs₁.congr k13.2.2) ((k13.gpr (by decide)).trans hbx) ((k13.gpr (by decide)).trans h10)
    (h15.trans hbp₂) ((k13.gpr (by decide)).trans h12) (by omega) (by omega) (by omega) (by omega) (by omega))
    fun u ⟨hx, hy, f₄', k₄⟩ => ?_
  rw [m₃, m₂, m₁] at hx hy f₄'
  have f₄ : Frm B (VG.Proof.Rsa.X86_64.rg w [fV, fQ] []) s.mem u.mem := f₄'.widen (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.Proof.Rsa.X86_64.rg_cover_arr _ (by decide) (Nat.le_refl _) (by omega)
    · exact VG.Proof.Rsa.X86_64.rg_cover_arr _ (by decide) (Nat.le_refl _) (by omega))
  refine ⟨f₄, (((k₁.trans k₂).trans k₃).trans k₄).mono (by decide),
    h.congrG f₄ (by simp) ((((k₁.trans k₂).trans k₃).trans k₄)) (by decide), ?_, ?_⟩
  · rw [hx]; split <;> rename_i hc <;> simp only [decide_eq_true_eq] at hc <;> omega
  · rw [hy]; split <;> rename_i hc <;> simp only [decide_eq_true_eq] at hc <;> omega

end VG.Proof.Rsa.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rsa.X86_64.RpOut`. -/
section

/-!
# `vg_rsa_recover_primes` on x86-64: the outputs

`p` and `q`, masked, to their outputs and the mask's low bit returned
(`rpStores_ok`); zeros and 0 if no candidate was tried (`rpFail_ok`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64

/-- The stores of `p` (`fV`) and `q` (`fQ`), and the exit. -/
theorem rpStores_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {k el dl : Nat}
    {pP pQ pN pE pD : Addr} {sv : Nat → BitVec 64} (ha : VG.Proof.Rsa.X86_64.RpArgs s.mem B k el dl pP pQ pN pE pD sv) {c : Bool}
    (hm : VG.Proof.Bignum.X86_64.word s.mem B (8 * Impl.Bignum.X86_64.Public.sMask) = VG.Proof.Bignum.X86_64.mask c) (hk1 : 1 ≤ k) (hk2 : k ≤ 8 * w)
    (oP : OutOk s B Z pP k) (oQ : OutOk s B Z pQ k) (a : VG.Proof.Rsa.X86_64.Apart pP k pQ k) :
    WP isa (seqs (storeA fV sP Impl.Bignum.X86_64.Public.sK Impl.Bignum.X86_64.Public.sMask ++
      (storeA fQ sQ Impl.Bignum.X86_64.Public.sK Impl.Bignum.X86_64.Public.sMask ++
        ([.block retMask] : List (Prog isa))))) s fun t =>
      (List.range k).map (fun i => t.mem (pP + BitVec.ofNat 64 i)) =
        Spec.Rsa.i2osp (if c then wv s.mem B (VG.Proof.Bignum.X86_64.slot w fV) ((k + 7) / 8) else 0) k ∧
      (List.range k).map (fun i => t.mem (pQ + BitVec.ofNat 64 i)) =
        Spec.Rsa.i2osp (if c then wv s.mem B (VG.Proof.Bignum.X86_64.slot w fQ) ((k + 7) / 8) else 0) k ∧
      t.gpr .rax = BitVec.ofNat 64 c.toNat ∧ (∀ i < 6, t.gpr (saved.getD i .rax) = sv i) ∧
      (∀ x, (∀ i < k, x ≠ pP + BitVec.ofNat 64 i) → (∀ i < k, x ≠ pQ + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧
      VG.Proof.MlKem.X86_64.Keep mmRegs s t := by
  have hn := h.scr.nowrap
  have h256 := h.h256
  have hZ := h.hZ
  have sl : ∀ j < 16, VG.Proof.Bignum.X86_64.slot w j + 8 * (w + 2) ≤ Z := fun j hj => h.sl hj
  have fw : ∀ {m m' : Mem}, Frm B [(Z, 2 ^ 64)] m m' → ∀ i < 32, VG.Proof.Bignum.X86_64.word m' B (8 * i) = VG.Proof.Bignum.X86_64.word m B (8 * i) :=
    fun hf i hi => hf.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact Or.inl (by omega)) (by omega)
  have fv : ∀ {m m' : Mem}, Frm B [(Z, 2 ^ 64)] m m' → ∀ j < 16, ∀ n ≤ w + 2,
      wv m' B (VG.Proof.Bignum.X86_64.slot w j) n = wv m B (VG.Proof.Bignum.X86_64.slot w j) n := fun hf j hj n hn' =>
    hf.wv_eq (fun r hr => by rw [List.mem_singleton.mp hr]; have := sl j hj; exact Or.inl (by omega))
      (by have := sl j hj; omega)
  refine wp_seqs_append (by simp [storeA]) (by simp [storeA]) (WP.mono (storeA_ws h (by decide) (by decide)
    (by decide) ha.p ha.k hm hk1 hk2 oP.wr oP.sep) fun s₁ ⟨b₁, x₁, h₁, f₁, k₁⟩ => ?_)
  have hm₁ : VG.Proof.Bignum.X86_64.word s₁.mem B (8 * Impl.Bignum.X86_64.Public.sMask) = VG.Proof.Bignum.X86_64.mask c := by rw [fw f₁ _ (by decide)]; exact hm
  refine wp_seqs_append (by simp [storeA]) (by simp) (WP.mono (storeA_ws h₁ (by decide) (by decide)
    (by decide) (by rw [fw f₁ _ (by decide)]; exact ha.q) (by rw [fw f₁ _ (by decide)]; exact ha.k) hm₁ hk1 hk2
    (fun i hi => by rw [k₁.2.2]; exact oQ.wr i hi) oQ.sep) fun s₂ ⟨b₂, x₂, h₂, f₂, k₂⟩ => ?_)
  have hm₂ : VG.Proof.Bignum.X86_64.word s₂.mem B (8 * Impl.Bignum.X86_64.Public.sMask) = VG.Proof.Bignum.X86_64.mask c := by rw [fw f₂ _ (by decide)]; exact hm₁
  simp only [seqs]
  refine WP.mono (cvExit_ok h₂ hm₂) fun t ⟨hax, hsv, hmt, k₃⟩ => ?_
  rw [hmt]
  refine ⟨?_, ?_, hax, fun i hi => ?_, fun x n1 n2 => by rw [x₂ x n2, x₁ x n1],
    ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  · rw [← b₁]
    exact List.map_congr_left fun i hi => by
      have hi' := List.mem_range.mp hi
      rw [x₂ _ (fun j hj => a i hi' j hj)]
  · rw [fv f₁ _ (by decide) _ (by omega)] at b₂
    exact b₂
  · rw [hsv i hi, fw f₂ _ (by omega), fw f₁ _ (by omega)]
    exact ha.saved i hi

/-- `fail`: zeros to `p` and `q`, 0 returned, and the saved registers
restored. -/
theorem rpFail_ok {s : State} {B : Addr} {Z : Nat} (hs : VG.Proof.Bignum.X86_64.Scr s B Z) (hdi : s.gpr .rdi = B) (hZ : 8 * 32 ≤ Z)
    {k el dl : Nat} {pP pQ pN pE pD : Addr} {sv : Nat → BitVec 64}
    (ha : VG.Proof.Rsa.X86_64.RpArgs s.mem B k el dl pP pQ pN pE pD sv) (hk1 : 1 ≤ k) (hk2 : k < 2 ^ 31)
    (oP : OutOk s B Z pP k) (oQ : OutOk s B Z pQ k) (a : VG.Proof.Rsa.X86_64.Apart pP k pQ k) :
    WP isa fail s fun t =>
      (∀ i < k, t.mem (pP + BitVec.ofNat 64 i) = 0) ∧ (∀ i < k, t.mem (pQ + BitVec.ofNat 64 i) = 0) ∧
      t.gpr .rax = 0 ∧ (∀ i < 6, t.gpr (saved.getD i .rax) = sv i) ∧
      (∀ x, (∀ i < k, x ≠ pP + BitVec.ofNat 64 i) → (∀ i < k, x ≠ pQ + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧
      t.gpr .rsp = s.gpr .rsp := by
  have hn := hs.nowrap
  have fw : ∀ {m m' : Mem} {op : Addr} {len : Nat}, (∀ j < len, Z ≤ VG.Proof.Bignum.X86_64.ofs B (op + BitVec.ofNat 64 j)) →
      (∀ x, (∀ j < len, x ≠ op + BitVec.ofNat 64 j) → m' x = m x) → ∀ i < 32, VG.Proof.Bignum.X86_64.word m' B (8 * i) = VG.Proof.Bignum.X86_64.word m B (8 * i) :=
    fun hsep hx i hi => (frm_scr hsep hx).word_eq (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Or.inl (by omega)) (by omega)
  unfold fail
  simp only [seqs]
  refine WP.seq (WP.mono (zeroOut_ok hs hdi hZ (by decide) (by decide) ha.p ha.k hk1 hk2 oP)
    fun s₁ ⟨z₁, x₁, k₁⟩ => ?_)
  have w₁ := fw oP.sep x₁
  have hs₁ := hs.congr k₁.2.2
  have hdi₁ : s₁.gpr .rdi = B := (k₁.gpr (by decide)).trans hdi
  refine WP.seq (WP.mono (zeroOut_ok hs₁ hdi₁ hZ (by decide) (by decide) (by rw [w₁ _ (by decide)]; exact ha.q)
    (by rw [w₁ _ (by decide)]; exact ha.k) hk1 hk2 ⟨fun i hi => by rw [k₁.2.2]; exact oQ.wr i hi, oQ.sep⟩)
    fun s₂ ⟨z₂, x₂, k₂⟩ => ?_)
  have w₂ := fw oQ.sep x₂
  have hs₂ := hs₁.congr k₂.2.2
  have hdi₂ : s₂.gpr .rdi = B := (k₂.gpr (by decide)).trans hdi₁
  have hl₂ : ∀ i < 32, InRegions (s₂.rd ++ s₂.wr) (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi => hs₂.ld (by omega)
  have hw : ∀ i < 32, VG.Proof.Bignum.X86_64.word s₂.mem B (8 * i) = VG.Proof.Bignum.X86_64.word s.mem B (8 * i) := fun i hi => by
    rw [w₂ i hi, w₁ i hi]
  rw [exit_eq]
  refine WP.mono (WP.keep [.rax, .rbx, .rbp, .r12, .r13, .r14, .r15] (Q := fun t =>
      t.gpr .rax = 0 ∧ t.gpr .rbx = VG.Proof.Bignum.X86_64.word s.mem B (8 * 0) ∧
      t.gpr .rbp = VG.Proof.Bignum.X86_64.word s.mem B (8 * 1) ∧ t.gpr .r12 = VG.Proof.Bignum.X86_64.word s.mem B (8 * 2) ∧
      t.gpr .r13 = VG.Proof.Bignum.X86_64.word s.mem B (8 * 3) ∧ t.gpr .r14 = VG.Proof.Bignum.X86_64.word s.mem B (8 * 4) ∧
      t.gpr .r15 = VG.Proof.Bignum.X86_64.word s.mem B (8 * 5) ∧ t.mem = s₂.mem) (by
    simp only [List.cons_append, List.nil_append]
    xrun [State.ea, hdr, hdi₂, hdrOff, hl₂ 0 (by decide), hl₂ 1 (by decide), hl₂ 2 (by decide),
      hl₂ 3 (by decide), hl₂ 4 (by decide), hl₂ 5 (by decide), hw 0 (by decide), hw 1 (by decide),
      hw 2 (by decide), hw 3 (by decide), hw 4 (by decide), hw 5 (by decide)]) rfl)
    fun t ⟨⟨hax, h0, h1, h2, h3, h4, h5, hm⟩, k₃⟩ => ?_
  have kk := (k₁.trans k₂).trans k₃
  rw [hm]
  refine ⟨fun i hi => ?_, z₂, hax, fun i hi => ?_, fun x n1 n2 => by rw [x₂ x n2, x₁ x n1],
    kk.gpr (by decide)⟩
  · rw [x₂ _ (fun j hj => a i hi j hj)]
    exact z₁ i hi
  · rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
    · exact h0.trans (ha.saved 0 (by decide))
    · exact h1.trans (ha.saved 1 (by decide))
    · exact h2.trans (ha.saved 2 (by decide))
    · exact h3.trans (ha.saved 3 (by decide))
    · exact h4.trans (ha.saved 4 (by decide))
    · exact h5.trans (ha.saved 5 (by decide))

end VG.Proof.Rsa.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rsa.X86_64.RpRest`. -/
section

/-!
# `vg_rsa_recover_primes` on x86-64: `rest`

From `M = m = d e - 1`, even and positive, and `-n⁻¹` in the header: the
halvings, Montgomery form, the candidates and the factors (`rpRest_ok`):
`recoverPrimes.go`'s result and the factors written masked by it.
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aR2 aXm aY aOne sCnt sMask)
open VG.Spec.Rsa (splitTwos recoverStep recoverPrimes recoverTries)

/-- The halvings' frame, as arrays and slots. -/
theorem frm_halving {B : Addr} {w : Nat} {m m' : Mem}
    (h : Frm B [(VG.Proof.Bignum.X86_64.slot w aM, 16 * (w + 2)), (VG.Proof.Bignum.X86_64.slot w aH, 16 * (w + 2)), (8 * sT, 8)] m m') :
    Frm B (VG.Proof.Rsa.X86_64.rg w [aM, aM + 1, aH, aH + 1] [sT]) m m' := fun x hx => h x fun r hr => by
  have eM := VG.Proof.Rsa.X86_64.slot_add w aM 1
  have eH := VG.Proof.Rsa.X86_64.slot_add w aH 1
  have a := hx _ (VG.Proof.Rsa.X86_64.rg_mem_arr (w := w) (j := aM) [sT] (by decide))
  have b := hx _ (VG.Proof.Rsa.X86_64.rg_mem_arr (w := w) (j := aM + 1) [sT] (by decide))
  have c := hx _ (VG.Proof.Rsa.X86_64.rg_mem_arr (w := w) (j := aH) [sT] (by decide))
  have d := hx _ (VG.Proof.Rsa.X86_64.rg_mem_arr (w := w) (j := aH + 1) [sT] (by decide))
  have e := hx _ (VG.Proof.Rsa.X86_64.rg_mem_hdr (w := w) [aM, aM + 1, aH, aH + 1] (show sT ∈ [sT] by decide))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  dsimp only at a b c d e
  rcases hr with rfl | rfl | rfl <;> dsimp only <;> omega

/-- What `rest` needs. -/
structure RestPre (I : VG.Proof.Rsa.X86_64.RpIn) (m₀ : Mem) (N m : Nat) (s : State) : Prop where
  S : VG.Proof.Rsa.X86_64.RpS I m₀ s
  L : VG.Proof.Rsa.X86_64.RpLens I
  odd : N % 2 = 1
  lo : 2 ^ (64 * (wk I.k - 1)) ≤ N
  n : wv s.mem I.B (VG.Proof.Bignum.X86_64.slot (wk I.k) aN) (wk I.k) = N
  inv : ((VG.Proof.Bignum.X86_64.word s.mem I.B (VG.Proof.Bignum.X86_64.slot (wk I.k) aN)).toNat * (VG.Proof.Bignum.X86_64.word s.mem I.B (8 * sMinv)).toNat + 1) % 2 ^ 64 = 0
  M : wv s.mem I.B (VG.Proof.Bignum.X86_64.slot (wk I.k) aM) (2 * (wk I.k + 2)) = m
  m0 : 0 < m
  even : m % 2 = 0
  mlt : m < 2 ^ (64 * (wk I.k + (I.el + 7) / 8))
  oP : OutOk s I.B I.Z I.pP I.k
  oQ : OutOk s I.B I.Z I.pQ I.k
  a : VG.Proof.Rsa.X86_64.Apart I.pP I.k I.pQ I.k

theorem rest_eq (mul : Nat → Nat → Nat → Prog isa) : VG.Impl.Rsa.X86_64.Keys.Recover.rest mul = seqs ([halving] ++ (mont mul ++ ([candLoop mul] ++
    (([.block [.mov .rax (.mem (hdr sC3)), .store (hdr sMask) .rax], mul aY aY aOne, zeroA fU,
      .block (VG.Impl.Rsa.X86_64.Keys.ws ++ base aY .r8 ++ base aOne .r10 ++ base fU .rsi ++ ([.mov32 .rbp (.imm 0)] : List Instr)),
      wordLoop 0 subBody] : List (Prog isa)) ++
    ([zeroA fV, copyA fV aN, zeroA fX₁, .block (setOneA fX₁), zeroA fX₂, inverse fU fV fX₁ fX₂ aN fT,
      zeroA fQ, copyA fQ aN, divmod fQ fR fV fT] ++
    (([.block (VG.Impl.Rsa.X86_64.Keys.ws ++ base fV .rbx ++ base fQ .r10 ++ ([.mov32 .rbp (.imm 0)] : List Instr)), wordLoop 0 ltBody,
      .block [.mov .r15 (.reg .rbp)], wordLoop 0 cswapBody] : List (Prog isa)) ++
    (storeA fV sP Impl.Bignum.X86_64.Public.sK Impl.Bignum.X86_64.Public.sMask ++
      (storeA fQ sQ Impl.Bignum.X86_64.Public.sK Impl.Bignum.X86_64.Public.sMask ++
        ([.block retMask] : List (Prog isa)))))))))) := by
  simp only [VG.Impl.Rsa.X86_64.Keys.Recover.rest, VG.Impl.Rsa.X86_64.Keys.Recover.fin, List.append_assoc, List.cons_append, List.nil_append]

/-- `rest`: `recoverPrimes.go`'s result, and `p` and `q` written masked by
it. -/
theorem rpRest_ok (M : Mont) {I : VG.Proof.Rsa.X86_64.RpIn} {m₀ : Mem} {N m : Nat} {s : State} (h : VG.Proof.Rsa.X86_64.RestPre I m₀ N m s) :
    WP isa (VG.Impl.Rsa.X86_64.Keys.Recover.rest M.mm) s fun u => ∃ res : Option Nat, ∃ cnt : Nat,
      recoverPrimes.go N (splitTwos m).1 (splitTwos m).2 recoverTries = (res.map (VG.Proof.Rsa.X86_64.pqOf N), cnt) ∧
      (List.range I.k).map (fun i => u.mem (I.pP + BitVec.ofNat 64 i)) =
        Spec.Rsa.i2osp (match res with | some y => (VG.Proof.Rsa.X86_64.pqOf N y).1 | none => 0) I.k ∧
      (List.range I.k).map (fun i => u.mem (I.pQ + BitVec.ofNat 64 i)) =
        Spec.Rsa.i2osp (match res with | some y => (VG.Proof.Rsa.X86_64.pqOf N y).2 | none => 0) I.k ∧
      u.gpr .rax = BitVec.ofNat 64 res.isSome.toNat ∧ (∀ i < 6, u.gpr (saved.getD i .rax) = I.sv i) ∧
      (∀ x, I.Z ≤ VG.Proof.Bignum.X86_64.ofs I.B x → (∀ i < I.k, x ≠ I.pP + BitVec.ofNat 64 i) →
        (∀ i < I.k, x ≠ I.pQ + BitVec.ofNat 64 i) → u.mem x = m₀ x) ∧
      u.gpr .rsp = I.sp := by
  have L := h.L
  have hk1 := L.k1
  have hk2 := L.k2
  have hel1 := L.el1
  have hel2 := L.el2
  have S := h.S
  have hZ16 : VG.Proof.Bignum.X86_64.slot (wk I.k) 16 ≤ 2 ^ 64 := by have := S.ws.scr.nowrap; have := S.ws.hZ; omega
  have hw1 := S.ws.w1
  have hN1 : 1 < N := by
    have : 2 ^ 64 ≤ 2 ^ (64 * (wk I.k - 1)) := Nat.pow_le_pow_right (by decide) (by omega)
    have := h.lo; omega
  rw [VG.Proof.Rsa.X86_64.rest_eq]
  -- The halvings.
  refine wp_seqs_append (by simp) (by simp [mont]) (WP.mono (VG.Proof.Rsa.X86_64.halving_ok S.ws S.args.el hel1
    (by unfold wk; omega) h.M h.m0 h.mlt) fun s₁ ⟨_, hr₁, ht₁, hf₁', k₁⟩ => ?_)
  have hf₁ := VG.Proof.Rsa.X86_64.frm_halving hf₁'
  have S₁ := S.step hf₁ (by decide) (by decide) k₁ (by decide)
  have hn₁ : wv s₁.mem I.B (VG.Proof.Bignum.X86_64.slot (wk I.k) aN) (wk I.k) = N := by
    rw [hf₁.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega)]; exact h.n
  have hi₁ : ((VG.Proof.Bignum.X86_64.word s₁.mem I.B (VG.Proof.Bignum.X86_64.slot (wk I.k) aN)).toNat * (VG.Proof.Bignum.X86_64.word s₁.mem I.B (8 * sMinv)).toNat + 1) % 2 ^ 64 = 0 := by
    rw [hf₁.rg_word0 hZ16 (by decide) (by decide) (by decide), hf₁.rg_word (by decide) (by decide)]; exact h.inv
  -- Montgomery form.
  refine wp_seqs_append (by simp [mont]) (by simp) (WP.mono (VG.Proof.Rsa.X86_64.mont_ok M S₁.ws hi₁ hn₁ h.odd h.lo)
    fun s₂ ⟨_, hr2lt, hr2, hone, ho, hng, hf₂, k₂⟩ => ?_)
  have S₂ := S₁.step hf₂ (by decide) (by decide) k₂ (by decide)
  have hspl := VG.Proof.Rsa.splitTwos_spec h.m0
  have hrlt : (splitTwos m).2 < 2 ^ (64 * (wk I.k + (I.el + 7) / 8)) := by
    have : (splitTwos m).2 ≤ m :=
      calc (splitTwos m).2 ≤ 2 ^ (splitTwos m).1 * (splitTwos m).2 := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
        _ = m := hspl.1.symm
    have := h.mlt; omega
  have ht1 : 1 ≤ (splitTwos m).1 := by
    rcases Nat.eq_zero_or_pos (splitTwos m).1 with h0 | h0
    · have := hspl.1; rw [h0, Nat.pow_zero, Nat.one_mul] at this; have := hspl.2; have := h.even; omega
    · exact h0
  have ht2 := VG.Proof.Rsa.splitTwos_lt h.m0 h.mlt
  have hc₂ : VG.Proof.Rsa.X86_64.Cst s₂ I.B I.Z (wk I.k) (VG.Proof.Bignum.X86_64.word s₂.mem I.B (8 * sMinv)) N I.el (splitTwos m).2 (splitTwos m).1 := by
    refine ⟨S₂.ws, rfl, ?_, ?_, hr2lt, hr2, hone, ho, hng, S₂.args.el, ?_, ?_, h.odd, h.lo, hel1,
      by unfold wk; omega, ht1, ht2⟩
    · rw [hf₂.rg_word0 hZ16 (by decide) (by decide) (by decide), hf₂.rg_word (by decide) (by decide)]; exact hi₁
    · rw [hf₂.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega)]; exact hn₁
    · rw [hf₂.rg_wv2 hZ16 (by decide) (by decide) (by decide) (by decide) (by unfold wk; omega)]
      rw [wv_low_of_lt (v := wk I.k + (I.el + 7) / 8) (w := 2 * (wk I.k + 2)) (by unfold wk; omega)
        (by rw [hr₁]; exact hrlt), hr₁]
    · rw [hf₂.rg_word (by decide) (by decide)]; exact ht₁
  -- The candidates.
  refine wp_seqs_append (by simp) (by simp) (WP.mono (VG.Proof.Rsa.X86_64.candLoop_ok M hc₂)
    fun s₃ ⟨res, cnt, hgo, _, hc3, hy, hf₃, k₃⟩ => ?_)
  have S₃ := S₂.step hf₃ (by decide) (by decide) k₃ (by decide)
  have hc₃ := hc₂.congr hf₃ (by decide) VG.Proof.Rsa.X86_64.cand_hs k₃ (by decide)
  -- `u = y - 1`.
  refine wp_seqs_append (by simp) (by simp) (WP.mono (VG.Proof.Rsa.X86_64.finA_ok M hc₃ hc3 (res := res) fun y hres => by
    obtain ⟨a, b, c⟩ := hy y hres
    refine ⟨a, b, ?_⟩
    rcases Nat.eq_zero_or_pos y with h0 | h0
    · rw [h0, Nat.zero_mul, Nat.zero_mod] at c; cases c
    · exact h0) fun s₄ ⟨hf₄, k₄, hm₄, hU0, hU⟩ => ?_)
  have S₄ := S₃.step hf₄ (by decide) (by decide) k₄ (by decide)
  have hn₄ : wv s₄.mem I.B (VG.Proof.Bignum.X86_64.slot (wk I.k) aN) (wk I.k) = N := by
    rw [hf₄.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega)]; exact hc₃.hn
  -- `p = gcd(u, n)`, `q = n / p`.
  refine wp_seqs_append (by simp) (by simp) (WP.mono (VG.Proof.Rsa.X86_64.finB_ok S₄.ws hn₄ h.odd hN1 hU0)
    fun s₅ ⟨hf₅, k₅, _, hv₅, hq₅, _⟩ => ?_)
  have S₅ := S₄.step hf₅ (by decide) (by decide) k₅ (by decide)
  -- The larger first.
  refine wp_seqs_append (by simp) (by simp [storeA]) (WP.mono (VG.Proof.Rsa.X86_64.finC_ok S₅.ws)
    fun s₆ ⟨hf₆, k₆, _, hv₆, hq₆⟩ => ?_)
  have S₆ := S₅.step hf₆ (by decide) (by simp) k₆ (by decide)
  have hm₆ : VG.Proof.Bignum.X86_64.word s₆.mem I.B (8 * sMask) = VG.Proof.Bignum.X86_64.mask res.isSome := by
    rw [hf₆.rg_word (by decide) (by simp), hf₅.rg_word (by decide) (by decide)]; exact hm₄
  -- The stores.
  refine WP.mono (VG.Proof.Rsa.X86_64.rpStores_ok S₆.ws S₆.args hm₆ (by omega) (by unfold wk; omega)
    ⟨fun i hi => by rw [S₆.wr, ← S.wr]; exact h.oP.wr i hi, h.oP.sep⟩
    ⟨fun i hi => by rw [S₆.wr, ← S.wr]; exact h.oQ.wr i hi, h.oQ.sep⟩ h.a)
    fun u ⟨bP, bQ, hax, hsv, hfr, k₇⟩ => ?_
  have hval : ∀ y, res = some y →
      wv s₆.mem I.B (VG.Proof.Bignum.X86_64.slot (wk I.k) fV) (wk I.k) = (VG.Proof.Rsa.X86_64.pqOf N y).1 ∧
      wv s₆.mem I.B (VG.Proof.Bignum.X86_64.slot (wk I.k) fQ) (wk I.k) = (VG.Proof.Rsa.X86_64.pqOf N y).2 := fun y hres => by
    rw [hv₆, hq₆, hv₅, hq₅, hU y hres]
    exact ⟨rfl, rfl⟩
  refine ⟨res, cnt, hgo, ?_, ?_, hax, hsv, fun x hx n1 n2 => by rw [hfr x n1 n2]; exact S₆.inScr x hx,
    (k₇.gpr (by decide)).trans S₆.rsp⟩
  · rw [bP]
    cases hres : res with
    | none => rfl
    | some y => simp only [Option.isSome_some, ite_true]; exact congrArg (Spec.Rsa.i2osp · I.k) (hval y hres).1
  · rw [bQ]
    cases hres : res with
    | none => rfl
    | some y => simp only [Option.isSome_some, ite_true]; exact congrArg (Spec.Rsa.i2osp · I.k) (hval y hres).2

end VG.Proof.Rsa.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rsa.X86_64.RpMain`. -/
section

/-!
# `vg_rsa_recover_primes` on x86-64: `main`

From a valid modulus, `main` loads `n`, `e` and `d`, computes `-n⁻¹` and
`M = d e`, and either writes zeros (`d e - 1` odd or not positive) or runs
`rest` (`rpMain_ok`): `recoverPrimes`'s result, written.
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aR2 aXm aY aOne sCnt sMask)
open VG.Spec.Rsa (splitTwos recoverStep recoverPrimes recoverTries)

/-- The inputs as numbers. -/
abbrev RpIn.N (I : VG.Proof.Rsa.X86_64.RpIn) : Nat := Spec.Rsa.os2ip I.nb
abbrev RpIn.E (I : VG.Proof.Rsa.X86_64.RpIn) : Nat := Spec.Rsa.os2ip I.eb
abbrev RpIn.D (I : VG.Proof.Rsa.X86_64.RpIn) : Nat := Spec.Rsa.os2ip I.db

/-- What `main` needs on entry. -/
structure RpPre (I : VG.Proof.Rsa.X86_64.RpIn) (s : State) : Prop where
  scr : VG.Proof.Bignum.X86_64.Scr s I.B I.Z
  rdi : s.gpr .rdi = I.B
  args : VG.Proof.Rsa.X86_64.RpArgs s.mem I.B I.k I.el I.dl I.pP I.pQ I.pN I.pE I.pD I.sv
  n : Src s I.B I.Z I.pN I.nb
  e : Src s I.B I.Z I.pE I.eb
  d : Src s I.B I.Z I.pD I.db
  L : VG.Proof.Rsa.X86_64.RpLens I
  oP : OutOk s I.B I.Z I.pP I.k
  oQ : OutOk s I.B I.Z I.pQ I.k
  a : VG.Proof.Rsa.X86_64.Apart I.pP I.k I.pQ I.k
  wr : s.wr = I.W
  rsp : s.gpr .rsp = I.sp

theorem rpMain_eq (mul : Nat → Nat → Nat → Prog isa) : VG.Impl.Rsa.X86_64.Keys.Recover.main mul = seqs (([.block CrtValues.head] : List (Prog isa)) ++
    ((loadA aN Impl.Bignum.X86_64.Public.sN Impl.Bignum.X86_64.Public.sK ++
      (loadA aE Impl.Bignum.X86_64.Public.sE Impl.Bignum.X86_64.Public.sElen ++ loadA aD sD sDl)) ++
    (([.block minvBlk] : List (Prog isa)) ++ (prod ++
    (([.block skipBlk, wordLoop 0 orBody, .block skipTest] : List (Prog isa)) ++
      ([.ite .ne fail (VG.Impl.Rsa.X86_64.Keys.Recover.rest mul)] : List (Prog isa))))))) := by
  simp only [VG.Impl.Rsa.X86_64.Keys.Recover.main, List.append_assoc, List.cons_append, List.nil_append]

/-- `head`: the working space, the mask all ones, and `RpS` from the
memory on entry to `main`. -/
theorem rpHeadS_ok {I : VG.Proof.Rsa.X86_64.RpIn} {s : State} (h : VG.Proof.Rsa.X86_64.RpPre I s) :
    WP isa (.block CrtValues.head) s fun t => VG.Proof.Rsa.X86_64.RpS I s.mem t := by
  have L := h.L
  have hZ := L.z
  refine WP.mono (cvHead_ok h.scr h.rdi L.k1 L.k2 hZ h.args.k) fun s₁ ⟨hw₁, _, f₁, k₁⟩ => ?_
  have eW : sW = 6 := rfl
  have eA : sArr 0 = 8 := rfl
  have eS : sStride = 28 := rfl
  have eM : Impl.Bignum.X86_64.Public.sMask = 22 := rfl
  have k1 := L.k1
  have hi₁ : InScr I.B I.Z s.mem s₁.mem := InScr.of_frm f₁ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> dsimp only <;> omega)
  exact ⟨hw₁, h.args.congr fun i hi => f₁.word_eq (fun r hr => by
      unfold VG.Proof.Rsa.X86_64.rArg at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> dsimp only <;> omega) (by unfold VG.Proof.Rsa.X86_64.rArg at hi; omega),
    h.n.congrK hi₁ k₁, h.e.congrK hi₁ k₁, h.d.congrK hi₁ k₁, hi₁, k₁.2.2.trans h.wr,
    (k₁.gpr (by decide)).trans h.rsp⟩

/-- The skip's frame, as arrays and slots. -/
theorem frm_skip {B : Addr} {w : Nat} {m m' : Mem} (h : Frm B [(VG.Proof.Bignum.X86_64.slot w aM, 8), (8 * sC2, 8)] m m') :
    Frm B (VG.Proof.Rsa.X86_64.rg w [aM] [sC2]) m m' := h.widen (by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact VG.Proof.Rsa.X86_64.rg_cover_arr _ (by decide) (Nat.le_refl _) (by omega)
  · exact VG.Proof.Rsa.X86_64.rg_cover_hdr _ (by decide))

/-- The factors written, or 0. -/
def fstOr : Option (Nat × Nat) → Nat
  | some v => v.1
  | none => 0

def sndOr : Option (Nat × Nat) → Nat
  | some v => v.2
  | none => 0

/-- The prefix of `main`, up to the check of `d e - 1`. -/
abbrev prefixList : List (Prog isa) := ([.block CrtValues.head] : List (Prog isa)) ++
    ((loadA aN Impl.Bignum.X86_64.Public.sN Impl.Bignum.X86_64.Public.sK ++
      (loadA aE Impl.Bignum.X86_64.Public.sE Impl.Bignum.X86_64.Public.sElen ++ loadA aD sD sDl)) ++
    (([.block minvBlk] : List (Prog isa)) ++ (prod ++
    ([.block skipBlk, wordLoop 0 orBody, .block skipTest] : List (Prog isa)))))

theorem rpMain_eq' (mul : Nat → Nat → Nat → Prog isa) :
    VG.Impl.Rsa.X86_64.Keys.Recover.main mul = seqs (VG.Proof.Rsa.X86_64.prefixList ++ ([.ite .ne fail (VG.Impl.Rsa.X86_64.Keys.Recover.rest mul)] : List (Prog isa))) := by
  simp only [VG.Impl.Rsa.X86_64.Keys.Recover.main, VG.Proof.Rsa.X86_64.prefixList, List.append_assoc, List.cons_append, List.nil_append]

/-- The prefix: `M = d e - (d e mod 2)`, `ZF` set if `d e` is odd and at
least 2, `n` and `-n⁻¹`. -/
theorem rpPrefix_ok {I : VG.Proof.Rsa.X86_64.RpIn} {s : State} (h : VG.Proof.Rsa.X86_64.RpPre I s) (hv : Spec.Rsa.modulusValid I.N I.k = true) :
    WP isa (seqs VG.Proof.Rsa.X86_64.prefixList) s fun s₅ => VG.Proof.Rsa.X86_64.RpS I s.mem s₅ ∧
      s₅.zf = some (decide (I.D * I.E % 2 = 1 ∧ 2 ≤ I.D * I.E)) ∧
      wv s₅.mem I.B (VG.Proof.Bignum.X86_64.slot (wk I.k) aM) (2 * (wk I.k + 2)) = I.D * I.E - I.D * I.E % 2 ∧
      wv s₅.mem I.B (VG.Proof.Bignum.X86_64.slot (wk I.k) aN) (wk I.k) = I.N ∧
      ((VG.Proof.Bignum.X86_64.word s₅.mem I.B (VG.Proof.Bignum.X86_64.slot (wk I.k) aN)).toNat * (VG.Proof.Bignum.X86_64.word s₅.mem I.B (8 * sMinv)).toNat + 1) % 2 ^ 64 = 0 ∧
      I.D * I.E < 2 ^ (64 * (wk I.k + (I.el + 7) / 8)) := by
  have L := h.L
  have k1 := L.k1
  have k2 := L.k2
  have hel1 := L.el1
  have hel2 := L.el2
  have hdl2 := L.dl2
  have hn := h.scr.nowrap
  have hZ := L.z
  obtain ⟨hNo, -⟩ := valid_lo hv
  have hEl : I.E < 2 ^ (64 * ((I.el + 7) / 8)) := by
    have := os2ip_lt I.eb; rw [L.ebl] at this; exact Nat.lt_of_lt_of_le this (pow256_le_wk I.el)
  have hDl : I.D < 2 ^ (64 * wk I.k) := by
    have := os2ip_lt I.db; rw [L.dbl] at this
    exact Nat.lt_of_lt_of_le this (by rw [pow256_eq]; exact Nat.pow_le_pow_right (by decide) (by unfold wk; omega))
  simp only [VG.Proof.Rsa.X86_64.prefixList]
  -- The head.
  refine wp_seqs_append (by simp) (by simp [loadA]) (WP.mono (VG.Proof.Rsa.X86_64.rpHeadS_ok h) fun s₁ S₁ => ?_)
  have hZ16 : VG.Proof.Bignum.X86_64.slot (wk I.k) 16 ≤ 2 ^ 64 := by have := S₁.ws.scr.nowrap; have := S₁.ws.hZ; omega
  -- The loads.
  refine wp_seqs_append (by simp [loadA]) (by simp) (WP.mono (VG.Proof.Rsa.X86_64.rpLoads_ok S₁ L)
    fun s₂ ⟨S₂, _, vN, vE, vD, _⟩ => ?_)
  -- `-n⁻¹`.
  refine wp_seqs_append (by simp) (by simp [prod]) (WP.mono (VG.Proof.Rsa.X86_64.minvBlk_ok S₂.ws (by
    rw [show (VG.Proof.Bignum.X86_64.word s₂.mem I.B (VG.Proof.Bignum.X86_64.slot (wk I.k) aN)).toNat % 2 = wv s₂.mem I.B (VG.Proof.Bignum.X86_64.slot (wk I.k) aN) (wk I.k) % 2 by
      rw [VG.Proof.Rsa.X86_64.wv_low (by have := S₂.ws.w1; omega)]; omega, vN]; exact hNo)) fun s₃ ⟨hi₃, f₃, k₃⟩ => ?_)
  have S₃ := S₂.step f₃ (by simp) (by decide) k₃ (by decide)
  -- `M = d e`.
  have vE₃ : wv s₃.mem I.B (VG.Proof.Bignum.X86_64.slot (wk I.k) aE) (wk I.k) = I.E := by
    rw [f₃.rg_wv hZ16 (by decide) (by decide) (by simp) (by omega), vE]
  have vD₃ : wv s₃.mem I.B (VG.Proof.Bignum.X86_64.slot (wk I.k) aD) (wk I.k) = I.D := by
    rw [f₃.rg_wv hZ16 (by decide) (by decide) (by simp) (by omega), vD]
  refine wp_seqs_append (by simp [prod]) (by simp) (WP.mono (prod_ok S₃.ws S₃.args.el hel1
    (by unfold wk; omega) (by rw [vE₃]; exact hEl)) fun s₄ ⟨vM₄, o₄, k₄⟩ => ?_)
  rw [vD₃, vE₃] at vM₄
  have sM := S₃.ws.sl (j := aM + 1) (by decide)
  have f₄ : Frm I.B (VG.Proof.Rsa.X86_64.rg (wk I.k) [aM, aM + 1] []) s₃.mem s₄.mem :=
    Frm.rg_of_out2 o₄ (Nat.le_refl _) _ _ (by decide) (by decide)
  have S₄ := S₃.step f₄ (by decide) (by simp) k₄ (by decide)
  have hDE : I.D * I.E < 2 ^ (64 * (wk I.k + (I.el + 7) / 8)) := by
    rw [Nat.mul_add, Nat.pow_add]; exact Nat.mul_lt_mul'' hDl hEl
  -- Whether `d e - 1` is even and positive.
  refine WP.mono (skip_ok S₄.ws S₄.args.el hel1 (by unfold wk; omega)
    (by rw [vM₄]; exact hDE)) fun s₅ ⟨hz₅, vM₅, f₅', _, k₅⟩ => ?_
  rw [vM₄] at hz₅ vM₅
  have f₅ := VG.Proof.Rsa.X86_64.frm_skip f₅'
  have S₅ := S₄.step f₅ (by decide) (by decide) k₅ (by decide)
  refine ⟨S₅, hz₅, vM₅, ?_, ?_, hDE⟩
  · rw [f₅.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega),
      f₄.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega),
      f₃.rg_wv hZ16 (by decide) (by decide) (by simp) (by omega), vN]
  · rw [f₅.rg_word0 hZ16 (by decide) (by decide) (by decide), f₅.rg_word (by decide) (by decide),
      f₄.rg_word0 hZ16 (by decide) (by decide) (by decide), f₄.rg_word (by decide) (by decide)]; exact hi₃

/-- `main`, from a valid modulus: `recoverPrimes`'s factors written, or
zeros. -/
theorem rpMain_ok (M : Mont) {I : VG.Proof.Rsa.X86_64.RpIn} {s : State} (h : VG.Proof.Rsa.X86_64.RpPre I s)
    (hv : Spec.Rsa.modulusValid I.N I.k = true) :
    WP isa (VG.Impl.Rsa.X86_64.Keys.Recover.main M.mm) s fun t => ∃ res : Option (Nat × Nat),
      (recoverPrimes I.N I.E I.D).1 = res ∧
      (List.range I.k).map (fun i => t.mem (I.pP + BitVec.ofNat 64 i)) =
        Spec.Rsa.i2osp (VG.Proof.Rsa.X86_64.fstOr res) I.k ∧
      (List.range I.k).map (fun i => t.mem (I.pQ + BitVec.ofNat 64 i)) =
        Spec.Rsa.i2osp (VG.Proof.Rsa.X86_64.sndOr res) I.k ∧
      t.gpr .rax = BitVec.ofNat 64 res.isSome.toNat ∧ (∀ i < 6, t.gpr (saved.getD i .rax) = I.sv i) ∧
      (∀ x, I.Z ≤ VG.Proof.Bignum.X86_64.ofs I.B x → (∀ i < I.k, x ≠ I.pP + BitVec.ofNat 64 i) →
        (∀ i < I.k, x ≠ I.pQ + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧
      t.gpr .rsp = s.gpr .rsp := by
  have L := h.L
  have k1 := L.k1
  have k2 := L.k2
  have hel1 := L.el1
  have hel2 := L.el2
  have hdl2 := L.dl2
  have hn := h.scr.nowrap
  have hZ := L.z
  obtain ⟨hNo, hlo⟩ := valid_lo hv
  have hlo' : 2 ^ (64 * (wk I.k - 1)) ≤ I.N := by
    refine Nat.le_trans ?_ hlo
    rw [pow256_eq]; exact Nat.pow_le_pow_right (by decide) (by unfold wk; omega)
  rw [VG.Proof.Rsa.X86_64.rpMain_eq']
  refine wp_seqs_append (by simp) (by simp) (WP.mono (VG.Proof.Rsa.X86_64.rpPrefix_ok h hv) fun s₅ ⟨S₅, hz₅, vM₅, vN₅, hi₅, hDE⟩ => ?_)
  have hspec : (I.D * I.E < 2 ∨ (I.D * I.E - 1) % 2 = 1) ↔ ¬(I.D * I.E % 2 = 1 ∧ 2 ≤ I.D * I.E) := by omega
  simp only [seqs]
  refine WP.ite (!decide (I.D * I.E % 2 = 1 ∧ 2 ≤ I.D * I.E)) (by simp [VG.X86_64.eval, hz₅]) (fun hb => ?_) (fun hb => ?_)
  · -- Zeros.
    have hb' : ¬(I.D * I.E % 2 = 1 ∧ 2 ≤ I.D * I.E) := by simp at hb; omega
    have hnone := VG.Proof.Rsa.recoverPrimes_none (n := I.N) (hspec.mpr hb')
    refine WP.mono (VG.Proof.Rsa.X86_64.rpFail_ok S₅.ws.scr S₅.ws.rdi (by omega) S₅.args (by omega) (by omega)
      ⟨fun i hi => by rw [S₅.wr, ← h.wr]; exact h.oP.wr i hi, h.oP.sep⟩
      ⟨fun i hi => by rw [S₅.wr, ← h.wr]; exact h.oQ.wr i hi, h.oQ.sep⟩ h.a)
      fun t ⟨z1, z2, hax, hsv, hfr, hsp⟩ => ⟨none, by rw [hnone], ?_, ?_, by rw [hax]; rfl, hsv,
        fun x hx n1 n2 => by rw [hfr x n1 n2]; exact S₅.inScr x hx, hsp.trans (S₅.rsp.trans h.rsp.symm)⟩
    · rw [List.map_congr_left fun i hi => z1 i (List.mem_range.mp hi)]; rw [VG.Proof.Rsa.X86_64.fstOr, i2osp_zero']; simp
    · rw [List.map_congr_left fun i hi => z2 i (List.mem_range.mp hi)]; rw [VG.Proof.Rsa.X86_64.sndOr, i2osp_zero']; simp
  · -- `rest`.
    have hb' : I.D * I.E % 2 = 1 ∧ 2 ≤ I.D * I.E := by simpa using hb
    have hgo := VG.Proof.Rsa.recoverPrimes_go (n := I.N) (fun h' => (hspec.mp h') hb')
    refine WP.mono (VG.Proof.Rsa.X86_64.rpRest_ok M (m := I.D * I.E - 1) (N := I.N) ⟨S₅, L, hNo, hlo', vN₅, hi₅,
      by rw [vM₅]; omega, by omega, by omega, by omega,
      ⟨fun i hi => by rw [S₅.wr, ← h.wr]; exact h.oP.wr i hi, h.oP.sep⟩,
      ⟨fun i hi => by rw [S₅.wr, ← h.wr]; exact h.oQ.wr i hi, h.oQ.sep⟩, h.a⟩)
      fun t ⟨res, cnt, hres, bP, bQ, hax, hsv, hfr, hsp⟩ => ?_
    refine ⟨res.map (VG.Proof.Rsa.X86_64.pqOf I.N), by rw [hgo, hres], ?_, ?_, by rw [hax]; cases res <;> rfl, hsv, hfr,
      hsp.trans h.rsp.symm⟩
    · rw [bP]; cases res <;> rfl
    · rw [bQ]; cases res <;> rfl

end VG.Proof.Rsa.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rsa.X86_64.RpCT1`. -/
section

/-!
# `vg_rsa_recover_primes` on x86-64: constant time, the prefix

`RpP`: the public data of `vg_rsa_recover_primes` (the working space, the
pointers and lengths, `n` and `e`, and the number of candidates tried).
`GA p`: what holds between the pieces of `main` (`RpS`), for the public
data `p`. The head, the loads, `-n⁻¹`, `M = d e` and the check of `M` leak
the same in two runs from `GM p` (`prefix_ct`), and leave the check's
result, which the public number of tries fixes (`prefixP_ct`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN)

/-- The public data of `vg_rsa_recover_primes`. -/
structure RpP where
  B : Addr
  Z : Nat
  k : Nat
  el : Nat
  dl : Nat
  pP : Addr
  pQ : Addr
  pN : Addr
  pE : Addr
  pD : Addr
  nb : List Byte
  eb : List Byte
  W : List Region
  sp : Addr
  cnt : Nat
  deriving Inhabited

/-- The public part of the inputs. -/
def RpIn.pub (I : VG.Proof.Rsa.X86_64.RpIn) : VG.Proof.Rsa.X86_64.RpP :=
  ⟨I.B, I.Z, I.k, I.el, I.dl, I.pP, I.pQ, I.pN, I.pE, I.pD, I.nb, I.eb, I.W, I.sp,
    (Spec.Rsa.primesKey I.nb I.eb I.db).2⟩

/-- The outputs: writable, outside the working space, and apart. -/
structure RpOuts (I : VG.Proof.Rsa.X86_64.RpIn) : Prop where
  p : ∀ i < I.k, InRegions I.W (I.pP + BitVec.ofNat 64 i) 1
  q : ∀ i < I.k, InRegions I.W (I.pQ + BitVec.ofNat 64 i) 1
  sp : ∀ i < I.k, I.Z ≤ VG.Proof.Bignum.X86_64.ofs I.B (I.pP + BitVec.ofNat 64 i)
  sq : ∀ i < I.k, I.Z ≤ VG.Proof.Bignum.X86_64.ofs I.B (I.pQ + BitVec.ofNat 64 i)
  a : VG.Proof.Rsa.X86_64.Apart I.pP I.k I.pQ I.k

theorem RpPre.outs {I : VG.Proof.Rsa.X86_64.RpIn} {s : State} (h : VG.Proof.Rsa.X86_64.RpPre I s) : VG.Proof.Rsa.X86_64.RpOuts I :=
  ⟨fun i hi => by rw [← h.wr]; exact h.oP.wr i hi, fun i hi => by rw [← h.wr]; exact h.oQ.wr i hi,
    h.oP.sep, h.oQ.sep, h.a⟩


/-- `ws`, a block checked from `rdi`, `r12` and `r9` that leaves the
registers `rs₂` with values of the public data, and code checked from
`rs₂`. -/
theorem ws_pin_ct {α : Type} {Φ Ψ : α → State → Prop} (B : α → Addr) (Z w : α → Nat) {rest : List Instr}
    {c₂ : Prog isa} (hws : ∀ a s, Φ a s → Ws s (B a) (Z a) (w a)) {hc₁ : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.block rest) hc₁).isSome = true)
    (rs₂ : List Reg) (f : α → Reg → BitVec 64)
    (hp : ∀ a s, Φ a s → WP isa (.block (VG.Impl.Rsa.X86_64.Keys.ws ++ rest)) s fun t => ∀ r ∈ rs₂, t.gpr r = f a r)
    {hc₂ : VG.Taint.Hint VG.X86_64.Taint.T} (ht₂ : (taint.check (Taint.ofRegs rs₂) c₂ hc₂).isSome = true)
    (hw : ∀ a s, Φ a s → WP isa (.seq (.block (VG.Impl.Rsa.X86_64.Keys.ws ++ rest)) c₂) s (Ψ a)) :
    RelCT isa (Two Φ) (.seq (.block (VG.Impl.Rsa.X86_64.Keys.ws ++ rest)) c₂) (Two Ψ) := by
  refine RelCT.block_seq (RelCT.seq (two_piece (Ψ := fun a t => (∀ r ∈ [.rdi, .r12, .r9], t.gpr r = wsVal (B a) (w a) r) ∧
      WP isa (.block rest) t (fun u => ∀ r ∈ rs₂, u.gpr r = f a r) ∧ WP isa (.seq (.block rest) c₂) t (Ψ a))
      [.rdi] (fun a s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [(hws a s₁ h₁).rdi, (hws a s₂ h₂).rdi])
      (by taint_decide) fun a s h => ?_)
    (pin_ct [.rdi, .r12, .r9] rs₂ f (fun a s₁ s₂ h₁ h₂ r hr => (h₁.1 r hr).trans (h₂.1 r hr).symm) ht₁
      (fun a t h => h.2.1) ht₂ fun a t h => h.2.2))
  have e₁ := WP.block_append_iff.mp (hp a s h)
  have e₂ := WP.block_seq_iff.mp (hw a s h)
  refine WP.mono (WP.and (WP.and (hws a s h).ws_ok e₁) (WP.seq_iff.mp e₂)) fun t ⟨⟨⟨h12, h9, _, k⟩, w₁⟩, w₂⟩ =>
    ⟨fun r hr => ?_, w₁, w₂⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (k.gpr (by decide)).trans (hws a s h).rdi
  · exact h12
  · exact h9

namespace Rp

/-- On entry to `main`. -/
def GM (p : VG.Proof.Rsa.X86_64.RpP) (s : State) : Prop :=
  ∃ I : VG.Proof.Rsa.X86_64.RpIn, I.pub = p ∧ VG.Proof.Rsa.X86_64.RpPre I s ∧ Spec.Rsa.modulusValid I.N I.k = true

/-- Between the pieces of `main`. -/
def GA (p : VG.Proof.Rsa.X86_64.RpP) (s : State) : Prop :=
  ∃ (I : VG.Proof.Rsa.X86_64.RpIn) (m₀ : Mem), I.pub = p ∧ VG.Proof.Rsa.X86_64.RpS I m₀ s ∧ VG.Proof.Rsa.X86_64.RpLens I ∧ VG.Proof.Rsa.X86_64.RpOuts I ∧
    Spec.Rsa.modulusValid I.N I.k = true

theorem GA.ws {p : VG.Proof.Rsa.X86_64.RpP} {s : State} (h : VG.Proof.Rsa.X86_64.Rp.GA p s) : Ws s p.B p.Z (wk p.k) := by
  obtain ⟨I, m₀, rfl, h, -⟩ := h
  exact h.ws

theorem pins_GA : Pins VG.Proof.Rsa.X86_64.Rp.GA [.rdi] := fun _ _ _ h₁ h₂ r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [h₁.ws.rdi, h₂.ws.rdi]

theorem pins_GM : Pins VG.Proof.Rsa.X86_64.Rp.GM [.rdi] := fun _ _ _ ⟨_, e₁, h₁, _⟩ ⟨_, e₂, h₂, _⟩ r hr => by
  simp only [List.mem_singleton] at hr; subst hr
  rw [h₁.rdi, h₂.rdi]
  exact (congrArg RpP.B e₁).trans (congrArg RpP.B e₂).symm

/-- `GA` after a piece that changes only arrays and slots of `rSlot`. -/
theorem GA.step {p : VG.Proof.Rsa.X86_64.RpP} {s t : State} (h : VG.Proof.Rsa.X86_64.Rp.GA p s) {js hs : List Nat}
    (hf : Frm p.B (VG.Proof.Rsa.X86_64.rg (wk p.k) js hs) s.mem t.mem) (hjs : ∀ j ∈ js, j < 16) (hhs : ∀ i ∈ hs, rSlot i = true)
    {regs : List Reg} (k : VG.Proof.MlKem.X86_64.Keep regs s t) (hr : .rdi ∉ regs ∧ .rsp ∉ regs) : VG.Proof.Rsa.X86_64.Rp.GA p t := by
  obtain ⟨I, m₀, rfl, h, L, O, hv⟩ := h
  exact ⟨I, m₀, rfl, h.step hf hjs hhs k hr, L, O, hv⟩

/-- `GA` after a piece that changes no memory. -/
theorem GA.same {p : VG.Proof.Rsa.X86_64.RpP} {s t : State} (h : VG.Proof.Rsa.X86_64.Rp.GA p s) (hm : t.mem = s.mem) {regs : List Reg} (k : VG.Proof.MlKem.X86_64.Keep regs s t)
    (hr : .rdi ∉ regs ∧ .rsp ∉ regs) : VG.Proof.Rsa.X86_64.Rp.GA p t :=
  h.step (js := []) (hs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) (by simp) k hr

/-- `GA` after a piece that changes only array `j`'s first `n` bytes. -/
theorem GA.arr {p : VG.Proof.Rsa.X86_64.RpP} {s t : State} (h : VG.Proof.Rsa.X86_64.Rp.GA p s) {j n : Nat} (hj : j < 16) (hn : n ≤ 8 * (wk p.k + 2))
    (o : VG.Proof.Bignum.X86_64.Outside p.B (VG.Proof.Bignum.X86_64.slot (wk p.k) j) n s.mem t.mem) {regs : List Reg} (k : VG.Proof.MlKem.X86_64.Keep regs s t)
    (hr : .rdi ∉ regs ∧ .rsp ∉ regs) : VG.Proof.Rsa.X86_64.Rp.GA p t :=
  h.step (Frm.rg_of_out o hn [j] [] (List.mem_singleton_self _)) (by simp [hj]) (by simp) k hr

/-! ## The head and the loads -/

theorem head_ct : RelCT isa (Two VG.Proof.Rsa.X86_64.Rp.GM) (.block CrtValues.head) (Two VG.Proof.Rsa.X86_64.Rp.GA) :=
  two_piece [.rdi] VG.Proof.Rsa.X86_64.Rp.pins_GM (by taint_decide) fun _ s ⟨I, e, h, hv⟩ =>
    WP.mono (VG.Proof.Rsa.X86_64.rpHeadS_ok h) fun _ ht => ⟨I, s.mem, e, ht, h.L, h.outs, hv⟩

theorem zeroA_ct {j : Nat} (hj : j < 16) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base j .r8)) zeroAccLoop) hc).isSome = true) :
    RelCT isa (Two VG.Proof.Rsa.X86_64.Rp.GA) (zeroA j) (Two VG.Proof.Rsa.X86_64.Rp.GA) :=
  ws_ct RpP.B RpP.Z (fun p => wk p.k) (fun _ _ h => h.ws) ht fun _ _ h =>
    WP.mono (zeroA_ok h.ws hj) fun _ ⟨_, o, k⟩ => h.arr hj (Nat.le_refl _) o k (by decide)

/-- `loadA`'s block and `loadBE`, from a `GA` with the pointer and the
length in the header slots `sPtr` and `sLen`. -/
theorem loadTail_ct {j sPtr sLen : Nat} (hj : j < 16) (hP : sPtr < 32) (hL : sLen < 32) (ptr : VG.Proof.Rsa.X86_64.RpP → Addr)
    (len : VG.Proof.Rsa.X86_64.RpP → Nat)
    (hA : ∀ p s, VG.Proof.Rsa.X86_64.Rp.GA p s → Bignum.X86_64.word s.mem p.B (8 * sPtr) = ptr p ∧
      Bignum.X86_64.word s.mem p.B (8 * sLen) = BitVec.ofNat 64 (len p) ∧
      (∃ bs, Src s p.B p.Z (ptr p) bs ∧ bs.length = len p) ∧ 1 ≤ len p ∧ len p ≤ 8 * wk p.k)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi]) (.block (VG.Impl.Rsa.X86_64.Keys.ws ++ base j .rbx ++ ([.mov .rsi (.mem (hdr sPtr)),
      .mov .rcx (.mem (hdr sLen))] : List Instr))) hc).isSome = true) :
    RelCT isa (Two VG.Proof.Rsa.X86_64.Rp.GA) (.seq (.block (VG.Impl.Rsa.X86_64.Keys.ws ++ base j .rbx ++ ([.mov .rsi (.mem (hdr sPtr)),
      .mov .rcx (.mem (hdr sLen))] : List Instr))) loadBE) (Two VG.Proof.Rsa.X86_64.Rp.GA) :=
  pin_ct [.rdi] [.rdi, .rbx, .rsi, .rcx] (fun p => ioVal p.B (VG.Proof.Bignum.X86_64.off p.B (VG.Proof.Bignum.X86_64.slot (wk p.k) j)) (ptr p) (len p)) VG.Proof.Rsa.X86_64.Rp.pins_GA ht
    (fun p s h => by
      obtain ⟨hp, hl, -⟩ := hA p s h
      exact WP.mono (loadBlk_ok h.ws hP hL hp hl) fun t ⟨hbx, hsi, hcx, hdi, _⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hdi
        · exact hbx
        · exact hsi
        · exact hcx)
    (by taint_decide) fun p s h => by
      obtain ⟨hp, hl, ⟨bs, hsrc, hbl⟩, hl1, hlw⟩ := hA p s h
      have hw := h.ws
      have hn := hw.scr.nowrap
      have sj := hw.sl hj
      have hw2 := hw.w2
      refine WP.seq (WP.mono (loadBlk_ok hw hP hL hp hl) fun t ⟨hbx, hsi, hcx, _, hm, k⟩ => ?_)
      have ht := h.same hm k (by decide)
      have hsrc' := hsrc.congrK (fun x _ => by rw [hm]) k
      exact WP.mono (loadBE_ok (w := (len p + 7) / 8) ht.ws.scr hsi hcx hbx hbl hl1 (by omega) rfl (by omega)
        (fun i hi => hsrc'.rd i (by omega)) (fun i hi => hsrc'.val i (by omega))
        (fun i hi => Or.inr (by have := hsrc'.out i (by omega); omega))) fun t' ⟨_, o, k'⟩ =>
          ht.arr hj (by omega) o k' (by decide)

theorem loadA_ct {j sPtr sLen : Nat} (hj : j < 16) (hP : sPtr < 32) (hL : sLen < 32) (ptr : VG.Proof.Rsa.X86_64.RpP → Addr)
    (len : VG.Proof.Rsa.X86_64.RpP → Nat)
    (hA : ∀ p s, VG.Proof.Rsa.X86_64.Rp.GA p s → Bignum.X86_64.word s.mem p.B (8 * sPtr) = ptr p ∧
      Bignum.X86_64.word s.mem p.B (8 * sLen) = BitVec.ofNat 64 (len p) ∧
      (∃ bs, Src s p.B p.Z (ptr p) bs ∧ bs.length = len p) ∧ 1 ≤ len p ∧ len p ≤ 8 * wk p.k)
    {hc₁ : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base j .r8)) zeroAccLoop) hc₁).isSome = true)
    {hc₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht₂ : (taint.check (Taint.ofRegs [.rdi]) (.block (VG.Impl.Rsa.X86_64.Keys.ws ++ base j .rbx ++ ([.mov .rsi (.mem (hdr sPtr)),
      .mov .rcx (.mem (hdr sLen))] : List Instr))) hc₂).isSome = true) :
    RelCT isa (Two VG.Proof.Rsa.X86_64.Rp.GA) (seqs (loadA j sPtr sLen)) (Two VG.Proof.Rsa.X86_64.Rp.GA) :=
  RelCT.seq (VG.Proof.Rsa.X86_64.Rp.zeroA_ct hj ht₁) (VG.Proof.Rsa.X86_64.Rp.loadTail_ct hj hP hL ptr len hA ht₂)

/-- The three loads. -/
theorem loads_ct : RelCT isa (Two VG.Proof.Rsa.X86_64.Rp.GA) (seqs (loadA aN Impl.Bignum.X86_64.Public.sN Impl.Bignum.X86_64.Public.sK ++
    (loadA aE Impl.Bignum.X86_64.Public.sE Impl.Bignum.X86_64.Public.sElen ++ loadA aD sD sDl))) (Two VG.Proof.Rsa.X86_64.Rp.GA) := by
  have k8 : ∀ {k : Nat}, k ≤ 8 * wk k := fun {k} => by unfold wk; omega
  refine ct_app (by simp [loadA]) (by simp [loadA]) (VG.Proof.Rsa.X86_64.Rp.loadA_ct (by decide) (by decide) (by decide) RpP.pN RpP.k
    (fun p s h => ?_) (by taint_decide) (by taint_decide)) (ct_app (by simp [loadA]) (by simp [loadA])
    (VG.Proof.Rsa.X86_64.Rp.loadA_ct (by decide) (by decide) (by decide) RpP.pE RpP.el (fun p s h => ?_) (by taint_decide) (by taint_decide))
    (VG.Proof.Rsa.X86_64.Rp.loadA_ct (by decide) (by decide) (by decide) RpP.pD RpP.dl (fun p s h => ?_) (by taint_decide)
      (by taint_decide)))
  all_goals
    obtain ⟨I, m₀, rfl, h, L, -⟩ := h
    dsimp only [RpIn.pub]
    have := L.k1
  · exact ⟨h.args.n, h.args.k, ⟨_, h.n, L.nbl⟩, by omega, k8⟩
  · exact ⟨h.args.e, h.args.el, ⟨_, h.e, L.ebl⟩, L.el1, by have := L.el2; have := @k8 I.k; omega⟩
  · exact ⟨h.args.d, h.args.dl, ⟨_, h.d, L.dbl⟩, L.dl1, by have := L.dl2; have := @k8 I.k; omega⟩

/-! ## Values between the pieces -/

/-- `GA` with facts `F` about the memory. -/
def GV (F : VG.Proof.Rsa.X86_64.RpIn → Mem → Prop) (p : VG.Proof.Rsa.X86_64.RpP) (s : State) : Prop :=
  ∃ (I : VG.Proof.Rsa.X86_64.RpIn) (m₀ : Mem), I.pub = p ∧ VG.Proof.Rsa.X86_64.RpS I m₀ s ∧ VG.Proof.Rsa.X86_64.RpLens I ∧ VG.Proof.Rsa.X86_64.RpOuts I ∧
    Spec.Rsa.modulusValid I.N I.k = true ∧ F I s.mem

theorem GV.ga {F : VG.Proof.Rsa.X86_64.RpIn → Mem → Prop} {p : VG.Proof.Rsa.X86_64.RpP} {s : State} (h : VG.Proof.Rsa.X86_64.Rp.GV F p s) : VG.Proof.Rsa.X86_64.Rp.GA p s := by
  obtain ⟨I, m₀, e, h, L, O, hv, -⟩ := h
  exact ⟨I, m₀, e, h, L, O, hv⟩

theorem GV.ws {F : VG.Proof.Rsa.X86_64.RpIn → Mem → Prop} {p : VG.Proof.Rsa.X86_64.RpP} {s : State} (h : VG.Proof.Rsa.X86_64.Rp.GV F p s) : Ws s p.B p.Z (wk p.k) := h.ga.ws

theorem pins_GV {F : VG.Proof.Rsa.X86_64.RpIn → Mem → Prop} : Pins (VG.Proof.Rsa.X86_64.Rp.GV F) [.rdi] := fun _ _ _ h₁ h₂ r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [h₁.ws.rdi, h₂.ws.rdi]

/-- `GV` after a piece, with the facts carried over. -/
theorem GV.step {F G : VG.Proof.Rsa.X86_64.RpIn → Mem → Prop} {p : VG.Proof.Rsa.X86_64.RpP} {s t : State} (h : VG.Proof.Rsa.X86_64.Rp.GV F p s) {js hs : List Nat}
    (hf : Frm p.B (VG.Proof.Rsa.X86_64.rg (wk p.k) js hs) s.mem t.mem) (hjs : ∀ j ∈ js, j < 16) (hhs : ∀ i ∈ hs, rSlot i = true)
    {regs : List Reg} (k : VG.Proof.MlKem.X86_64.Keep regs s t) (hr : .rdi ∉ regs ∧ .rsp ∉ regs)
    (hFG : ∀ I : VG.Proof.Rsa.X86_64.RpIn, I.pub = p → VG.Proof.Rsa.X86_64.RpS I s.mem s → VG.Proof.Rsa.X86_64.RpS I s.mem t → F I s.mem → G I t.mem) : VG.Proof.Rsa.X86_64.Rp.GV G p t := by
  obtain ⟨I, m₀, rfl, h, L, O, hv, hF⟩ := h
  have h' := h.step hf hjs hhs k hr
  have hS : VG.Proof.Rsa.X86_64.RpS I s.mem s := { h with
                                      inScr := InScr.refl _ _ _ }
  exact ⟨I, m₀, rfl, h', L, O, hv, hFG I rfl hS (hS.step hf hjs hhs k hr) hF⟩

/-- The values of `n`, `e` and `d` in their arrays. -/
def FL (I : VG.Proof.Rsa.X86_64.RpIn) (m : Mem) : Prop :=
  wv m I.B (VG.Proof.Bignum.X86_64.slot (wk I.k) aN) (wk I.k) = I.N ∧ wv m I.B (VG.Proof.Bignum.X86_64.slot (wk I.k) aE) (wk I.k) = I.E ∧
    wv m I.B (VG.Proof.Bignum.X86_64.slot (wk I.k) aD) (wk I.k) = I.D

/-- And `-n⁻¹`. -/
def FM (I : VG.Proof.Rsa.X86_64.RpIn) (m : Mem) : Prop :=
  VG.Proof.Rsa.X86_64.Rp.FL I m ∧ ((VG.Proof.Bignum.X86_64.word m I.B (VG.Proof.Bignum.X86_64.slot (wk I.k) aN)).toNat * (VG.Proof.Bignum.X86_64.word m I.B (8 * sMinv)).toNat + 1) % 2 ^ 64 = 0

theorem loadsV_ct : RelCT isa (Two VG.Proof.Rsa.X86_64.Rp.GA) (seqs (loadA aN Impl.Bignum.X86_64.Public.sN Impl.Bignum.X86_64.Public.sK ++
    (loadA aE Impl.Bignum.X86_64.Public.sE Impl.Bignum.X86_64.Public.sElen ++ loadA aD sD sDl))) (Two (VG.Proof.Rsa.X86_64.Rp.GV VG.Proof.Rsa.X86_64.Rp.FL)) :=
  two_post (loads_ct.mono (fun _ _ h => h) fun _ _ _ => trivial) fun p s h => by
    obtain ⟨I, m₀, rfl, h, L, O, hv⟩ := h
    exact WP.mono (VG.Proof.Rsa.X86_64.rpLoads_ok h L) fun t ⟨ht, _, vN, vE, vD, _⟩ => ⟨I, m₀, rfl, ht, L, O, hv, vN, vE, vD⟩

theorem minv_ct : RelCT isa (Two (VG.Proof.Rsa.X86_64.Rp.GV VG.Proof.Rsa.X86_64.Rp.FL)) (.block minvBlk) (Two (VG.Proof.Rsa.X86_64.Rp.GV VG.Proof.Rsa.X86_64.Rp.FM)) := by
  have e : minvBlk = VG.Impl.Rsa.X86_64.Keys.ws ++ (base aN .r10 ++ ([.mov .rbx (.mem (at0 .r10))] : List Instr) ++ minv ++
      ([.store (hdr sMinv) .r15] : List Instr)) := by simp only [minvBlk, List.append_assoc]
  rw [e]
  refine ws_block_ct (rest := base aN .r10 ++ ([.mov .rbx (.mem (at0 .r10))] : List Instr) ++ minv ++
      ([.store (hdr sMinv) .r15] : List Instr)) RpP.B RpP.Z (fun p => wk p.k) (fun _ _ h => h.ws)
    (by taint_decide) fun p s h => ?_
  rw [← e]
  obtain ⟨I, m₀, eI, h', L, O, hv, vN, vE, vD⟩ := id h
  subst eI
  have hw := h'.ws
  have hZ16 : VG.Proof.Bignum.X86_64.slot (wk I.k) 16 ≤ 2 ^ 64 := by have := hw.scr.nowrap; have := hw.hZ; omega
  have hodd := (valid_lo hv).1
  have hw0 : (VG.Proof.Bignum.X86_64.word s.mem I.B (VG.Proof.Bignum.X86_64.slot (wk I.k) aN)).toNat % 2 = 1 := by
    rw [show (VG.Proof.Bignum.X86_64.word s.mem I.B (VG.Proof.Bignum.X86_64.slot (wk I.k) aN)).toNat % 2 = wv s.mem I.B (VG.Proof.Bignum.X86_64.slot (wk I.k) aN) (wk I.k) % 2 by
      rw [VG.Proof.Rsa.X86_64.wv_low (by have := hw.w1; omega)]; omega, vN]; exact hodd
  refine WP.mono (VG.Proof.Rsa.X86_64.minvBlk_ok hw hw0) fun t ⟨hi, f, k⟩ => ⟨I, m₀, rfl, h'.step f (by simp) (by decide) k (by decide),
    L, O, hv, ⟨?_, ?_, ?_⟩, hi⟩
  · rw [f.rg_wv hZ16 (by decide) (by decide) (by simp) (by omega)]; exact vN
  · rw [f.rg_wv hZ16 (by decide) (by decide) (by simp) (by omega)]; exact vE
  · rw [f.rg_wv hZ16 (by decide) (by decide) (by simp) (by omega)]; exact vD

/-! ## `M = d e` and its check -/

def FZ1 (I : VG.Proof.Rsa.X86_64.RpIn) (m : Mem) : Prop := VG.Proof.Rsa.X86_64.Rp.FM I m ∧ wv m I.B (VG.Proof.Bignum.X86_64.slot (wk I.k) aM) (wk I.k + 2) = 0
def FZ2 (I : VG.Proof.Rsa.X86_64.RpIn) (m : Mem) : Prop := VG.Proof.Rsa.X86_64.Rp.FM I m ∧ wv m I.B (VG.Proof.Bignum.X86_64.slot (wk I.k) aM) (2 * (wk I.k + 2)) = 0
def FP (I : VG.Proof.Rsa.X86_64.RpIn) (m : Mem) : Prop := VG.Proof.Rsa.X86_64.Rp.FM I m ∧ wv m I.B (VG.Proof.Bignum.X86_64.slot (wk I.k) aM) (2 * (wk I.k + 2)) = I.D * I.E

theorem zeroAV_ct {F : VG.Proof.Rsa.X86_64.RpIn → Mem → Prop} {j : Nat} (hj : j < 16) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base j .r8)) zeroAccLoop) hc).isSome = true) :
    RelCT isa (Two (VG.Proof.Rsa.X86_64.Rp.GV F)) (zeroA j) fun _ _ => True :=
  (VG.Proof.Rsa.X86_64.Rp.zeroA_ct hj ht).mono (fun _ _ h => two_mono (Φ := VG.Proof.Rsa.X86_64.Rp.GV F) (fun _ _ h => GV.ga h) h) fun _ _ _ => trivial

theorem zeroM_ct : RelCT isa (Two (VG.Proof.Rsa.X86_64.Rp.GV VG.Proof.Rsa.X86_64.Rp.FM)) (zeroA aM) (Two (VG.Proof.Rsa.X86_64.Rp.GV VG.Proof.Rsa.X86_64.Rp.FZ1)) :=
  two_post (VG.Proof.Rsa.X86_64.Rp.zeroAV_ct (by decide) (by taint_decide)) fun p s h => by
    obtain ⟨I, m₀, rfl, h', L, O, hv, ⟨vN, vE, vD⟩, hi⟩ := id h
    have hw := h'.ws
    have hZ16 : VG.Proof.Bignum.X86_64.slot (wk I.k) 16 ≤ 2 ^ 64 := by have := hw.scr.nowrap; have := hw.hZ; omega
    refine WP.mono (zeroA_ok hw (j := aM) (by decide)) fun t ⟨z, o, k⟩ => ?_
    have f : Frm I.B (VG.Proof.Rsa.X86_64.rg (wk I.k) [aM] []) s.mem t.mem := Frm.rg_of_out o (Nat.le_refl _) _ _ (by decide)
    refine ⟨I, m₀, rfl, h'.step f (by decide) (by simp) k (by decide), L, O, hv, ⟨⟨?_, ?_, ?_⟩, ?_⟩, z⟩
    · rw [f.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega)]; exact vN
    · rw [f.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega)]; exact vE
    · rw [f.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega)]; exact vD
    · rw [f.rg_word0 hZ16 (by simp) (by decide) (by decide), f.rg_word (by decide) (by simp)]; exact hi

theorem zeroM1_ct : RelCT isa (Two (VG.Proof.Rsa.X86_64.Rp.GV VG.Proof.Rsa.X86_64.Rp.FZ1)) (zeroA (aM + 1)) (Two (VG.Proof.Rsa.X86_64.Rp.GV VG.Proof.Rsa.X86_64.Rp.FZ2)) :=
  two_post (VG.Proof.Rsa.X86_64.Rp.zeroAV_ct (by decide) (by taint_decide)) fun p s h => by
    obtain ⟨I, m₀, rfl, h', L, O, hv, ⟨⟨vN, vE, vD⟩, hi⟩, z₁⟩ := id h
    have hw := h'.ws
    have hZ16 : VG.Proof.Bignum.X86_64.slot (wk I.k) 16 ≤ 2 ^ 64 := by have := hw.scr.nowrap; have := hw.hZ; omega
    refine WP.mono (zeroA_ok hw (j := aM + 1) (by decide)) fun t ⟨z, o, k⟩ => ?_
    have f : Frm I.B (VG.Proof.Rsa.X86_64.rg (wk I.k) [aM + 1] []) s.mem t.mem := Frm.rg_of_out o (Nat.le_refl _) _ _ (by decide)
    have eM1 : VG.Proof.Bignum.X86_64.slot (wk I.k) (aM + 1) = VG.Proof.Bignum.X86_64.slot (wk I.k) aM + 8 * (wk I.k + 2) := by simp only [VG.Proof.Bignum.X86_64.slot, hdrBytes, aM]; omega
    refine ⟨I, m₀, rfl, h'.step f (by decide) (by simp) k (by decide), L, O, hv, ⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩
    · rw [f.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega)]; exact vN
    · rw [f.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega)]; exact vE
    · rw [f.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega)]; exact vD
    · rw [f.rg_word0 hZ16 (by simp) (by decide) (by decide), f.rg_word (by decide) (by simp)]; exact hi
    · rw [show 2 * (wk I.k + 2) = (wk I.k + 2) + (wk I.k + 2) by omega, wv_add, ← eM1, z,
        f.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega), z₁, Nat.mul_zero]

/-- The registers `prod`'s loop needs pinned. -/
def prodVal (p : VG.Proof.Rsa.X86_64.RpP) : Reg → BitVec 64
  | .rdi => p.B
  | .r12 => BitVec.ofNat 64 (wk p.k)
  | .rbx => VG.Proof.Bignum.X86_64.off p.B (VG.Proof.Bignum.X86_64.slot (wk p.k) aE)
  | .r10 => VG.Proof.Bignum.X86_64.off p.B (VG.Proof.Bignum.X86_64.slot (wk p.k) aM)
  | .r15 => VG.Proof.Bignum.X86_64.off p.B (VG.Proof.Bignum.X86_64.slot (wk p.k) aD)
  | .r11 => BitVec.ofNat 64 ((p.el + 7) / 8)
  | .r13 => BitVec.ofNat 64 0
  | _ => 0

theorem prodLoop_ct : RelCT isa (Two (VG.Proof.Rsa.X86_64.Rp.GV VG.Proof.Rsa.X86_64.Rp.FZ2))
    (.seq (.block prodInit) (.loop (.seq (.block rowHead) (.seq mulAddRow (.block rowNext))) .ne)) (Two (VG.Proof.Rsa.X86_64.Rp.GV VG.Proof.Rsa.X86_64.Rp.FP)) :=
  pin_ct [.rdi] [.rdi, .r12, .rbx, .r10, .r15, .r11, .r13] VG.Proof.Rsa.X86_64.Rp.prodVal VG.Proof.Rsa.X86_64.Rp.pins_GV (by taint_decide)
    (fun p s h => by
      obtain ⟨I, m₀, rfl, h', L, O, hv, -⟩ := id h
      exact WP.mono (prodInit_ok h'.ws h'.args.el (by have := L.el2; have := L.k2; omega))
        fun t ⟨h12, hbx, h10, h15, h11, h13, hdi, _⟩ r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact hdi
          · exact h12
          · exact hbx
          · exact h10
          · exact h15
          · exact h11
          · exact h13)
    (by taint_decide) fun p s h => by
      obtain ⟨I, m₀, rfl, h', L, O, hv, ⟨⟨vN, vE, vD⟩, hi⟩, hz⟩ := id h
      have hw := h'.ws
      have hZ16 : VG.Proof.Bignum.X86_64.slot (wk I.k) 16 ≤ 2 ^ 64 := by have := hw.scr.nowrap; have := hw.hZ; omega
      have hEl : I.E < 2 ^ (64 * ((I.el + 7) / 8)) := by
        have := os2ip_lt I.eb; rw [L.ebl] at this; exact Nat.lt_of_lt_of_le this (pow256_le_wk I.el)
      have sM := hw.sl (j := aM + 1) (by decide)
      refine WP.mono (prodLoop_ok hw h'.args.el L.el1 (by have := L.el2; unfold wk; omega)
        (by rw [vE]; exact hEl) hz) fun t ⟨vM, o, k⟩ => ?_
      have f : Frm I.B (VG.Proof.Rsa.X86_64.rg (wk I.k) [aM, aM + 1] []) s.mem t.mem :=
        Frm.rg_of_out2 o (Nat.le_refl _) _ _ (by decide) (by decide)
      refine ⟨I, m₀, rfl, h'.step f (by decide) (by simp) k (by decide), L, O, hv, ⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩⟩
      · rw [f.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega)]; exact vN
      · rw [f.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega)]; exact vE
      · rw [f.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega)]; exact vD
      · rw [f.rg_word0 hZ16 (by simp) (by decide) (by decide), f.rg_word (by decide) (by simp)]; exact hi
      · rw [vM, vD, vE]

theorem prod_ct : RelCT isa (Two (VG.Proof.Rsa.X86_64.Rp.GV VG.Proof.Rsa.X86_64.Rp.FM)) (seqs prod) (Two (VG.Proof.Rsa.X86_64.Rp.GV VG.Proof.Rsa.X86_64.Rp.FP)) := by
  simp only [prod, seqs]
  exact RelCT.seq VG.Proof.Rsa.X86_64.Rp.zeroM_ct (RelCT.seq VG.Proof.Rsa.X86_64.Rp.zeroM1_ct VG.Proof.Rsa.X86_64.Rp.prodLoop_ct)

/-- The registers the check of `M` needs pinned. -/
def skipVal (p : VG.Proof.Rsa.X86_64.RpP) : Reg → BitVec 64
  | .rdi => p.B
  | .rbx => VG.Proof.Bignum.X86_64.off p.B (VG.Proof.Bignum.X86_64.slot (wk p.k) aM)
  | .r12 => BitVec.ofNat 64 (wk p.k + (p.el + 7) / 8)
  | _ => 0

theorem skipBlk_eq : skipBlk = VG.Impl.Rsa.X86_64.Keys.ws ++ (base aM .rbx ++
    ([.mov .rax (.mem (at0 .rbx)), .mov .rdx (.reg .rax), .alu .and .rdx (.imm 1), .alu .sub .rax (.reg .rdx),
      .mov .rcx (.mem (hdr Impl.Bignum.X86_64.Public.sElen)), .alu .add .rcx (.imm 7), .shift .shr .rcx 3,
      .alu .add .rcx (.mem (hdr sW)), .mov .r12 (.reg .rcx), .store (at0 .rbx) .rax, .alu .sub .rdx (.imm 1),
      .store (hdr sC2) .rdx, .mov32 .rbp (.imm 0)] : List Instr)) := by
  simp only [skipBlk, List.append_assoc]

theorem skip_ct : RelCT isa (Two (VG.Proof.Rsa.X86_64.Rp.GV VG.Proof.Rsa.X86_64.Rp.FP)) (seqs [.block skipBlk, wordLoop 0 orBody, .block skipTest])
    fun _ _ => True := by
  simp only [seqs]
  rw [VG.Proof.Rsa.X86_64.Rp.skipBlk_eq]
  refine (VG.Proof.Rsa.X86_64.ws_pin_ct (Ψ := fun _ _ => True) RpP.B RpP.Z (fun p => wk p.k) (fun _ _ h => h.ws) (by taint_decide)
    [.rdi, .rbx, .r12, .rbp] VG.Proof.Rsa.X86_64.Rp.skipVal (fun p s h => ?_) (by taint_decide) fun p s h => ?_).mono
    (fun _ _ h => h) fun _ _ _ => trivial
  · rw [← VG.Proof.Rsa.X86_64.Rp.skipBlk_eq]
    obtain ⟨I, m₀, rfl, h', L, O, -⟩ := id h
    exact WP.mono (skipBlk_ok h'.ws h'.args.el (by have := L.el2; have := L.k2; omega))
      fun t ⟨hbx, hbp, h12, hdi, _⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hdi
        · exact hbx
        · exact h12
        · exact hbp
  · rw [← VG.Proof.Rsa.X86_64.Rp.skipBlk_eq]
    obtain ⟨I, m₀, rfl, h', L, O, hv, ⟨⟨vN, vE, vD⟩, hi⟩, vM⟩ := id h
    have hEl : I.E < 2 ^ (64 * ((I.el + 7) / 8)) := by
      have := os2ip_lt I.eb; rw [L.ebl] at this; exact Nat.lt_of_lt_of_le this (pow256_le_wk I.el)
    have hDl : I.D < 2 ^ (64 * wk I.k) := by
      have := os2ip_lt I.db; rw [L.dbl] at this
      exact Nat.lt_of_lt_of_le this (by
        rw [pow256_eq]; exact Nat.pow_le_pow_right (by decide) (by have := L.dl2; unfold wk; omega))
    have := skip_ok h'.ws h'.args.el L.el1 (by have := L.el2; unfold wk; omega)
      (by rw [vM, Nat.mul_add, Nat.pow_add]; exact Nat.mul_lt_mul'' hDl hEl)
    simp only [seqs] at this
    exact WP.mono this fun _ _ => trivial

/-- The prefix of `main` leaks the same in two runs with the same public
data. -/
theorem prefix_ct : RelCT isa (Two VG.Proof.Rsa.X86_64.Rp.GM) (seqs VG.Proof.Rsa.X86_64.prefixList) (Two fun (_ : VG.Proof.Rsa.X86_64.RpP) (_ : State) => True) := by
  simp only [VG.Proof.Rsa.X86_64.prefixList]
  refine ct_app ?_ ?_ (ct_one VG.Proof.Rsa.X86_64.Rp.head_ct) (ct_app ?_ ?_ VG.Proof.Rsa.X86_64.Rp.loadsV_ct (ct_app ?_ ?_ (ct_one VG.Proof.Rsa.X86_64.Rp.minv_ct)
    (ct_app ?_ ?_ VG.Proof.Rsa.X86_64.Rp.prod_ct (skip_ct.mono (fun _ _ h => h) fun _ _ _ => ⟨default, trivial, trivial⟩))))
  all_goals simp [loadA, prod]

end Rp

end VG.Proof.Rsa.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rsa.X86_64.RpCT2`. -/
section

/-!
# `vg_rsa_recover_primes` on x86-64: constant time, the halvings

`64 Bw` halvings, a public count (`halving_ct`): the counter in `r13` and
its bound in `r11` are pinned by correctness, and so are the bases and `Bw`
after each halving's head.
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN)
open VG.Spec.Rsa (splitTwos)

namespace Rp

/-- On entry to `rest`. -/
def GR0 (p : VG.Proof.Rsa.X86_64.RpP) (s : State) : Prop :=
  ∃ (I : VG.Proof.Rsa.X86_64.RpIn) (m₀ : Mem), I.pub = p ∧ VG.Proof.Rsa.X86_64.RestPre I m₀ I.N (I.D * I.E - 1) s ∧ VG.Proof.Rsa.X86_64.RpOuts I ∧
    Spec.Rsa.modulusValid I.N I.k = true

/-- The halvings' count, `64 Bw`. -/
abbrev hN (p : VG.Proof.Rsa.X86_64.RpP) : Nat := 64 * (wk p.k + (p.el + 7) / 8)

/-- After `j` halvings, from `s₁`. -/
def HL (p : VG.Proof.Rsa.X86_64.RpP) (j : Nat) (s : State) : Prop :=
  ∃ (s₁ : State) (m : Nat), Bignum.X86_64.word s₁.mem p.B (8 * Impl.Bignum.X86_64.Public.sElen) =
    BitVec.ofNat 64 p.el ∧ 1 ≤ p.el ∧ p.el ≤ 8 * wk p.k ∧ m < 2 ^ (64 * (wk p.k + (p.el + 7) / 8)) ∧
    s₁.gpr .r11 = BitVec.ofNat 64 (VG.Proof.Rsa.X86_64.Rp.hN p) ∧ VG.Proof.Rsa.X86_64.HalfInv s₁ p.B p.Z (wk p.k) m j s

theorem halfHead_eq : halfHead = VG.Impl.Rsa.X86_64.Keys.ws ++ (base aM .r8 ++ base aH .rsi ++ bw ++
    ([.mov .r12 (.reg .rax), .mov .rax (.mem (at0 .r8)), .alu .and .rax (.imm 1), .mov32 .rbp (.imm 0),
      .alu .sub .rbp (.reg .rax)] : List Instr)) := by
  simp only [halfHead, List.append_assoc]

/-- The registers a halving needs pinned after its head. -/
def halfVal (q : VG.Proof.Rsa.X86_64.RpP × Nat) : Reg → BitVec 64
  | .rdi => q.1.B
  | .r8 => VG.Proof.Bignum.X86_64.off q.1.B (VG.Proof.Bignum.X86_64.slot (wk q.1.k) aM)
  | .rsi => VG.Proof.Bignum.X86_64.off q.1.B (VG.Proof.Bignum.X86_64.slot (wk q.1.k) aH)
  | .r12 => BitVec.ofNat 64 (wk q.1.k + (q.1.el + 7) / 8)
  | .r13 => BitVec.ofNat 64 q.2
  | .r11 => BitVec.ofNat 64 (VG.Proof.Rsa.X86_64.Rp.hN q.1)
  | _ => 0

theorem halfBody_ct : RelCT isa (Two fun (q : VG.Proof.Rsa.X86_64.RpP × Nat) s => q.2 < VG.Proof.Rsa.X86_64.Rp.hN q.1 ∧ VG.Proof.Rsa.X86_64.Rp.HL q.1 q.2 s)
    (seqs [.block halfHead, wordLoop 0 shrBody, wordLoop 0 VG.Impl.Rsa.X86_64.Keys.selBody, .block halfNext]) fun _ _ => True := by
  simp only [seqs]
  rw [VG.Proof.Rsa.X86_64.Rp.halfHead_eq]
  refine (VG.Proof.Rsa.X86_64.ws_pin_ct (Ψ := fun _ _ => True) (fun q : VG.Proof.Rsa.X86_64.RpP × Nat => q.1.B) (fun q => q.1.Z) (fun q => wk q.1.k)
    (fun q s h => by obtain ⟨-, s₁, m, -, -, -, -, -, hI⟩ := h; exact hI.ws) (by taint_decide)
    [.rdi, .r8, .rsi, .r12, .r13, .r11] VG.Proof.Rsa.X86_64.Rp.halfVal (fun q s h => ?_) (by taint_decide) fun q s h => ?_).mono
    (fun _ _ h => h) fun _ _ _ => trivial
  · rw [← VG.Proof.Rsa.X86_64.Rp.halfHead_eq]
    obtain ⟨-, s₁, m, hel, he1, he2, -, h11, hI⟩ := h
    have hel₀ : Bignum.X86_64.word s.mem q.1.B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 q.1.el := by
      have hT0 := hdr_lt_slot (wk q.1.k) aM (show Impl.Bignum.X86_64.Public.sElen < 32 by decide)
      have hT1 := hdr_lt_slot (wk q.1.k) aH (show Impl.Bignum.X86_64.Public.sElen < 32 by decide)
      have hZ := hI.ws.hZ
      rw [hI.frm.word_eq (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp only [Impl.Bignum.X86_64.Public.sElen, sFn, sT] at * <;> omega)
        (by simp only [Impl.Bignum.X86_64.Public.sElen, sFn]; omega)]
      exact hel
    exact WP.mono (VG.Proof.Rsa.X86_64.halfHead_ok hI.ws hel₀ (by have := hI.ws.w2; omega))
      fun t ⟨h8, hsi, h12, _, hdi, _, k⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        · exact hdi
        · exact h8
        · exact hsi
        · exact h12
        · exact (k.gpr (by decide)).trans hI.r13
        · exact (k.gpr (by decide)).trans ((hI.keep.gpr (by decide)).trans h11)
  · rw [← VG.Proof.Rsa.X86_64.Rp.halfHead_eq]
    obtain ⟨hj, s₁, m, hel, he1, he2, hm, h11, hI⟩ := h
    have := VG.Proof.Rsa.X86_64.halfStep_ok hI hel he1 he2 hm h11 hj
    simp only [seqs] at this
    exact WP.mono this fun _ _ => trivial

/-- After the halvings: `r` and `t`, and what Montgomery form needs. -/
def GR1 (p : VG.Proof.Rsa.X86_64.RpP) (s : State) : Prop :=
  ∃ (I : VG.Proof.Rsa.X86_64.RpIn) (m₀ : Mem), I.pub = p ∧ VG.Proof.Rsa.X86_64.RpS I m₀ s ∧ VG.Proof.Rsa.X86_64.RpLens I ∧ VG.Proof.Rsa.X86_64.RpOuts I ∧
    Spec.Rsa.modulusValid I.N I.k = true ∧ I.N % 2 = 1 ∧ 2 ^ (64 * (wk I.k - 1)) ≤ I.N ∧
    wv s.mem I.B (VG.Proof.Bignum.X86_64.slot (wk I.k) aN) (wk I.k) = I.N ∧
    ((VG.Proof.Bignum.X86_64.word s.mem I.B (VG.Proof.Bignum.X86_64.slot (wk I.k) aN)).toNat * (VG.Proof.Bignum.X86_64.word s.mem I.B (8 * sMinv)).toNat + 1) % 2 ^ 64 = 0 ∧
    wv s.mem I.B (VG.Proof.Bignum.X86_64.slot (wk I.k) aM) (2 * (wk I.k + 2)) = (splitTwos (I.D * I.E - 1)).2 ∧
    VG.Proof.Bignum.X86_64.word s.mem I.B (8 * sT) = BitVec.ofNat 64 (splitTwos (I.D * I.E - 1)).1 ∧
    0 < I.D * I.E - 1 ∧ (I.D * I.E - 1) % 2 = 0 ∧ I.D * I.E - 1 < 2 ^ (64 * (wk I.k + (I.el + 7) / 8))

theorem halfInit_ct : RelCT isa (Two VG.Proof.Rsa.X86_64.Rp.GR0) (.block halfInit) (Two fun p s => 0 < VG.Proof.Rsa.X86_64.Rp.hN p ∧ VG.Proof.Rsa.X86_64.Rp.HL p 0 s) :=
  two_piece [.rdi] (fun _ _ _ ⟨_, _, e₁, h₁, _⟩ ⟨_, _, e₂, h₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.S.ws.rdi, h₂.S.ws.rdi]
      exact (congrArg RpP.B e₁).trans (congrArg RpP.B e₂).symm)
    (by taint_decide) fun p s h => by
      obtain ⟨I, m₀, rfl, h, O, hv⟩ := h
      dsimp only [RpIn.pub]
      have hw := h.S.ws
      have hn := hw.scr.nowrap
      have h256 := hw.h256
      have hZ := hw.hZ
      have hT0 := hdr_lt_slot (wk I.k) aM (show sT < 32 by decide)
      have L := h.L
      refine WP.mono (VG.Proof.Rsa.X86_64.halfInit_ok hw h.S.args.el (by have := L.el2; have := L.k2; omega))
        fun t ⟨h11, h13, m₁, k₁⟩ => ⟨by show 0 < 64 * (wk I.k + (I.el + 7) / 8); unfold wk; have := L.k1; omega, t, I.D * I.E - 1, ?_, L.el1,
          by show I.el ≤ 8 * wk I.k; have := L.el2; unfold wk; omega, h.mlt, h11, ?_⟩
      · have o₁ := VG.Proof.Bignum.X86_64.writeW_outside s.mem I.B (0 : BitVec 64) (d := 8 * sT) (by simp only [sT, sFn]; omega)
        rw [← m₁] at o₁
        rw [o₁.word (Or.inl (by simp only [Impl.Bignum.X86_64.Public.sElen, sFn, sT]; omega))
          (by simp only [Impl.Bignum.X86_64.Public.sElen, sFn]; omega)]
        exact h.S.args.el
      · have o₁ := VG.Proof.Bignum.X86_64.writeW_outside s.mem I.B (0 : BitVec 64) (d := 8 * sT) (by simp only [sT, sFn]; omega)
        rw [← m₁] at o₁
        have hf₁ : Frm I.B (VG.Proof.Rsa.X86_64.rg (wk I.k) [] [sT]) s.mem t.mem := Frm.rg_of_hdr o₁ _ _ (List.mem_singleton_self _)
        dsimp only
        have hs₁ := VG.Proof.Rsa.X86_64.slot_add (wk I.k) aM 2
        have hs₂ := VG.Proof.Rsa.X86_64.slot_mono (w := wk I.k) (show aM + 2 ≤ 16 by decide)
        have hs₃ := hdr_lt_slot (wk I.k) aM (show sT < 32 by decide)
        exact ⟨hw.congrG hf₁ (by decide) k₁ (by decide), Keep.refl _ _, h13, Frm.refl _ _ _,
          by rw [o₁.wv (Or.inr (by omega)) (by omega), h.M]; rfl, by rw [m₁, VG.Proof.Bignum.X86_64.word_writeW_self]; rfl⟩

theorem halfLoop_ct : RelCT isa (Two fun p s => 0 < VG.Proof.Rsa.X86_64.Rp.hN p ∧ VG.Proof.Rsa.X86_64.Rp.HL p 0 s)
    (.loop (seqs [.block halfHead, wordLoop 0 shrBody, wordLoop 0 VG.Impl.Rsa.X86_64.Keys.selBody, .block halfNext]) .ne)
    (Two fun (_ : VG.Proof.Rsa.X86_64.RpP) (_ : State) => True) :=
  two_loop VG.Proof.Rsa.X86_64.Rp.hN VG.Proof.Rsa.X86_64.Rp.halfBody_ct fun p j s hj h => by
    obtain ⟨s₁, m, hel, he1, he2, hm, h11, hI⟩ := h
    exact WP.mono (VG.Proof.Rsa.X86_64.halfStep_ok hI hel he1 he2 hm h11 hj) fun s' ⟨hz, hI'⟩ =>
      ⟨eval_ne_count hj hz,
        fun _ => ⟨s₁, m, hel, he1, he2, hm, h11, hI'⟩, fun _ => trivial⟩

theorem halving_ct : RelCT isa (Two VG.Proof.Rsa.X86_64.Rp.GR0) halving (Two VG.Proof.Rsa.X86_64.Rp.GR1) :=
  two_post ((RelCT.seq VG.Proof.Rsa.X86_64.Rp.halfInit_ct VG.Proof.Rsa.X86_64.Rp.halfLoop_ct).mono (fun _ _ h => h) fun _ _ _ => trivial) fun p s h => by
    obtain ⟨I, m₀, rfl, h, O, hv⟩ := h
    have L := h.L
    have hZ16 : VG.Proof.Bignum.X86_64.slot (wk I.k) 16 ≤ 2 ^ 64 := by have := h.S.ws.scr.nowrap; have := h.S.ws.hZ; omega
    refine WP.mono (VG.Proof.Rsa.X86_64.halving_ok h.S.ws h.S.args.el L.el1 (by have := L.el2; unfold wk; omega) h.M h.m0 h.mlt)
      fun t ⟨_, hr₁, ht₁, hf₁', k₁⟩ => ?_
    have hf₁ := VG.Proof.Rsa.X86_64.frm_halving hf₁'
    refine ⟨I, m₀, rfl, h.S.step hf₁ (by decide) (by decide) k₁ (by decide), L, O, hv, h.odd, h.lo, ?_, ?_, hr₁, ht₁,
      h.m0, h.even, h.mlt⟩
    · rw [hf₁.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega)]; exact h.n
    · rw [hf₁.rg_word0 hZ16 (by decide) (by decide) (by decide), hf₁.rg_word (by decide) (by decide)]; exact h.inv

end Rp

end VG.Proof.Rsa.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rsa.X86_64.RpCT3`. -/
section

/-!
# `vg_rsa_recover_primes` on x86-64: constant time, Montgomery form

`mont` computes only from `n`, which is public: `R² mod n` leaks only
`n` (`r2_ct`, with `-n⁻¹`, a function of `n`, the same in both runs), and
the other pieces' loops count `w` words (`mont_ct`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aR2 aXm aY aOne sCnt)
open VG.Spec.Rsa (splitTwos)

namespace Rp

/-- Before `R² mod n`. -/
def MR (q : R2Pub) (s : State) : Prop :=
  R2Pre q s ∧ Ws s q.L.B q.L.Z q.L.w ∧ VG.Proof.Bignum.X86_64.word s.mem q.L.B (8 * sMinv) = q.L.minv

/-- Between `mont`'s pieces after `R² mod n`. -/
def MW (q : R2Pub) (s : State) : Prop :=
  Ws s q.L.B q.L.Z q.L.w ∧ VG.Proof.Bignum.X86_64.word s.mem q.L.B (8 * sMinv) = q.L.minv ∧
    wv s.mem q.L.B (VG.Proof.Bignum.X86_64.slot q.L.w aN) q.L.w = q.N ∧
    ((VG.Proof.Bignum.X86_64.word s.mem q.L.B (VG.Proof.Bignum.X86_64.slot q.L.w aN)).toNat * q.L.minv.toNat + 1) % 2 ^ 64 = 0 ∧ 1 < q.N

/-- Before `setWord aOne`. -/
def MB (q : R2Pub) (s : State) : Prop :=
  VG.Proof.Rsa.X86_64.Rp.MW q s ∧ s.gpr .r12 = BitVec.ofNat 64 q.L.w ∧ s.gpr .rcx = BitVec.ofNat 64 0 ∧ s.gpr .rdx = BitVec.ofNat 64 1

/-- After `setWord aOne`. -/
def MW1 (q : R2Pub) (s : State) : Prop := VG.Proof.Rsa.X86_64.Rp.MW q s ∧ wv s.mem q.L.B (VG.Proof.Bignum.X86_64.slot q.L.w aOne) q.L.w = 1

theorem pins_MW : Pins VG.Proof.Rsa.X86_64.Rp.MW [.rdi] := fun _ _ _ h₁ h₂ r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.rdi, h₂.1.rdi]

theorem pins_MB : Pins VG.Proof.Rsa.X86_64.Rp.MB [.rdi, .r12, .rcx] := fun _ _ _ h₁ h₂ r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [h₁.1.1.rdi, h₂.1.1.rdi]
  · rw [h₁.2.1, h₂.2.1]
  · rw [h₁.2.2.1, h₂.2.2.1]

/-- `MW` after a piece that changes only arrays other than `n`. -/
theorem MW.step {q : R2Pub} {s t : State} (h : VG.Proof.Rsa.X86_64.Rp.MW q s) {js : List Nat}
    (hf : Frm q.L.B (VG.Proof.Rsa.X86_64.rg q.L.w js []) s.mem t.mem) (hN : aN ∉ js)
    {regs : List Reg} (k : VG.Proof.MlKem.X86_64.Keep regs s t) (hr : .rdi ∉ regs) : VG.Proof.Rsa.X86_64.Rp.MW q t := by
  obtain ⟨hw, hmv, hn, hi, h1⟩ := h
  have hZ16 : VG.Proof.Bignum.X86_64.slot q.L.w 16 ≤ 2 ^ 64 := by have := hw.scr.nowrap; have := hw.hZ; omega
  refine ⟨hw.congrG hf (by simp) k hr, by rw [hf.rg_word (by decide) (by simp)]; exact hmv, ?_, ?_, h1⟩
  · rw [hf.rg_wv hZ16 (by simp) (by decide) hN (by omega)]; exact hn
  · rw [hf.rg_word0 hZ16 (by simp) (by decide) hN]; exact hi

theorem mr_bind (p : VG.Proof.Rsa.X86_64.RpP) (s₁ s₂ : State)
    (h₁ : ∃ minv, VG.Proof.Rsa.X86_64.Rp.MR ⟨⟨p.B, p.Z, wk p.k, minv⟩, Spec.Rsa.os2ip p.nb⟩ s₁)
    (h₂ : ∃ minv, VG.Proof.Rsa.X86_64.Rp.MR ⟨⟨p.B, p.Z, wk p.k, minv⟩, Spec.Rsa.os2ip p.nb⟩ s₂) : ∃ q, VG.Proof.Rsa.X86_64.Rp.MR q s₁ ∧ VG.Proof.Rsa.X86_64.Rp.MR q s₂ := by
  obtain ⟨mi₁, h₁⟩ := h₁
  obtain ⟨mi₂, h₂⟩ := h₂
  have e : ∀ {s : State} {mi : BitVec 64}, VG.Proof.Rsa.X86_64.Rp.MR ⟨⟨p.B, p.Z, wk p.k, mi⟩, Spec.Rsa.os2ip p.nb⟩ s →
      (VG.Proof.Bignum.X86_64.word s.mem p.B (VG.Proof.Bignum.X86_64.slot (wk p.k) aN)).toNat = Spec.Rsa.os2ip p.nb % 2 ^ 64 := fun h => by
    rw [← wv_mod64 _ _ _ (show 1 ≤ wk p.k by have : 2 ≤ wk p.k := h.1.2.1; omega), h.1.2.2.2.1]
  have i₁ := h₁.1.2.2.2.2.1
  have i₂ := h₂.1.2.2.2.2.1
  rw [e h₁] at i₁
  rw [e h₂] at i₂
  obtain rfl := minv_unique (by rw [Nat.mod_mod_of_dvd _ (by decide)]; exact h₁.1.2.2.2.2.2.2.2.1) i₁ i₂
  exact ⟨_, h₁, h₂⟩

/-- The loads of `w` and `n`'s base, and `R² mod n`. -/
theorem montR2_ct (M : Mont) :
    RelCT isa (Two VG.Proof.Rsa.X86_64.Rp.GR1) (.seq (.block [.mov .r12 (.mem (hdr sW)), .mov .r10 (.mem (hdr (sArr aN)))])
      (seqs (r2Steps M))) (Two VG.Proof.Rsa.X86_64.Rp.MW) := by
  refine RelCT.seq (R := Two VG.Proof.Rsa.X86_64.Rp.MR) ((two_piece (Ψ := fun p s => ∃ minv,
      VG.Proof.Rsa.X86_64.Rp.MR ⟨⟨p.B, p.Z, wk p.k, minv⟩, Spec.Rsa.os2ip p.nb⟩ s) [.rdi]
    (fun _ _ _ ⟨_, _, e₁, h₁, _⟩ ⟨_, _, e₂, h₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.ws.rdi, h₂.ws.rdi]
      exact (congrArg RpP.B e₁).trans (congrArg RpP.B e₂).symm) (by taint_decide) fun p s h => ?_).mono
    (fun _ _ h => h) fun _ _ h => two_bind VG.Proof.Rsa.X86_64.Rp.mr_bind h) ?_
  · obtain ⟨I, m₀, rfl, S, L, O, hv, hodd, hlo, hn, hinv, -⟩ := h
    dsimp only [RpIn.pub]
    have hw := S.ws
    have hn0 := hw.scr.nowrap
    have h256 := hw.h256
    have hZ := hw.hZ
    have hw1 := hw.w1
    have hw2 := hw.w2
    have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off I.B (8 * i)) 8 := fun i hi => hw.scr.ld (by omega)
    refine WP.mono (WP.keep [.r12, .r10] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 (wk I.k) ∧
        t.gpr .r10 = VG.Proof.Bignum.X86_64.off I.B (VG.Proof.Bignum.X86_64.slot (wk I.k) aN) ∧ t.mem = s.mem) (by
      xrun [State.ea, hdr, hw.rdi, hdrOff, hl _ (show sW < 32 by decide), hl _ (show sArr aN < 32 by decide),
        hw.hw, hw.harr aN (by decide)]) rfl) fun t ⟨⟨h12, h10, m₁⟩, k₁⟩ => ⟨VG.Proof.Bignum.X86_64.word t.mem I.B (8 * sMinv), ?_⟩
    have hw₁ : Ws t I.B I.Z (wk I.k) :=
      hw.congrG (js := []) (hs := []) (by rw [m₁]; exact Frm.refl _ _ _) (by simp) k₁ (by decide)
    exact ⟨⟨hw₁.good, hw1, show wk I.k < 2 ^ 30 by omega, by rw [m₁]; exact hn, by rw [m₁]; exact hinv, h12, h10, hodd, hlo⟩, hw₁, rfl⟩
  · refine two_post ((two_map id (fun _ _ h => h.1) (r2_ct M)).mono (fun _ _ h => h) fun _ _ _ => trivial)
      fun q s ⟨⟨hg, hw1, hw30, hn, hinv, h12, h10, hodd, hlo⟩, hw, hmv⟩ => ?_
    have hZ16 : VG.Proof.Bignum.X86_64.slot q.L.w 16 ≤ 2 ^ 64 := by have := hw.scr.nowrap; have := hw.hZ; omega
    have hN1 : 1 < q.N := by
      have : 2 ^ 64 ≤ 2 ^ (64 * (q.L.w - 1)) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    refine WP.mono (r2_ok M hg.1 hg.2 hw1 hw30 hn hinv h12 h10 hodd hlo) fun t ⟨hg₂, _, _, hf₂, k₂⟩ => ?_
    have hf₂' : Frm q.L.B (VG.Proof.Rsa.X86_64.rg q.L.w [aAcc, aTmp, aR2] [sCnt]) s.mem t.mem := hf₂
    exact ⟨hw.congrG hf₂' (by decide) k₂ (by decide), hg₂.hdr.hminv,
      by rw [hf₂'.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega)]; exact hn,
      by rw [hf₂'.rg_word0 hZ16 (by decide) (by decide) (by decide)]; exact hinv, hN1⟩

/-- `setWord`'s registers after its load. -/
def swVal (q : R2Pub) : Reg → BitVec 64
  | .r8 => VG.Proof.Bignum.X86_64.off q.L.B (VG.Proof.Bignum.X86_64.slot q.L.w aOne)
  | .r12 => BitVec.ofNat 64 q.L.w
  | .rcx => BitVec.ofNat 64 0
  | _ => 0

/-- 1, 0 and `w`. -/
theorem montB_ct : RelCT isa (Two VG.Proof.Rsa.X86_64.Rp.MW) (.block [.mov32 .rdx (.imm 1), .mov32 .rcx (.imm 0),
    .mov .r12 (.mem (hdr sW))]) (Two VG.Proof.Rsa.X86_64.Rp.MB) :=
  two_piece [.rdi] VG.Proof.Rsa.X86_64.Rp.pins_MW (by taint_decide) fun q s h => by
    have hw := h.1
    refine WP.mono (WP.keep [.rdx, .rcx, .r12] (Q := fun t => t.gpr .rdx = BitVec.ofNat 64 1 ∧
        t.gpr .rcx = BitVec.ofNat 64 0 ∧ t.gpr .r12 = BitVec.ofNat 64 q.L.w ∧ t.mem = s.mem) (by
      have := hw.h256
      xrun [State.ea, hdr, hw.rdi, hdrOff, hw.scr.ld (d := 8 * sW) (by simp only [sW]; omega), hw.hw]) rfl)
      fun t ⟨⟨hdx, hcx, h12, m⟩, k⟩ => ⟨h.step (js := []) (by rw [m]; exact Frm.refl _ _ _) (by simp) k (by decide), h12, hcx, hdx⟩

/-- 1 into its array. -/
theorem montSet_ct : RelCT isa (Two VG.Proof.Rsa.X86_64.Rp.MB) (setWord aOne .rcx) (Two VG.Proof.Rsa.X86_64.Rp.MW1) := by
  rw [setWord_eq]
  refine pin_ct [.rdi, .r12, .rcx] [.r8, .r12, .rcx] VG.Proof.Rsa.X86_64.Rp.swVal VG.Proof.Rsa.X86_64.Rp.pins_MB (by taint_decide) (fun q s h => ?_)
    (by taint_decide) fun q s h => ?_
  · have hw := h.1.1
    have := hw.h256
    have hl : InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off q.L.B (8 * sArr aOne)) 8 :=
      hw.scr.ld (by have := hw.hZ; have := hdr_lt_slot q.L.w 16 (show sArr aOne < 32 by decide); omega)
    refine WP.mono (WP.keep [.r8] (Q := fun t => t.gpr .r8 = VG.Proof.Bignum.X86_64.off q.L.B (VG.Proof.Bignum.X86_64.slot q.L.w aOne)) (by
      xrun [State.ea, hdr, hw.rdi, hdrOff, hl, hw.harr aOne (by decide)]) rfl) fun t ⟨h8, k⟩ r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h8
    · exact (k.gpr (by decide)).trans h.2.1
    · exact (k.gpr (by decide)).trans h.2.2.1
  · rw [← setWord_eq]
    obtain ⟨hM, h12, hcx, hdx⟩ := h
    have hw := hM.1
    have hw1 := hw.w1
    have hw2 := hw.w2
    have hH : Hdr s.mem q.L.B q.L.w q.L.minv := ⟨hw.hw, hM.2.1, fun j hj => hw.harr j hj⟩
    refine WP.mono (setWord_ok hw.scr hw.rdi hH hw.good.2 h12 (by omega) (by omega) (o := aOne) (by decide)
      (ri := .rcx) (by decide) (i := 0) (by omega) hcx) fun t ⟨hv, o, k⟩ => ?_
    rw [hdx, BitVec.toNat_ofNat] at hv
    have hf : Frm q.L.B (VG.Proof.Rsa.X86_64.rg q.L.w [aOne] []) s.mem t.mem := Frm.rg_of_out o (Nat.le_refl _) _ _ (by decide)
    exact ⟨hM.step hf (by decide) k (by decide), by rw [hv]; rfl⟩

/-- `Y = R mod n`. -/
theorem montY_ct (M : Mont) : RelCT isa (Two VG.Proof.Rsa.X86_64.Rp.MW1) (M.mm aY aR2 aOne) (Two VG.Proof.Rsa.X86_64.Rp.MW) :=
  two_post (two_map (fun q => (⟨q.L.B, q.L.Z, q.L.w⟩ : Bignum.X86_64.Ws)) (fun _ _ h => ⟨_, h.1.1.good⟩)
    (M.ct (by unfold MmUse; decide))) fun q s ⟨hM, h1⟩ => by
    have hw := hM.1
    have hg := hw.good
    rw [hM.2.1] at hg
    exact WP.mono (M.mm_ok hg.1 hg.2 hw.w1 (by have := hw.w2; omega) (o := aY) (a := aR2) (b := aOne) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hM.2.2.2.1
      (by rw [h1, hM.2.2.1]; exact hM.2.2.2.2)) fun t ⟨_, _, _, ha, k⟩ =>
      hM.step (Frm.rg_of_arrays ha [aAcc, aTmp, aY] [] (by decide)) (by decide) k (by decide)

/-- `R mod n` into its array. -/
theorem montO_ct : RelCT isa (Two VG.Proof.Rsa.X86_64.Rp.MW) (copyA aO aY) (Two fun (q : R2Pub) s => Ws s q.L.B q.L.Z q.L.w) := by
  have e : copyA aO aY = .seq (.block (VG.Impl.Rsa.X86_64.Keys.ws ++ (base aY .rsi ++ base aO .rbx))) VG.Impl.Rsa.X86_64.copyWords := by
    simp only [copyA, List.append_assoc]
  rw [e]
  exact ws_ct (Φ := VG.Proof.Rsa.X86_64.Rp.MW) (Ψ := fun q s => Ws s q.L.B q.L.Z q.L.w) (fun q : R2Pub => q.L.B) (fun q => q.L.Z) (fun q => q.L.w) (fun _ _ h => h.1) (by taint_decide)
    fun q s h => by
      rw [← e]
      exact WP.mono (copyA_ok h.1 (o := aO) (a := aY) (by decide) (by decide) (by decide)) fun t ⟨_, o, k⟩ =>
        h.1.congrG (Frm.rg_of_out o (by omega) [aO] [] (by decide)) (by simp) k (by decide)

/-- `n - R mod n`. -/
theorem montNg_ct : RelCT isa (Two fun (q : R2Pub) s => Ws s q.L.B q.L.Z q.L.w)
    (.seq (.block (VG.Impl.Rsa.X86_64.Keys.ws ++ base aN .r8 ++ base aO .r10 ++ base aNg .rsi ++ ([.mov32 .rbp (.imm 0)] : List Instr)))
      (wordLoop 0 subBody)) fun _ _ => True := by
  have e : (.seq (.block (VG.Impl.Rsa.X86_64.Keys.ws ++ base aN .r8 ++ base aO .r10 ++ base aNg .rsi ++ [.mov32 .rbp (.imm 0)]))
      (wordLoop 0 subBody) : Prog isa) = .seq (.block (VG.Impl.Rsa.X86_64.Keys.ws ++ (base aN .r8 ++ (base aO .r10 ++
        (base aNg .rsi ++ ([.mov32 .rbp (.imm 0)] : List Instr)))))) (wordLoop 0 subBody) := by
    simp only [List.append_assoc]
  rw [e]
  refine (ws_ct (Ψ := fun _ _ => True) (fun q : R2Pub => q.L.B) (fun q => q.L.Z) (fun q => q.L.w)
    (fun _ _ h => h) (by taint_decide) fun q s hw => ?_).mono (fun _ _ h => h) fun _ _ _ => trivial
  rw [← e]
  have hn0 := hw.scr.nowrap
  have hZ := hw.hZ
  have hw1 := hw.w1
  have hw2 := hw.w2
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86_64.subSet_ok hw aN aO aNg) fun t ⟨h12, h8, h10, hsi, hbp, _, k⟩ => ?_)
  exact WP.mono (VG.Proof.Rsa.X86_64.sub_ok (hw.scr.congr k.2.2) h8 h10 hsi h12 hbp (by omega) (by omega)
    (by have := hw.sl (j := aN) (by decide); omega) (by have := hw.sl (j := aO) (by decide); omega)
    (by have := hw.sl (j := aNg) (by decide); omega)
    (by have := slot_far (w := q.L.w) (show aNg ≠ aN by decide); omega)
    (by have := slot_far (w := q.L.w) (show aNg ≠ aO by decide); omega)) fun _ _ => trivial

/-- `mont` leaks only `n`. -/
theorem montT_ct (M : Mont) : RelCT isa (Two VG.Proof.Rsa.X86_64.Rp.GR1) (seqs (mont M.mm)) fun _ _ => True := by
  rw [show mont M.mm = ([.block [.mov .r12 (.mem (hdr sW)), .mov .r10 (.mem (hdr (sArr aN)))]] ++ r2Steps M) ++
    [.block [.mov32 .rdx (.imm 1), .mov32 .rcx (.imm 0), .mov .r12 (.mem (hdr sW))],
      setWord aOne .rcx, M.mm aY aR2 aOne, copyA aO aY,
      .block (VG.Impl.Rsa.X86_64.Keys.ws ++ base aN .r8 ++ base aO .r10 ++ base aNg .rsi ++ [.mov32 .rbp (.imm 0)]),
      wordLoop 0 subBody] from rfl]
  refine RelCT.seqs_append (by simp) (by simp) (RelCT.seq (VG.Proof.Rsa.X86_64.Rp.montR2_ct M) ?_)
  simp only [seqs]
  exact RelCT.seq VG.Proof.Rsa.X86_64.Rp.montB_ct (RelCT.seq VG.Proof.Rsa.X86_64.Rp.montSet_ct (RelCT.seq (VG.Proof.Rsa.X86_64.Rp.montY_ct M) (RelCT.seq VG.Proof.Rsa.X86_64.Rp.montO_ct VG.Proof.Rsa.X86_64.Rp.montNg_ct)))

/-- After Montgomery form: what the candidates need. -/
def GR2 (p : VG.Proof.Rsa.X86_64.RpP) (s : State) : Prop :=
  ∃ (I : VG.Proof.Rsa.X86_64.RpIn) (m₀ : Mem), I.pub = p ∧ VG.Proof.Rsa.X86_64.RpS I m₀ s ∧ VG.Proof.Rsa.X86_64.RpLens I ∧ VG.Proof.Rsa.X86_64.RpOuts I ∧
    Spec.Rsa.modulusValid I.N I.k = true ∧
    VG.Proof.Rsa.X86_64.Cst s I.B I.Z (wk I.k) (VG.Proof.Bignum.X86_64.word s.mem I.B (8 * sMinv)) I.N I.el (splitTwos (I.D * I.E - 1)).2
      (splitTwos (I.D * I.E - 1)).1 ∧ 0 < I.D * I.E - 1 ∧ (I.D * I.E - 1) % 2 = 0

theorem mont_ct (M : Mont) : RelCT isa (Two VG.Proof.Rsa.X86_64.Rp.GR1) (seqs (mont M.mm)) (Two VG.Proof.Rsa.X86_64.Rp.GR2) :=
  two_post (VG.Proof.Rsa.X86_64.Rp.montT_ct M) fun p s h => by
    obtain ⟨I, m₀, rfl, S₁, L, O, hv, hodd, hlo, hn₁, hi₁, hr₁, ht₁, hm0, heven, hmlt⟩ := h
    have hk1 := L.k1
    have hel1 := L.el1
    have hel2 := L.el2
    have hZ16 : VG.Proof.Bignum.X86_64.slot (wk I.k) 16 ≤ 2 ^ 64 := by have := S₁.ws.scr.nowrap; have := S₁.ws.hZ; omega
    refine WP.mono (VG.Proof.Rsa.X86_64.mont_ok M S₁.ws hi₁ hn₁ hodd hlo)
      fun s₂ ⟨_, hr2lt, hr2, hone, ho, hng, hf₂, k₂⟩ => ⟨I, m₀, rfl, ?_⟩
    have S₂ := S₁.step hf₂ (by decide) (by decide) k₂ (by decide)
    have hspl := VG.Proof.Rsa.splitTwos_spec hm0
    have hrlt : (splitTwos (I.D * I.E - 1)).2 < 2 ^ (64 * (wk I.k + (I.el + 7) / 8)) := by
      have : (splitTwos (I.D * I.E - 1)).2 ≤ I.D * I.E - 1 :=
        calc (splitTwos (I.D * I.E - 1)).2
            ≤ 2 ^ (splitTwos (I.D * I.E - 1)).1 * (splitTwos (I.D * I.E - 1)).2 :=
              Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
          _ = I.D * I.E - 1 := hspl.1.symm
      omega
    have ht1 : 1 ≤ (splitTwos (I.D * I.E - 1)).1 := by
      rcases Nat.eq_zero_or_pos (splitTwos (I.D * I.E - 1)).1 with h0 | h0
      · have := hspl.1; rw [h0, Nat.pow_zero, Nat.one_mul] at this; have := hspl.2; omega
      · exact h0
    have ht2 := VG.Proof.Rsa.splitTwos_lt hm0 hmlt
    refine ⟨S₂, L, O, hv, ⟨S₂.ws, rfl, ?_, ?_, hr2lt, hr2, hone, ho, hng, S₂.args.el, ?_, ?_, hodd, hlo, hel1,
      by unfold wk; omega, ht1, ht2⟩, hm0, heven⟩
    · rw [hf₂.rg_word0 hZ16 (by decide) (by decide) (by decide), hf₂.rg_word (by decide) (by decide)]; exact hi₁
    · rw [hf₂.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega)]; exact hn₁
    · rw [hf₂.rg_wv2 hZ16 (by decide) (by decide) (by decide) (by decide) (by unfold wk; omega)]
      rw [wv_low_of_lt (v := wk I.k + (I.el + 7) / 8) (w := 2 * (wk I.k + 2)) (by unfold wk; omega)
        (by rw [hr₁]; exact hrlt), hr₁]
    · rw [hf₂.rg_word (by decide) (by decide)]; exact ht₁

end Rp

end VG.Proof.Rsa.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rsa.X86_64.RpCT4`. -/
section

/-!
# `vg_rsa_recover_primes` on x86-64: constant time, the squarings

Pieces of a candidate leak the same in runs whose working spaces agree:
`copyA`, `eqA` and blocks checked from `rdi` (`copyA_gct`, `eqA_gct`,
`blk_gct`), a Montgomery multiplication (`mm_gct`). The squarings count a
public `64 Bw` (`sqLoop_ct`): their counter in `sC1` is pinned by
correctness.
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aR2 aXm aY aOne sCnt sMask)

namespace Rp

/-! ## Pieces, from correctness -/

theorem copyA_gct {α : Type} {Φ Ψ : α → State → Prop} (B : α → Addr) (Z w : α → Nat)
    (hws : ∀ a s, Φ a s → Ws s (B a) (Z a) (w a)) {o a : Nat} {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base a .rsi ++ base o .rbx))
      VG.Impl.Rsa.X86_64.copyWords) hc).isSome = true)
    (hw : ∀ x s, Φ x s → WP isa (copyA o a) s (Ψ x)) : RelCT isa (Two Φ) (copyA o a) (Two Ψ) := by
  have e : copyA o a = .seq (.block (VG.Impl.Rsa.X86_64.Keys.ws ++ (base a .rsi ++ base o .rbx))) VG.Impl.Rsa.X86_64.copyWords := by
    simp only [copyA, List.append_assoc]
  rw [e]
  exact ws_ct B Z w hws ht fun x s h => by rw [← e]; exact hw x s h

theorem eqA_gct {α : Type} {Φ Ψ : α → State → Prop} (B : α → Addr) (Z w : α → Nat)
    (hws : ∀ a s, Φ a s → Ws s (B a) (Z a) (w a)) {a b : Nat} {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base a .rbx ++ (base b .r10 ++
      ([.mov32 .rbp (.imm 0)] : List Instr)))) (wordLoop 0 xorBody)) hc).isSome = true)
    (hw : ∀ x s, Φ x s → WP isa (seqs (eqA a b)) s (Ψ x)) : RelCT isa (Two Φ) (seqs (eqA a b)) (Two Ψ) := by
  have e : seqs (eqA a b) = .seq (.block (VG.Impl.Rsa.X86_64.Keys.ws ++ (base a .rbx ++ (base b .r10 ++
      ([.mov32 .rbp (.imm 0)] : List Instr))))) (wordLoop 0 xorBody) := by
    simp only [eqA, seqs, List.append_assoc]
  rw [e]
  exact ws_ct B Z w hws ht fun x s h => by rw [← e]; exact hw x s h

theorem blk_gct {α : Type} {Φ Ψ : α → State → Prop} (B : α → Addr) (Z w : α → Nat)
    (hws : ∀ a s, Φ a s → Ws s (B a) (Z a) (w a)) {l : List Instr} {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi]) (.block l) hc).isSome = true)
    (hw : ∀ x s, Φ x s → WP isa (.block l) s (Ψ x)) : RelCT isa (Two Φ) (.block l) (Two Ψ) :=
  two_piece [.rdi] (fun x s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [(hws x s₁ h₁).rdi, (hws x s₂ h₂).rdi]) ht hw

theorem mm_gct {α : Type} {Φ Ψ : α → State → Prop} (B : α → Addr) (Z w : α → Nat)
    (hws : ∀ a s, Φ a s → Ws s (B a) (Z a) (w a)) (M : Mont) {o a b : Nat} (hu : MmUse o a b)
    (hw : ∀ x s, Φ x s → WP isa (M.mm o a b) s (Ψ x)) : RelCT isa (Two Φ) (M.mm o a b) (Two Ψ) :=
  two_post (two_map (fun x => (⟨B x, Z x, w x⟩ : Bignum.X86_64.Ws)) (fun x s h => ⟨_, (hws x s h).good⟩)
    (M.ct hu)) hw

/-! ## The squarings -/

/-- In a squaring: the constants, the counter `k` and the masks `done` and
`ok`, and `Y < n` if `hy`. -/
def SQ (hy : Bool) (p : VG.Proof.Rsa.X86_64.RpP) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (N r t k : Nat) (done ok : Bool), VG.Proof.Rsa.X86_64.Cst s p.B p.Z (wk p.k) minv N p.el r t ∧
    k < 64 * (wk p.k + (p.el + 7) / 8) ∧ VG.Proof.Bignum.X86_64.word s.mem p.B (8 * sC1) = BitVec.ofNat 64 k ∧
    VG.Proof.Bignum.X86_64.word s.mem p.B (8 * sC2) = VG.Proof.Bignum.X86_64.mask done ∧ VG.Proof.Bignum.X86_64.word s.mem p.B (8 * sC3) = VG.Proof.Bignum.X86_64.mask ok ∧
    (hy = true → wv s.mem p.B (VG.Proof.Bignum.X86_64.slot (wk p.k) aY) (wk p.k) < N)

/-- After the mask of `x = 1`. -/
def SQM (p : VG.Proof.Rsa.X86_64.RpP) (s : State) : Prop := VG.Proof.Rsa.X86_64.Rp.SQ false p s ∧ ∃ e1, VG.Proof.Bignum.X86_64.word s.mem p.B (8 * sMask) = VG.Proof.Bignum.X86_64.mask e1

theorem SQ.ws {hy : Bool} {p : VG.Proof.Rsa.X86_64.RpP} {s : State} (h : VG.Proof.Rsa.X86_64.Rp.SQ hy p s) : Ws s p.B p.Z (wk p.k) := by
  obtain ⟨_, _, _, _, _, _, _, hc, -⟩ := h
  exact hc.ws

/-- `SQ` after a piece that keeps the constants, `sC1`–`sC3`, and `Y` if
`hy`. -/
theorem SQ.step {hy : Bool} {p : VG.Proof.Rsa.X86_64.RpP} {s u : State} (h : VG.Proof.Rsa.X86_64.Rp.SQ hy p s) {js hs : List Nat}
    (hf : Frm p.B (VG.Proof.Rsa.X86_64.rg (wk p.k) js hs) s.mem u.mem) (hjs : ∀ j ∈ VG.Proof.Rsa.X86_64.cArr, j ∉ js)
    (hhs : ∀ i ∈ hs, rSlot i = true ∧ i ≠ sMinv ∧ i ≠ sT)
    (hc : ∀ i ∈ hs, i ≠ sC1 ∧ i ≠ sC2 ∧ i ≠ sC3) (hY : hy = true → aY ∉ js)
    {regs : List Reg} (k : VG.Proof.MlKem.X86_64.Keep regs s u) (hr : .rdi ∉ regs) : VG.Proof.Rsa.X86_64.Rp.SQ hy p u := by
  obtain ⟨minv, N, r, t, kk, done, ok, hcs, hk, h1, h2, h3, hyl⟩ := h
  have hZ16 := hcs.hZ16
  have h32 : ∀ i ∈ hs, i < 32 := fun i hi => by
    have := (hhs i hi).1; simp only [rSlot, Bool.or_eq_true, beq_iff_eq] at this; omega
  have hw : ∀ i, i < 32 → i ∉ hs → VG.Proof.Bignum.X86_64.word u.mem p.B (8 * i) = VG.Proof.Bignum.X86_64.word s.mem p.B (8 * i) := fun i hi hn =>
    hf.rg_word hi hn
  refine ⟨minv, N, r, t, kk, done, ok, hcs.congr hf hjs hhs k hr, hk, ?_, ?_, ?_, fun e => ?_⟩
  · rw [hw _ (by decide) fun hm => (hc _ hm).1 rfl]; exact h1
  · rw [hw _ (by decide) fun hm => (hc _ hm).2.1 rfl]; exact h2
  · rw [hw _ (by decide) fun hm => (hc _ hm).2.2 rfl]; exact h3
  · rw [hf.rg_wv hZ16 h32 (by decide) (hY e) (by omega)]; exact hyl e

/-- `sqLogic`'s and `sqNext`'s registers after `sqLogic`. -/
def sqVal (p : VG.Proof.Rsa.X86_64.RpP) : Reg → BitVec 64
  | .rdi => p.B
  | .r8 => VG.Proof.Bignum.X86_64.off p.B (VG.Proof.Bignum.X86_64.slot (wk p.k) aY)
  | .rsi => VG.Proof.Bignum.X86_64.off p.B (VG.Proof.Bignum.X86_64.slot (wk p.k) aX)
  | .r12 => BitVec.ofNat 64 (wk p.k)
  | _ => 0

/-- The masks, `y := x` if the squarings continue, and `k += 1`. -/
theorem sqTail_ct : RelCT isa (Two VG.Proof.Rsa.X86_64.Rp.SQM) (seqs [.block sqLogic, wordLoop 0 VG.Impl.Rsa.X86_64.Keys.selBody, .block sqNext])
    fun _ _ => True := by
  simp only [seqs]
  refine (pin_ct (Ψ := fun _ _ => True) [.rdi] [.rdi, .r8, .rsi, .r12] VG.Proof.Rsa.X86_64.Rp.sqVal
    (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.ws.rdi, h₂.1.ws.rdi])
    (by taint_decide) (fun p s h => ?_) (by taint_decide) fun p s h => ?_).mono (fun _ _ h => h)
      fun _ _ _ => trivial
  · obtain ⟨⟨minv, N, r, t, k, done, ok, hc, hk, h1, h2, h3, -⟩, e1, hm⟩ := h
    have he2 := hc.e2
    have hw2 := hc.ws.w2
    rw [VG.Proof.Rsa.X86_64.sqLogic_eq]
    refine WP.block_append_iff.mpr (WP.mono (VG.Proof.Rsa.X86_64.sqMasks_ok hc.ws (k := k) (t := t) (done := done) (ok := ok)
      (by omega) (by have := hc.t2; omega) h1 hc.ht h2 h3 hm rfl) fun u₆ ⟨_, m₆, k₆⟩ => ?_)
    have h256 := hc.ws.h256
    have hf₆ : Frm p.B (VG.Proof.Rsa.X86_64.rg (wk p.k) [] [sC2, sC3]) s.mem u₆.mem := by
      rw [m₆]
      exact (Frm.rg_of_hdr (VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (by simp only [sC2, sFn]; omega)) [] [sC2, sC3]
        (by decide)).trans (Frm.rg_of_hdr (VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (by simp only [sC3, sFn]; omega)) [] [sC2, sC3]
          (by decide))
    have hw₆ := hc.ws.congrG hf₆ (by decide) k₆ (by decide)
    refine WP.mono (VG.Proof.Rsa.X86_64.bases2_ok hw₆ aY aX) fun u₇ ⟨h12, h8, hsi, _, k₇⟩ r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (k₇.gpr (by decide)).trans hw₆.rdi
    · exact h8
    · exact hsi
    · exact h12
  · obtain ⟨⟨minv, N, r, t, k, done, ok, hc, hk, h1, h2, h3, -⟩, e1, hm⟩ := h
    have he2 := hc.e2
    have hw1 := hc.ws.w1
    have hw2 := hc.ws.w2
    have h256 := hc.ws.h256
    have hZ16 := hc.hZ16
    rw [VG.Proof.Rsa.X86_64.sqLogic_eq]
    refine WP.seq (WP.block_append_iff.mpr (WP.mono (VG.Proof.Rsa.X86_64.sqMasks_ok hc.ws (k := k) (t := t) (done := done) (ok := ok)
      (by omega) (by have := hc.t2; omega) h1 hc.ht h2 h3 hm rfl) fun u₆ ⟨hbp₆, m₆, k₆⟩ => ?_))
    have hf₆ : Frm p.B (VG.Proof.Rsa.X86_64.rg (wk p.k) [] [sC2, sC3]) s.mem u₆.mem := by
      rw [m₆]
      exact (Frm.rg_of_hdr (VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (by simp only [sC2, sFn]; omega)) [] [sC2, sC3]
        (by decide)).trans (Frm.rg_of_hdr (VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (by simp only [sC3, sFn]; omega)) [] [sC2, sC3]
          (by decide))
    have hc₆ := hc.congr hf₆ (by decide) (by decide) k₆ (by decide)
    refine WP.mono (VG.Proof.Rsa.X86_64.bases2_ok hc₆.ws aY aX) fun u₇ ⟨h12, h8, hsi, m₇, k₇⟩ => ?_
    have hc₇ := hc₆.congr (js := []) (hs := []) (by rw [m₇]; exact Frm.refl _ _ _) (by simp) (by simp) k₇
      (by decide)
    have hbp₇ : u₇.gpr .rbp = _ := (k₇.gpr (by decide)).trans hbp₆
    have sY := hc₇.ws.sl (j := aY) (by decide)
    have sX := hc₇.ws.sl (j := aX) (by decide)
    refine WP.seq (WP.mono (sel_ok hc₇.ws.scr h8 hsi hbp₇ h12 (by omega) (by omega) (by omega) (by omega)
      (by have := slot_far (w := wk p.k) (show aY ≠ aX by decide); omega)) fun u₈ ⟨_, o₈, k₈⟩ => ?_)
    have hf₈ : Frm p.B (VG.Proof.Rsa.X86_64.rg (wk p.k) [aY] []) u₇.mem u₈.mem := Frm.rg_of_out o₈ (by omega) _ _ (by decide)
    have hc₈ := hc₇.congr hf₈ (by decide) (by simp) k₈ (by decide)
    have hc1₈ : VG.Proof.Bignum.X86_64.word u₈.mem p.B (8 * sC1) = BitVec.ofNat 64 k := by
      rw [hf₈.rg_word (by decide) (by simp), m₇, hf₆.rg_word (by decide) (by decide)]; exact h1
    exact WP.mono (VG.Proof.Rsa.X86_64.sqNext_ok hc₈.ws hc₈.hel (by omega) hc1₈ hk) fun _ _ => trivial

/-- A squaring leaks the same in runs that agree on the public data. -/
theorem sqBody_ct (M : Mont) : RelCT isa (Two (VG.Proof.Rsa.X86_64.Rp.SQ true)) (sqBody M.mm) fun _ _ => True := by
  have hB : ∀ (hy : Bool) p s, VG.Proof.Rsa.X86_64.Rp.SQ hy p s → Ws s p.B p.Z (wk p.k) := fun _ _ _ h => h.ws
  rw [show sqBody M.mm = seqs ([copyA aX aY, M.mm aX aX aY] ++ (eqA aX aO ++ ([.block (eqStore sMask)] ++
    (eqA aX aNg ++ [.block sqLogic, wordLoop 0 VG.Impl.Rsa.X86_64.Keys.selBody, .block sqNext])))) by
      simp only [sqBody, List.append_assoc]]
  refine RelCT.seqs_append (by simp) (by simp [eqA]) (RelCT.seq (R := Two (VG.Proof.Rsa.X86_64.Rp.SQ false)) ?_ ?_)
  · simp only [seqs]
    refine RelCT.seq (R := Two (VG.Proof.Rsa.X86_64.Rp.SQ true)) (VG.Proof.Rsa.X86_64.Rp.copyA_gct RpP.B RpP.Z (fun p => wk p.k) (hB true) (by taint_decide)
      fun p s h => ?_) (VG.Proof.Rsa.X86_64.Rp.mm_gct RpP.B RpP.Z (fun p => wk p.k) (hB true) M (by unfold MmUse; decide) fun p s h => ?_)
    · have hw := h.ws
      exact WP.mono (copyA_ok hw (o := aX) (a := aY) (by decide) (by decide) (by decide)) fun u ⟨_, o, k⟩ =>
        h.step (Frm.rg_of_out o (by omega) [aX] [] (by decide)) (by decide) (by simp) (by simp) (by decide) k
          (by decide)
    · obtain ⟨minv, N, r, t, kk, done, ok, hc, hk, h1, h2, h3, hyl⟩ := h
      have hg := hc.good
      have hw2 := hc.ws.w2
      exact WP.mono (M.mm_ok hg.1 hg.2 hc.ws.w1 (by omega) (o := aX) (a := aX) (b := aY) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.hinv
        (by rw [hc.hn]; exact hyl rfl)) fun u ⟨_, _, _, ha, k⟩ =>
        (show VG.Proof.Rsa.X86_64.Rp.SQ false p s from ⟨minv, N, r, t, kk, done, ok, hc, hk, h1, h2, h3, fun e => by cases e⟩).step
          (Frm.rg_of_arrays ha [aX, aAcc, aTmp] [] (by decide)) (by decide) (by simp) (by simp) (by simp) k
          (by decide)
  refine RelCT.seqs_append (by simp [eqA]) (by simp) (RelCT.seq (R := Two (VG.Proof.Rsa.X86_64.Rp.SQ false))
    (VG.Proof.Rsa.X86_64.Rp.eqA_gct RpP.B RpP.Z (fun p => wk p.k) (hB false) (by taint_decide) fun p s h => ?_) ?_)
  · exact WP.mono (eqA_ok h.ws (a := aX) (b := aO) (by decide) (by decide)) fun u ⟨_, m, k⟩ =>
      h.step (js := []) (hs := []) (by rw [m]; exact Frm.refl _ _ _) (by simp) (by simp) (by simp) (by simp) k
        (by decide)
  refine RelCT.seqs_append (by simp) (by simp [eqA]) (RelCT.seq (R := Two VG.Proof.Rsa.X86_64.Rp.SQM) ?_ ?_)
  · simp only [seqs]
    refine VG.Proof.Rsa.X86_64.Rp.blk_gct RpP.B RpP.Z (fun p => wk p.k) (hB false) (by taint_decide) fun p s h => ?_
    have h256 := h.ws.h256
    refine WP.mono (VG.Proof.Rsa.X86_64.eqStore_ok h.ws (i := sMask) (by decide) (by decide)) fun u ⟨m, k⟩ => ⟨?_, decide (s.gpr .rbp = 0), ?_⟩
    · exact h.step (js := []) (Frm.rg_of_hdr (m ▸ VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (by simp only [sMask, sFn]; omega))
        [] [sMask] (List.mem_singleton_self _)) (by decide) (by decide) (by decide) (by simp) k (by decide)
    · rw [m, VG.Proof.Bignum.X86_64.word_writeW_self]
  refine RelCT.seqs_append (by simp [eqA]) (by simp) (RelCT.seq (R := Two VG.Proof.Rsa.X86_64.Rp.SQM)
    (VG.Proof.Rsa.X86_64.Rp.eqA_gct RpP.B RpP.Z (fun p => wk p.k) (fun p s h => h.1.ws) (by taint_decide) fun p s h => ?_) VG.Proof.Rsa.X86_64.Rp.sqTail_ct)
  have hZ16 := h.1.ws.scr.nowrap
  have h256 := h.1.ws.h256
  obtain ⟨h, e1, hm⟩ := h
  exact WP.mono (eqA_ok h.ws (a := aX) (b := aNg) (by decide) (by decide)) fun u ⟨_, m, k⟩ =>
    ⟨h.step (js := []) (hs := []) (by rw [m]; exact Frm.refl _ _ _) (by simp) (by simp) (by simp) (by simp) k
      (by decide), e1, by rw [m]; exact hm⟩

/-- The squarings' invariant: `k` squarings from `t₀`. -/
def SQI (p : VG.Proof.Rsa.X86_64.RpP) (k : Nat) (u : State) : Prop :=
  ∃ (t₀ : State) (minv : BitVec 64) (N r t : Nat) (st₀ : Nat × Bool × Bool),
    VG.Proof.Rsa.X86_64.Cst t₀ p.B p.Z (wk p.k) minv N p.el r t ∧ VG.Proof.Rsa.X86_64.SqI t₀ p.B (wk p.k) N t st₀ k u

/-- The squarings: `64 Bw` of them. -/
theorem sqLoop_ct (M : Mont) : RelCT isa (Two fun p s => 0 < 64 * (wk p.k + (p.el + 7) / 8) ∧ VG.Proof.Rsa.X86_64.Rp.SQI p 0 s)
    (.loop (sqBody M.mm) .ne) (Two fun p s => VG.Proof.Rsa.X86_64.Rp.SQI p (64 * (wk p.k + (p.el + 7) / 8)) s) :=
  two_loop (fun p => 64 * (wk p.k + (p.el + 7) / 8))
    (two_map (fun q => q.1) (fun q s hq => by
      obtain ⟨hk, t₀, minv, N, r, t, st₀, hc, hI⟩ := hq
      have hcu := hc.congr hI.frm (by decide) VG.Proof.Rsa.X86_64.sq_hs hI.keep (by decide)
      have hN : 0 < N := by have := hc.n1; omega
      exact ⟨minv, N, r, t, q.2, _, _, hcu, hk, hI.c1, hI.c2, hI.c3, fun _ => by
        rw [hI.y]; exact Nat.mod_lt _ hN⟩) (VG.Proof.Rsa.X86_64.Rp.sqBody_ct M))
    fun p k s hk ⟨t₀, minv, N, r, t, st₀, hc, hI⟩ =>
      WP.mono (VG.Proof.Rsa.X86_64.sqBody_ok M hc hk hI) fun s' ⟨hz, hI'⟩ =>
        ⟨eval_ne_count hk hz, fun _ => ⟨t₀, minv, N, r, t, st₀, hc, hI'⟩,
          fun e => e ▸ ⟨t₀, minv, N, r, t, st₀, hc, hI'⟩⟩

end Rp

end VG.Proof.Rsa.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rsa.X86_64.RpCT5`. -/
section

/-!
# `vg_rsa_recover_primes` on x86-64: constant time, the exponentiation

`Bw` words of 64 bits each, public counts (`expLoop_ct`): the counters in
`sC1` and `sC3` are pinned by correctness, and so is the index of the word
`wordHead` loads.
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aR2 aXm aY aOne sCnt sMask)

namespace Rp

/-- The words of `r`. -/
abbrev bW (p : VG.Proof.Rsa.X86_64.RpP) : Nat := wk p.k + (p.el + 7) / 8

/-! ## A bit -/

theorem RelCT.seq_assoc {P Q : State → State → Prop} {a b c : Prog isa}
    (h : RelCT isa P (.seq (.seq a b) c) Q) : RelCT isa P (.seq a (.seq b c)) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | seq ea e' =>
    cases e' with
    | seq eb ec =>
      cases e₂ with
      | seq fa f' =>
        cases f' with
        | seq fb fc =>
          have := h _ _ _ _ _ _ hp (.seq (.seq ea eb) ec) (.seq (.seq fa fb) fc)
          simpa only [List.append_assoc] using this

/-- In a bit: the constants, `Y < n`, `G < n`, and `Xm < n` if `hx`. -/
def BT (hx : Bool) (p : VG.Proof.Rsa.X86_64.RpP) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (N r t : Nat), VG.Proof.Rsa.X86_64.Cst s p.B p.Z (wk p.k) minv N p.el r t ∧
    wv s.mem p.B (VG.Proof.Bignum.X86_64.slot (wk p.k) aY) (wk p.k) < N ∧ wv s.mem p.B (VG.Proof.Bignum.X86_64.slot (wk p.k) aG) (wk p.k) < N ∧
    (hx = true → wv s.mem p.B (VG.Proof.Bignum.X86_64.slot (wk p.k) aXm) (wk p.k) < N)

theorem BT.ws {hx : Bool} {p : VG.Proof.Rsa.X86_64.RpP} {s : State} (h : VG.Proof.Rsa.X86_64.Rp.BT hx p s) : Ws s p.B p.Z (wk p.k) := by
  obtain ⟨_, _, _, _, hc, -⟩ := h
  exact hc.ws

/-- `bitSel`'s and the selection's registers. -/
def selVal (p : VG.Proof.Rsa.X86_64.RpP) : Reg → BitVec 64
  | .rdi => p.B
  | .r8 => VG.Proof.Bignum.X86_64.off p.B (VG.Proof.Bignum.X86_64.slot (wk p.k) aXm)
  | .rsi => VG.Proof.Bignum.X86_64.off p.B (VG.Proof.Bignum.X86_64.slot (wk p.k) aG)
  | .r12 => BitVec.ofNat 64 (wk p.k)
  | _ => 0

/-- The bit, and the multiplicand `G` or `R mod n`. -/
theorem bitSel_ct : RelCT isa (Two (VG.Proof.Rsa.X86_64.Rp.BT true)) (.seq (.block bitSel) (wordLoop 0 VG.Impl.Rsa.X86_64.Keys.selBody)) (Two (VG.Proof.Rsa.X86_64.Rp.BT true)) := by
  refine pin_ct [.rdi] [.rdi, .r8, .rsi, .r12] VG.Proof.Rsa.X86_64.Rp.selVal (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.ws.rdi, h₂.ws.rdi])
    (by taint_decide) (fun p s h => ?_) (by taint_decide) fun p s h => ?_
  · have hw := h.ws
    refine WP.mono (VG.Proof.Rsa.X86_64.bitSel_ok hw (V := (VG.Proof.Bignum.X86_64.word s.mem p.B (8 * sC2)).toNat) (by rw [BitVec.ofNat_toNat,
                                                 BitVec.setWidth_eq]) (BitVec.isLt _)) fun t ⟨_, h8, hsi, h12, _, k⟩ r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (k.gpr (by decide)).trans hw.rdi
    · exact h8
    · exact hsi
    · exact h12
  · obtain ⟨minv, N, r, t, hc, hY, hG, hX⟩ := h
    have hZ16 := hc.hZ16
    have hw1 := hc.ws.w1
    have hw2 := hc.ws.w2
    have h256 := hc.ws.h256
    refine WP.seq (WP.mono (VG.Proof.Rsa.X86_64.bitSel_ok hc.ws (V := (VG.Proof.Bignum.X86_64.word s.mem p.B (8 * sC2)).toNat) (by rw [BitVec.ofNat_toNat,
                                                 BitVec.setWidth_eq]) (BitVec.isLt _)) fun u₂ ⟨hbp, h8, hsi, h12, m₂, k₂⟩ => ?_)
    have hf₂ : Frm p.B (VG.Proof.Rsa.X86_64.rg (wk p.k) [] [sC2]) s.mem u₂.mem := by
      rw [m₂]; exact Frm.rg_of_hdr (VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (by simp only [sC2, sFn]; omega)) _ _
        (List.mem_singleton_self _)
    have hc₂ := hc.congr hf₂ (by decide) (by decide) k₂ (by decide)
    have sXm := hc₂.ws.sl (j := aXm) (by decide)
    have sG := hc₂.ws.sl (j := aG) (by decide)
    refine WP.mono (sel_ok hc₂.ws.scr h8 hsi hbp h12 (by omega) (by omega) (by omega) (by omega)
      (by have := slot_far (w := wk p.k) (show aXm ≠ aG by decide); omega)) fun u₃ ⟨hx₃, o₃, k₃⟩ => ?_
    have hf₃ : Frm p.B (VG.Proof.Rsa.X86_64.rg (wk p.k) [aXm] []) u₂.mem u₃.mem := Frm.rg_of_out o₃ (by omega) _ _ (by decide)
    have hc₃ := hc₂.congr hf₃ (by decide) (by simp) k₃ (by decide)
    have e₂ : ∀ j, j < 16 → j ≠ aXm →
        wv u₃.mem p.B (VG.Proof.Bignum.X86_64.slot (wk p.k) j) (wk p.k) = wv s.mem p.B (VG.Proof.Bignum.X86_64.slot (wk p.k) j) (wk p.k) := fun j hj hne => by
      rw [hf₃.rg_wv hZ16 (by simp) hj (by simpa using hne) (by omega),
        hf₂.rg_wv hZ16 (by decide) hj (by simp) (by omega)]
    refine ⟨minv, N, r, t, hc₃, by rw [e₂ _ (by decide) (by decide)]; exact hY,
      by rw [e₂ _ (by decide) (by decide)]; exact hG, fun _ => ?_⟩
    rw [hx₃, hf₂.rg_wv hZ16 (by decide) (by decide) (by simp) (by omega),
      hf₂.rg_wv hZ16 (by decide) (by decide) (by simp) (by omega)]
    split
    · exact hX rfl
    · exact hG

/-- A bit leaks the same in runs that agree on the public data. -/
theorem bitBody_ct (M : Mont) : RelCT isa (Two (VG.Proof.Rsa.X86_64.Rp.BT false)) (bitBody M.mm) fun _ _ => True := by
  have hB : ∀ (hx : Bool) p s, VG.Proof.Rsa.X86_64.Rp.BT hx p s → Ws s p.B p.Z (wk p.k) := fun _ _ _ h => h.ws
  simp only [bitBody, seqs]
  refine RelCT.seq (R := Two (VG.Proof.Rsa.X86_64.Rp.BT true)) (VG.Proof.Rsa.X86_64.Rp.copyA_gct RpP.B RpP.Z (fun p => wk p.k) (hB false) (by taint_decide)
    fun p s h => ?_) ?_
  · obtain ⟨minv, N, r, t, hc, hY, hG, -⟩ := h
    have hZ16 := hc.hZ16
    have hN : 0 < N := by have := hc.n1; omega
    refine WP.mono (copyA_ok hc.ws (o := aXm) (a := aO) (by decide) (by decide) (by decide))
      fun u ⟨hx, o, k⟩ => ?_
    have hf : Frm p.B (VG.Proof.Rsa.X86_64.rg (wk p.k) [aXm] []) s.mem u.mem := Frm.rg_of_out o (by omega) _ _ (by decide)
    refine ⟨minv, N, r, t, hc.congr hf (by decide) (by simp) k (by decide), ?_, ?_, fun _ => ?_⟩
    · rw [hf.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega)]; exact hY
    · rw [hf.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega)]; exact hG
    · rw [hx, hc.ho]; exact Nat.mod_lt _ hN
  refine RelCT.seq_assoc (RelCT.seq VG.Proof.Rsa.X86_64.Rp.bitSel_ct (RelCT.seq (R := Two (VG.Proof.Rsa.X86_64.Rp.BT true)) (VG.Proof.Rsa.X86_64.Rp.mm_gct RpP.B RpP.Z (fun p => wk p.k)
    (hB true) M (o := aY) (a := aY) (b := aY) (by unfold MmUse; decide) fun p s h => ?_)
    (RelCT.seq (R := Two (VG.Proof.Rsa.X86_64.Rp.BT false)) (VG.Proof.Rsa.X86_64.Rp.mm_gct RpP.B RpP.Z (fun p => wk p.k) (hB true) M (o := aY) (a := aY)
      (b := aXm) (by unfold MmUse; decide) fun p s h => ?_)
    (two_taint [.rdi] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.ws.rdi, h₂.ws.rdi]) (by taint_decide)))))
  · obtain ⟨minv, N, r, t, hc, hY, hG, hX⟩ := h
    have hZ16 := hc.hZ16
    have hg := hc.good
    have hw2 := hc.ws.w2
    refine WP.mono (M.mm_ok hg.1 hg.2 hc.ws.w1 (by omega) (o := aY) (a := aY) (b := aY) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.hinv
      (by rw [hc.hn]; exact hY)) fun u ⟨_, hlt, _, ha, k⟩ => ?_
    rw [hc.hn] at hlt
    have hf : Frm p.B (VG.Proof.Rsa.X86_64.rg (wk p.k) [aAcc, aTmp, aY] []) s.mem u.mem := Frm.rg_of_arrays ha _ _ (by decide)
    refine ⟨minv, N, r, t, hc.congr hf (by decide) (by simp) k (by decide), hlt, ?_, fun _ => ?_⟩
    · rw [hf.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega)]; exact hG
    · rw [hf.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega)]; exact hX rfl
  · obtain ⟨minv, N, r, t, hc, hY, hG, hX⟩ := h
    have hZ16 := hc.hZ16
    have hg := hc.good
    have hw2 := hc.ws.w2
    refine WP.mono (M.mm_ok hg.1 hg.2 hc.ws.w1 (by omega) (o := aY) (a := aY) (b := aXm) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.hinv
      (by rw [hc.hn]; exact hX rfl)) fun u ⟨_, hlt, _, ha, k⟩ => ?_
    rw [hc.hn] at hlt
    have hf : Frm p.B (VG.Proof.Rsa.X86_64.rg (wk p.k) [aAcc, aTmp, aY] []) s.mem u.mem := Frm.rg_of_arrays ha _ _ (by decide)
    refine ⟨minv, N, r, t, hc.congr hf (by decide) (by simp) k (by decide), hlt, ?_, fun e => by cases e⟩
    rw [hf.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega)]; exact hG

/-- The bits' invariant: `j` bits of the word `V` from `t₀`. -/
def BI (p : VG.Proof.Rsa.X86_64.RpP) (j : Nat) (u : State) : Prop :=
  ∃ (t₀ : State) (minv : BitVec 64) (N r t g e V : Nat), VG.Proof.Rsa.X86_64.Cst t₀ p.B p.Z (wk p.k) minv N p.el r t ∧
    wv t₀.mem p.B (VG.Proof.Bignum.X86_64.slot (wk p.k) aG) (wk p.k) < N ∧
    wv t₀.mem p.B (VG.Proof.Bignum.X86_64.slot (wk p.k) aG) (wk p.k) % N = g * 2 ^ (64 * wk p.k) % N ∧ V = e % 2 ^ 64 ∧
    VG.Proof.Rsa.X86_64.BitInv t₀ p.B (wk p.k) N g e V j u

theorem bitLoop_ct (M : Mont) : RelCT isa (Two fun (p : VG.Proof.Rsa.X86_64.RpP) s => 0 < 64 ∧ VG.Proof.Rsa.X86_64.Rp.BI p 0 s) (.loop (bitBody M.mm) .ne)
    (Two fun p s => VG.Proof.Rsa.X86_64.Rp.BI p 64 s) :=
  two_loop (fun _ => 64) (two_map (fun q => q.1) (fun q s hq => by
      obtain ⟨-, t₀, minv, N, r, t, g, e, V, hc, hGlt, -, -, hI⟩ := hq
      have hZ16 := hc.hZ16
      have hcu := hc.congr hI.frm (by decide) VG.Proof.Rsa.X86_64.bit_hs hI.keep (by decide)
      refine ⟨minv, N, r, t, hcu, hI.ylt, ?_, fun e => by cases e⟩
      rw [hI.frm.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega)]; exact hGlt) (VG.Proof.Rsa.X86_64.Rp.bitBody_ct M))
    fun p j s hj ⟨t₀, minv, N, r, t, g, e, V, hc, hGlt, hG, hV, hI⟩ =>
      WP.mono (VG.Proof.Rsa.X86_64.bitBody_ok M hc hGlt hG hV hj hI) fun s' ⟨hz, hI'⟩ =>
        ⟨eval_ne_count hj hz, fun _ => ⟨t₀, minv, N, r, t, g, e, V, hc, hGlt, hG, hV, hI'⟩,
          fun h => h ▸ ⟨t₀, minv, N, r, t, g, e, V, hc, hGlt, hG, hV, hI'⟩⟩

/-! ## A word -/

/-- The words' invariant: `k` words of `r` from `t₀`. -/
def WI (p : VG.Proof.Rsa.X86_64.RpP) (k : Nat) (u : State) : Prop :=
  ∃ (t₀ : State) (minv : BitVec 64) (N r t g : Nat), VG.Proof.Rsa.X86_64.Cst t₀ p.B p.Z (wk p.k) minv N p.el r t ∧
    wv t₀.mem p.B (VG.Proof.Bignum.X86_64.slot (wk p.k) aG) (wk p.k) < N ∧
    wv t₀.mem p.B (VG.Proof.Bignum.X86_64.slot (wk p.k) aG) (wk p.k) % N = g * 2 ^ (64 * wk p.k) % N ∧
    VG.Proof.Rsa.X86_64.WordInv t₀ p.B (wk p.k) N g r (VG.Proof.Rsa.X86_64.Rp.bW p) k u

theorem wordHead_eq : wordHead = (VG.Impl.Rsa.X86_64.Keys.ws ++ (base aM .rbx ++ ([.mov .rax (.mem (hdr sC1)), .alu .sub .rax (.imm 1)] :
    List Instr))) ++ ([.mov .rax (.mem (ix .rbx .rax)), .store (hdr sC2) .rax, .mov32 .rax (.imm 64),
      .store (hdr sC3) .rax] : List Instr) := by
  simp only [wordHead, List.append_assoc, List.cons_append, List.nil_append]

/-- `wordHead`'s registers before its load of the word. -/
def headVal (q : VG.Proof.Rsa.X86_64.RpP × Nat) : Reg → BitVec 64
  | .rdi => q.1.B
  | .rbx => VG.Proof.Bignum.X86_64.off q.1.B (VG.Proof.Bignum.X86_64.slot (wk q.1.k) aM)
  | .rax => BitVec.ofNat 64 (VG.Proof.Rsa.X86_64.Rp.bW q.1 - q.2 - 1)
  | _ => 0

theorem wordHead_ct : RelCT isa (Two fun (q : VG.Proof.Rsa.X86_64.RpP × Nat) s => q.2 < VG.Proof.Rsa.X86_64.Rp.bW q.1 ∧ VG.Proof.Rsa.X86_64.Rp.WI q.1 q.2 s) (.block wordHead)
    (Two fun (q : VG.Proof.Rsa.X86_64.RpP × Nat) s => 0 < 64 ∧ VG.Proof.Rsa.X86_64.Rp.BI q.1 0 s) := by
  rw [VG.Proof.Rsa.X86_64.Rp.wordHead_eq]
  refine RelCT.block_append (VG.Proof.Rsa.X86_64.ws_pin_ct (fun q : VG.Proof.Rsa.X86_64.RpP × Nat => q.1.B) (fun q => q.1.Z) (fun q => wk q.1.k)
    (fun (q : VG.Proof.Rsa.X86_64.RpP × Nat) s ⟨_, t₀, minv, N, r, t, g, hc, _, _, hI⟩ => (hc.congr hI.frm (by decide) VG.Proof.Rsa.X86_64.word_hs hI.keep
      (by decide)).ws) (by taint_decide) [.rdi, .rbx, .rax] VG.Proof.Rsa.X86_64.Rp.headVal (fun q s h => ?_) (by taint_decide)
    fun q s h => ?_)
  · obtain ⟨hk, t₀, minv, N, r, t, g, hc, _, _, hI⟩ := h
    have hcu := hc.congr hI.frm (by decide) VG.Proof.Rsa.X86_64.word_hs hI.keep (by decide)
    have h256 := hcu.ws.h256
    have he2 := hc.e2
    have hw2 := hc.ws.w2
    rw [WP.block_append_iff]
    refine WP.mono hcu.ws.ws_ok fun u₁ ⟨_, h9, m₁, k₁⟩ => WP.block_append_iff.mpr ?_
    refine WP.mono (base_ok aM (r := .rbx) (by decide) ((k₁.gpr (by decide)).trans hcu.ws.rdi) h9)
      fun u₂ ⟨hbx, m₂, k₂⟩ => ?_
    have k12 := k₁.trans k₂
    have hs₂ := hcu.ws.scr.congr k12.2.2
    have hdi₂ : u₂.gpr .rdi = q.1.B := (k12.gpr (by decide)).trans hcu.ws.rdi
    have hc1 := hI.c1
    have hk' : q.2 < wk q.1.k + (q.1.el + 7) / 8 := hk
    have e1 : BitVec.ofNat 64 (VG.Proof.Rsa.X86_64.Rp.bW q.1 - q.2) - 1 = BitVec.ofNat 64 (VG.Proof.Rsa.X86_64.Rp.bW q.1 - q.2 - 1) :=
      ofNat64_pred (by simp only [VG.Proof.Rsa.X86_64.Rp.bW]; omega) (by simp only [VG.Proof.Rsa.X86_64.Rp.bW]; unfold wk at *; omega)
    refine WP.mono (WP.keep [.rax] (Q := fun u => u.gpr .rax = BitVec.ofNat 64 (VG.Proof.Rsa.X86_64.Rp.bW q.1 - q.2 - 1)) (by
      xrun [State.ea, hdr, hdi₂, hdrOff, hs₂.ld (d := 8 * sC1) (by simp only [sC1, sCnt, sFn]; omega), m₂, m₁,
        hc1, e1]) rfl) fun u ⟨hax, k₃⟩ r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (k₃.gpr (by decide)).trans hdi₂
    · exact (k₃.gpr (by decide)).trans hbx
    · exact hax
  · obtain ⟨hk, t₀, minv, N, r, t, g, hc, hGlt, hG, hI⟩ := h
    have hZ16 := hc.hZ16
    have he2 := hc.e2
    have hw2 := hc.ws.w2
    have hm := hc.hm
    have hk' : q.2 < wk q.1.k + (q.1.el + 7) / 8 := hk
    have hBw2 : wk q.1.k + (q.1.el + 7) / 8 ≤ 2 * (wk q.1.k + 2) := by unfold wk at *; omega
    have hcu := hc.congr hI.frm (by decide) VG.Proof.Rsa.X86_64.word_hs hI.keep (by decide)
    obtain ⟨i, hi₀⟩ : ∃ i, wk q.1.k + (q.1.el + 7) / 8 - q.2 = i + 1 := ⟨wk q.1.k + (q.1.el + 7) / 8 - q.2 - 1, by omega⟩
    have hi : VG.Proof.Rsa.X86_64.Rp.bW q.1 - q.2 = i + 1 := hi₀
    have hc1 : VG.Proof.Bignum.X86_64.word s.mem q.1.B (8 * sC1) = BitVec.ofNat 64 (i + 1) := by rw [← hi]; exact hI.c1
    have sM := slot_lt (w := wk q.1.k) (show aM + 1 < 16 by decide)
    have eM1 : VG.Proof.Bignum.X86_64.slot (wk q.1.k) (aM + 1) = VG.Proof.Bignum.X86_64.slot (wk q.1.k) aM + 8 * (wk q.1.k + 2) := by
      simp only [VG.Proof.Bignum.X86_64.slot, hdrBytes, aM]; omega
    have hZ := hcu.ws.hZ
    rw [WP.seq_iff, ← WP.block_append_iff, ← VG.Proof.Rsa.X86_64.Rp.wordHead_eq]
    refine WP.mono (VG.Proof.Rsa.X86_64.wordHead_ok hcu.ws hc1 (by omega) (by omega)) fun u₁ ⟨m₁, k₁⟩ => ⟨by decide, ?_⟩
    have hW : (VG.Proof.Bignum.X86_64.word s.mem q.1.B (VG.Proof.Bignum.X86_64.slot (wk q.1.k) aM + 8 * i)).toNat = r / 2 ^ (64 * i) % 2 ^ 64 := by
      have := word_of_wv s.mem q.1.B (VG.Proof.Bignum.X86_64.slot (wk q.1.k) aM) (VG.Proof.Rsa.X86_64.Rp.bW q.1) (q := i) (by omega)
      rw [hcu.hm] at this
      exact this
    have hf₁ : Frm q.1.B (VG.Proof.Rsa.X86_64.rg (wk q.1.k) [] [sC2, sC3]) s.mem u₁.mem := by
      rw [m₁]
      exact (Frm.rg_of_hdr (VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (by simp only [sC2, sFn]; omega)) [] [sC2, sC3]
        (by decide)).trans (Frm.rg_of_hdr (VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (by simp only [sC3, sFn]; omega)) [] [sC2, sC3]
          (by decide))
    have hc₁ := hcu.congr hf₁ (by decide) (by decide) k₁ (by decide)
    have hGu : wv u₁.mem q.1.B (VG.Proof.Bignum.X86_64.slot (wk q.1.k) aG) (wk q.1.k) = wv t₀.mem q.1.B (VG.Proof.Bignum.X86_64.slot (wk q.1.k) aG) (wk q.1.k) := by
      rw [hf₁.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega),
        hI.frm.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega)]
    have hpow : r / 2 ^ (64 * i) / 2 ^ (64 - 0) = r / 2 ^ (64 * (VG.Proof.Rsa.X86_64.Rp.bW q.1 - q.2)) := by
      rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, hi, Nat.sub_zero, Nat.mul_succ]
    have hW' : VG.Proof.Bignum.X86_64.word s.mem q.1.B (VG.Proof.Bignum.X86_64.slot (wk q.1.k) aM + 8 * i) =
        BitVec.ofNat 64 (r / 2 ^ (64 * i) % 2 ^ 64 * 2 ^ 0 % 2 ^ 64) := by
      rw [← hW, Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt (BitVec.isLt _), BitVec.ofNat_toNat,
        BitVec.setWidth_eq]
    refine ⟨u₁, minv, N, r, t, g, r / 2 ^ (64 * i), r / 2 ^ (64 * i) % 2 ^ 64, hc₁, by rw [hGu]; exact hGlt,
      by rw [hGu]; exact hG, rfl, Frm.refl _ _ _, Keep.refl _ _, ?_, ?_, ?_, ?_⟩
    · rw [hf₁.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega)]; exact hI.ylt
    · rw [hf₁.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega), hpow]; exact hI.y
    · rw [m₁, (VG.Proof.Bignum.X86_64.writeW_outside _ q.1.B _ (d := 8 * sC3) (by simp only [sC3, sFn]; omega)).word
        (Or.inl (by simp only [sC2, sC3, sFn]; omega)) (by simp only [sC2, sFn]; omega), VG.Proof.Bignum.X86_64.word_writeW_self, hW']
    · rw [m₁, VG.Proof.Bignum.X86_64.word_writeW_self]

theorem pins_BI : Pins (fun (p : VG.Proof.Rsa.X86_64.RpP) s => VG.Proof.Rsa.X86_64.Rp.BI p 64 s) [.rdi] := fun _ _ _ h₁ h₂ r hr => by
  obtain ⟨_, _, _, _, _, _, _, _, hc₁, _, _, _, hI₁⟩ := h₁
  obtain ⟨_, _, _, _, _, _, _, _, hc₂, _, _, _, hI₂⟩ := h₂
  simp only [List.mem_singleton] at hr; subst hr
  rw [(hc₁.congr hI₁.frm (by decide) VG.Proof.Rsa.X86_64.bit_hs hI₁.keep (by decide)).ws.rdi,
    (hc₂.congr hI₂.frm (by decide) VG.Proof.Rsa.X86_64.bit_hs hI₂.keep (by decide)).ws.rdi]

/-- A word leaks the same in runs that agree on the public data. -/
theorem wordBody_ct (M : Mont) : RelCT isa (Two fun (q : VG.Proof.Rsa.X86_64.RpP × Nat) s => q.2 < VG.Proof.Rsa.X86_64.Rp.bW q.1 ∧ VG.Proof.Rsa.X86_64.Rp.WI q.1 q.2 s)
    (.seq (.block wordHead) (.seq (.loop (bitBody M.mm) .ne) (.block wordNext))) fun _ _ => True :=
  RelCT.seq VG.Proof.Rsa.X86_64.Rp.wordHead_ct (RelCT.seq (two_map (fun q => q.1) (fun _ _ h => h) (VG.Proof.Rsa.X86_64.Rp.bitLoop_ct M))
    (two_taint [.rdi] VG.Proof.Rsa.X86_64.Rp.pins_BI (by taint_decide)))

theorem wordLoop_ct (M : Mont) : RelCT isa (Two fun p s => 0 < VG.Proof.Rsa.X86_64.Rp.bW p ∧ VG.Proof.Rsa.X86_64.Rp.WI p 0 s)
    (.loop (.seq (.block wordHead) (.seq (.loop (bitBody M.mm) .ne) (.block wordNext))) .ne)
    (Two fun p s => VG.Proof.Rsa.X86_64.Rp.WI p (VG.Proof.Rsa.X86_64.Rp.bW p) s) :=
  two_loop VG.Proof.Rsa.X86_64.Rp.bW (VG.Proof.Rsa.X86_64.Rp.wordBody_ct M) fun _ _ _ hk ⟨t₀, minv, N, r, t, g, hc, hGlt, hG, hI⟩ =>
    WP.mono (VG.Proof.Rsa.X86_64.wordStep_ok M hc hGlt hG hk hI) fun _ ⟨hz, hI'⟩ =>
      ⟨eval_ne_count hk hz, fun _ => ⟨t₀, minv, N, r, t, g, hc, hGlt, hG, hI'⟩,
        fun h => h ▸ ⟨t₀, minv, N, r, t, g, hc, hGlt, hG, hI'⟩⟩

/-- `expLoop`'s hypotheses. -/
def EX (p : VG.Proof.Rsa.X86_64.RpP) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (N r t g : Nat), VG.Proof.Rsa.X86_64.Cst s p.B p.Z (wk p.k) minv N p.el r t ∧
    wv s.mem p.B (VG.Proof.Bignum.X86_64.slot (wk p.k) aG) (wk p.k) < N ∧
    wv s.mem p.B (VG.Proof.Bignum.X86_64.slot (wk p.k) aG) (wk p.k) % N = g * 2 ^ (64 * wk p.k) % N ∧
    wv s.mem p.B (VG.Proof.Bignum.X86_64.slot (wk p.k) aY) (wk p.k) = 2 ^ (64 * wk p.k) % N

/-- The exponentiation leaks the same in runs that agree on the public data. -/
theorem expLoop_ct (M : Mont) : RelCT isa (Two VG.Proof.Rsa.X86_64.Rp.EX) (VG.Impl.Rsa.X86_64.Keys.Recover.expLoop M.mm) (Two fun p s => VG.Proof.Rsa.X86_64.Rp.WI p (VG.Proof.Rsa.X86_64.Rp.bW p) s) := by
  unfold VG.Impl.Rsa.X86_64.Keys.Recover.expLoop
  refine RelCT.seq (VG.Proof.Rsa.X86_64.Rp.blk_gct RpP.B RpP.Z (fun p => wk p.k) (fun p s ⟨_, _, _, _, _, hc, _⟩ => hc.ws)
    (by taint_decide) fun p s h => ?_) (VG.Proof.Rsa.X86_64.Rp.wordLoop_ct M)
  obtain ⟨minv, N, r, t, g, hc, hGlt, hG, hY⟩ := h
  have hZ16 := hc.hZ16
  have he2 := hc.e2
  have hw1 := hc.ws.w1
  have hw2 := hc.ws.w2
  have h256 := hc.ws.h256
  have hN : 0 < N := by have := hc.n1; omega
  unfold VG.Impl.Rsa.X86_64.Keys.Recover.expInit
  refine WP.block_append_iff.mpr (WP.mono (VG.Proof.Rsa.X86_64.bw_ok hc.ws hc.hel (by omega)) fun s₁ ⟨hax, m₁, k₁⟩ => ?_)
  have hs₁ := hc.ws.scr.congr k₁.2.2
  have hdi₁ : s₁.gpr .rdi = p.B := (k₁.gpr (by decide)).trans hc.ws.rdi
  refine WP.mono (WP.keep [] (Q := fun u => u.mem = s.mem.writeW (VG.Proof.Bignum.X86_64.off p.B (8 * sC1))
      (BitVec.ofNat 64 (VG.Proof.Rsa.X86_64.Rp.bW p))) (by
    xrun [State.ea, hdr, hdi₁, hdrOff, hs₁.st (d := 8 * sC1) (by simp only [sC1, sCnt, sFn]; omega), hax, m₁])
    rfl) fun u ⟨mu, k₂⟩ => ⟨by simp only [VG.Proof.Rsa.X86_64.Rp.bW]; unfold wk at *; omega, s, minv, N, r, t, g, hc, hGlt, hG, ?_⟩
  have hf₁ : Frm p.B (VG.Proof.Rsa.X86_64.rg (wk p.k) [] [sC1]) s.mem u.mem := by
    rw [mu]; exact Frm.rg_of_hdr (VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (by simp only [sC1, sCnt, sFn]; omega)) _ _
      (List.mem_singleton_self _)
  have hr : r < 2 ^ (64 * VG.Proof.Rsa.X86_64.Rp.bW p) := hc.hm ▸ wv_lt _ _ _ _
  refine ⟨hf₁.rg_mono (by decide) (by decide), (k₁.trans k₂).mono (by decide), ?_, ?_, ?_⟩
  · rw [hf₁.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega), hY]; exact Nat.mod_lt _ hN
  · rw [hf₁.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega), hY, Nat.sub_zero,
      Nat.div_eq_of_lt hr, Nat.pow_zero, Nat.one_mul, Nat.mod_mod]
  · rw [mu, VG.Proof.Bignum.X86_64.word_writeW_self, Nat.sub_zero]

end Rp

end VG.Proof.Rsa.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rsa.X86_64.RpCT6`. -/
section

/-!
# `vg_rsa_recover_primes` on x86-64: constant time, the candidates

A candidate leaks the same in runs whose working spaces agree
(`candBody_ct`); the candidates tried are the public number of tries
(`candLoop_ct`): the loop stops after candidate `j` iff `j + 1` is that
number, which `recoverPrimes.go` fixes (`go_ge`, `go_le`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aR2 aXm aY aOne sCnt sMask)
open VG.Spec.Rsa (splitTwos recoverStep recoverPrimes recoverTries)

/-! ## The number of tries -/

theorem go_ge (n t r : Nat) : ∀ k, k ≤ recoverTries → recoverTries - k ≤ (recoverPrimes.go n t r k).2
  | 0, _ => by rw [recoverPrimes.go]; exact Nat.le_refl _
  | k + 1, hk => by
    rw [recoverPrimes.go]
    split
    · show recoverTries - (k + 1) ≤ recoverTries - k
      omega
    · have := VG.Proof.Rsa.X86_64.go_ge n t r k (by omega)
      omega

theorem go_le (n t r : Nat) : ∀ k, k ≤ recoverTries → (recoverPrimes.go n t r k).2 ≤ recoverTries
  | 0, _ => by rw [recoverPrimes.go]
  | k + 1, hk => by
    rw [recoverPrimes.go]
    split
    · show recoverTries - k ≤ recoverTries
      omega
    · exact VG.Proof.Rsa.X86_64.go_le n t r k (by omega)

/-- After candidate `j` fails, at least `j + 2` are tried. -/
theorem go_ge1 (n t r : Nat) {k : Nat} (hk : k < recoverTries) :
    recoverTries - k ≤ (recoverPrimes.go n t r (k + 1)).2 := by
  rw [recoverPrimes.go]
  split
  · exact Nat.le_refl _
  · exact VG.Proof.Rsa.X86_64.go_ge n t r k (by omega)

/-- The loop's condition after candidate `j`, from the tries. -/
theorem cand_cond (n t r : Nat) {j : Nat} (hj : j < (recoverPrimes.go n t r recoverTries).2)
    (hgo : recoverPrimes.go n t r recoverTries = recoverPrimes.go n t r (recoverTries - j)) :
    (!(!(decide (j + 1 < 100) && !(recoverStep n t r (j + 2)).isSome))) =
      decide (j + 1 < (recoverPrimes.go n t r recoverTries).2) := by
  have hle := VG.Proof.Rsa.X86_64.go_le n t r recoverTries (Nat.le_refl _)
  have hj100 : j < recoverTries := by omega
  rw [hgo, VG.Proof.Rsa.go_eq n t r hj100]
  cases hs : recoverStep n t r (j + 2) with
  | some y => simp
  | none =>
    simp only [Option.isSome_none, Bool.not_false, Bool.and_true, Bool.not_not]
    by_cases h1 : j + 1 < 100
    · obtain ⟨k, hk⟩ : ∃ k, recoverTries - (j + 1) = k + 1 := ⟨recoverTries - (j + 1) - 1, by unfold recoverTries; omega⟩
      have := VG.Proof.Rsa.X86_64.go_ge1 n t r (k := k) (by unfold recoverTries at *; omega)
      rw [hk]
      simp only [h1, decide_true]
      exact (decide_eq_true (by unfold recoverTries at *; omega)).symm
    · have e : recoverTries - (j + 1) = 0 := by unfold recoverTries; omega
      rw [e, recoverPrimes.go]
      simp only [h1, decide_false]
      exact (decide_eq_false (by unfold recoverTries; omega)).symm

namespace Rp

/-! ## A candidate -/

/-- At a candidate's start: the constants, and the candidate `c < 100`. -/
def CA (p : VG.Proof.Rsa.X86_64.RpP) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (N r t c : Nat), VG.Proof.Rsa.X86_64.Cst s p.B p.Z (wk p.k) minv N p.el r t ∧
    VG.Proof.Bignum.X86_64.word s.mem p.B (8 * sCand) = BitVec.ofNat 64 c ∧ c < 100

/-- The constants. -/
def CK (p : VG.Proof.Rsa.X86_64.RpP) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (N r t : Nat), VG.Proof.Rsa.X86_64.Cst s p.B p.Z (wk p.k) minv N p.el r t

theorem CK.ws {p : VG.Proof.Rsa.X86_64.RpP} {s : State} (h : VG.Proof.Rsa.X86_64.Rp.CK p s) : Ws s p.B p.Z (wk p.k) := by
  obtain ⟨_, _, _, _, hc⟩ := h
  exact hc.ws

/-- After `gBlk`. -/
def CG (p : VG.Proof.Rsa.X86_64.RpP) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (N r t : Nat), VG.Proof.Rsa.X86_64.Cst s p.B p.Z (wk p.k) minv N p.el r t ∧
    s.gpr .r12 = BitVec.ofNat 64 (wk p.k) ∧ s.gpr .rcx = BitVec.ofNat 64 0

/-- After `g R mod n` in `Xm` (`hg`), then copied to `G`. -/
def CX (j : Nat) (p : VG.Proof.Rsa.X86_64.RpP) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (N r t g : Nat), VG.Proof.Rsa.X86_64.Cst s p.B p.Z (wk p.k) minv N p.el r t ∧
    wv s.mem p.B (VG.Proof.Bignum.X86_64.slot (wk p.k) j) (wk p.k) < N ∧
    wv s.mem p.B (VG.Proof.Bignum.X86_64.slot (wk p.k) j) (wk p.k) % N = g * 2 ^ (64 * wk p.k) % N

/-- `setWord`'s registers after its load. -/
def swXVal (p : VG.Proof.Rsa.X86_64.RpP) : Reg → BitVec 64
  | .r8 => VG.Proof.Bignum.X86_64.off p.B (VG.Proof.Bignum.X86_64.slot (wk p.k) aX)
  | .r12 => BitVec.ofNat 64 (wk p.k)
  | .rcx => BitVec.ofNat 64 0
  | _ => 0

theorem setX_ct : RelCT isa (Two VG.Proof.Rsa.X86_64.Rp.CG) (setWord aX .rcx) (Two VG.Proof.Rsa.X86_64.Rp.CK) := by
  rw [setWord_eq]
  refine pin_ct [.rdi, .r12, .rcx] [.r8, .r12, .rcx] VG.Proof.Rsa.X86_64.Rp.swXVal (fun _ _ _ h₁ h₂ r hr => ?_) (by taint_decide)
    (fun p s h => ?_) (by taint_decide) fun p s h => ?_
  · obtain ⟨_, _, _, _, hc₁, a₁, b₁⟩ := h₁
    obtain ⟨_, _, _, _, hc₂, a₂, b₂⟩ := h₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [hc₁.ws.rdi, hc₂.ws.rdi]
    · rw [a₁, a₂]
    · rw [b₁, b₂]
  · obtain ⟨_, _, _, _, hc, h12, hcx⟩ := h
    have hw := hc.ws
    have := hw.h256
    have hl : InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off p.B (8 * sArr aX)) 8 :=
      hw.scr.ld (by have := hw.hZ; have := hdr_lt_slot (wk p.k) 16 (show sArr aX < 32 by decide); omega)
    refine WP.mono (WP.keep [.r8] (Q := fun t => t.gpr .r8 = VG.Proof.Bignum.X86_64.off p.B (VG.Proof.Bignum.X86_64.slot (wk p.k) aX)) (by
      xrun [State.ea, hdr, hw.rdi, hdrOff, hl, hw.harr aX (by decide)]) rfl) fun t ⟨h8, k⟩ r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h8
    · exact (k.gpr (by decide)).trans h12
    · exact (k.gpr (by decide)).trans hcx
  · rw [← setWord_eq]
    obtain ⟨minv, N, r, t, hc, h12, hcx⟩ := h
    have hw1 := hc.ws.w1
    have hw2 := hc.ws.w2
    have hg := hc.good
    refine WP.mono (setWord_ok hc.ws.scr hc.ws.rdi hg.1.hdr hg.2 h12 (by omega) (by omega) (o := aX) (by decide)
      (ri := .rcx) (by decide) (i := 0) (by omega) hcx) fun u ⟨_, o, k⟩ => ?_
    exact ⟨minv, N, r, t, hc.congr (Frm.rg_of_out o (Nat.le_refl _) [aX] [] (by decide)) (by decide) (by simp) k
      (by decide)⟩

/-- `g`, `g R mod n`, its copy and `Y = R mod n`, and the exponentiation. -/
theorem candA_ct (M : Mont) : RelCT isa (Two VG.Proof.Rsa.X86_64.Rp.CA)
    (seqs [.block gBlk, setWord aX .rcx, M.mm aXm aX aR2, copyA aG aXm, copyA aY aO, VG.Impl.Rsa.X86_64.Keys.Recover.expLoop M.mm])
    fun _ _ => True := by
  have hK : ∀ p s, VG.Proof.Rsa.X86_64.Rp.CK p s → Ws s p.B p.Z (wk p.k) := fun _ _ h => h.ws
  have hX : ∀ j p s, VG.Proof.Rsa.X86_64.Rp.CX j p s → Ws s p.B p.Z (wk p.k) := fun _ _ _ ⟨_, _, _, _, _, hc, _⟩ => hc.ws
  simp only [seqs]
  refine RelCT.seq (R := Two VG.Proof.Rsa.X86_64.Rp.CG) (VG.Proof.Rsa.X86_64.Rp.blk_gct RpP.B RpP.Z (fun p => wk p.k)
    (fun _ _ ⟨_, _, _, _, _, hc, _⟩ => hc.ws) (by taint_decide) fun p s h => ?_) ?_
  · obtain ⟨minv, N, r, t, c, hc, hcand, -⟩ := h
    exact WP.mono (VG.Proof.Rsa.X86_64.gBlk_ok hc.ws hcand) fun u ⟨_, hcx, h12, m, k⟩ =>
      ⟨minv, N, r, t, hc.congr (js := []) (hs := []) (by rw [m]; exact Frm.refl _ _ _) (by simp) (by simp) k
        (by decide), h12, hcx⟩
  refine RelCT.seq VG.Proof.Rsa.X86_64.Rp.setX_ct (RelCT.seq (R := Two (VG.Proof.Rsa.X86_64.Rp.CX aXm)) (VG.Proof.Rsa.X86_64.Rp.mm_gct RpP.B RpP.Z (fun p => wk p.k) hK M
    (o := aXm) (a := aX) (b := aR2) (by unfold MmUse; decide) fun p s h => ?_) ?_)
  · obtain ⟨minv, N, r, t, hc⟩ := h
    have hg := hc.good
    have hw2 := hc.ws.w2
    refine WP.mono (M.mm_ok hg.1 hg.2 hc.ws.w1 (by omega) (o := aXm) (a := aX) (b := aR2) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.hinv
      (by rw [hc.hn]; exact hc.hr2lt)) fun u ⟨_, hlt, hm, ha, k⟩ => ?_
    rw [hc.hn] at hlt hm
    exact ⟨minv, N, r, t, _, hc.congr (Frm.rg_of_arrays ha [aXm, aAcc, aTmp] [] (by decide)) (by decide) (by simp)
      k (by decide), hlt, VG.Proof.Rsa.X86_64.g_mont hc.coprime hc.hr2 hm⟩
  refine RelCT.seq (R := Two (VG.Proof.Rsa.X86_64.Rp.CX aG)) (VG.Proof.Rsa.X86_64.Rp.copyA_gct RpP.B RpP.Z (fun p => wk p.k) (hX aXm) (by taint_decide)
    fun p s h => ?_) (RelCT.seq (R := Two VG.Proof.Rsa.X86_64.Rp.EX) (VG.Proof.Rsa.X86_64.Rp.copyA_gct RpP.B RpP.Z (fun p => wk p.k) (hX aG) (by taint_decide)
      fun p s h => ?_) ((VG.Proof.Rsa.X86_64.Rp.expLoop_ct M).mono (fun _ _ h => h) fun _ _ _ => trivial))
  · obtain ⟨minv, N, r, t, g, hc, hlt, hm⟩ := h
    have hZ16 := hc.hZ16
    refine WP.mono (copyA_ok hc.ws (o := aG) (a := aXm) (by decide) (by decide) (by decide)) fun u ⟨hv, o, k⟩ => ?_
    have hf : Frm p.B (VG.Proof.Rsa.X86_64.rg (wk p.k) [aG] []) s.mem u.mem := Frm.rg_of_out o (by omega) _ _ (by decide)
    exact ⟨minv, N, r, t, g, hc.congr hf (by decide) (by simp) k (by decide), by rw [hv]; exact hlt,
      by rw [hv]; exact hm⟩
  · obtain ⟨minv, N, r, t, g, hc, hlt, hm⟩ := h
    have hZ16 := hc.hZ16
    refine WP.mono (copyA_ok hc.ws (o := aY) (a := aO) (by decide) (by decide) (by decide)) fun u ⟨hv, o, k⟩ => ?_
    have hf : Frm p.B (VG.Proof.Rsa.X86_64.rg (wk p.k) [aY] []) s.mem u.mem := Frm.rg_of_out o (by omega) _ _ (by decide)
    have hG : wv u.mem p.B (VG.Proof.Bignum.X86_64.slot (wk p.k) aG) (wk p.k) = wv s.mem p.B (VG.Proof.Bignum.X86_64.slot (wk p.k) aG) (wk p.k) :=
      hf.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega)
    exact ⟨minv, N, r, t, g, hc.congr hf (by decide) (by simp) k (by decide), by rw [hG]; exact hlt,
      by rw [hG]; exact hm, by rw [hv, hc.ho]⟩

/-- The checks of `y = ±1` and the start of the squarings. -/
theorem candB_ct : RelCT isa (Two VG.Proof.Rsa.X86_64.Rp.CK) (seqs (eqA aY aO ++ (([.block (eqStore sC2)] : List (Prog isa)) ++ (eqA aY aNg ++
    ([.block chkBlk] : List (Prog isa)))))) fun _ _ => True := by
  have hK : ∀ p s, VG.Proof.Rsa.X86_64.Rp.CK p s → Ws s p.B p.Z (wk p.k) := fun _ _ h => h.ws
  have same : ∀ p s u, VG.Proof.Rsa.X86_64.Rp.CK p s → u.mem = s.mem → ∀ {regs : List Reg}, VG.Proof.MlKem.X86_64.Keep regs s u → .rdi ∉ regs → VG.Proof.Rsa.X86_64.Rp.CK p u :=
    fun p s u ⟨minv, N, r, t, hc⟩ m _ k hr => ⟨minv, N, r, t, hc.congr (js := []) (hs := [])
      (by rw [m]; exact Frm.refl _ _ _) (by simp) (by simp) k hr⟩
  refine RelCT.seqs_append (by simp [eqA]) (by simp) (RelCT.seq (R := Two VG.Proof.Rsa.X86_64.Rp.CK) (VG.Proof.Rsa.X86_64.Rp.eqA_gct RpP.B RpP.Z
    (fun p => wk p.k) hK (by taint_decide) fun p s h => WP.mono (eqA_ok h.ws (a := aY) (b := aO) (by decide)
      (by decide)) fun u ⟨_, m, k⟩ => same p s u h m k (by decide)) ?_)
  refine RelCT.seqs_append (by simp) (by simp [eqA]) (RelCT.seq (R := Two VG.Proof.Rsa.X86_64.Rp.CK) ?_ ?_)
  · simp only [seqs]
    refine VG.Proof.Rsa.X86_64.Rp.blk_gct RpP.B RpP.Z (fun p => wk p.k) hK (by taint_decide) fun p s h => ?_
    obtain ⟨minv, N, r, t, hc⟩ := h
    have h256 := hc.ws.h256
    exact WP.mono (VG.Proof.Rsa.X86_64.eqStore_ok hc.ws (i := sC2) (by decide) (by decide)) fun u ⟨m, k⟩ =>
      ⟨minv, N, r, t, hc.congr (js := []) (Frm.rg_of_hdr (m ▸ VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (by simp only [sC2, sFn]; omega))
        [] [sC2] (List.mem_singleton_self _)) (by decide) (by decide) k (by decide)⟩
  refine RelCT.seqs_append (by simp [eqA]) (by simp) (RelCT.seq (R := Two VG.Proof.Rsa.X86_64.Rp.CK) (VG.Proof.Rsa.X86_64.Rp.eqA_gct RpP.B RpP.Z
    (fun p => wk p.k) hK (by taint_decide) fun p s h => WP.mono (eqA_ok h.ws (a := aY) (b := aNg) (by decide)
      (by decide)) fun u ⟨_, m, k⟩ => same p s u h m k (by decide)) ?_)
  simp only [seqs]
  exact two_taint [.rdi] (fun _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.ws.rdi, h₂.ws.rdi]) (by taint_decide)

/-- After the start of the squarings. -/
theorem candBody_ct (M : Mont) : RelCT isa (Two VG.Proof.Rsa.X86_64.Rp.CA) (candBody M.mm) fun _ _ => True := by
  rw [show candBody M.mm = seqs ([.block gBlk, setWord aX .rcx, M.mm aXm aX aR2, copyA aG aXm, copyA aY aO,
      VG.Impl.Rsa.X86_64.Keys.Recover.expLoop M.mm] ++ ((eqA aY aO ++ ([.block (eqStore sC2)] ++ (eqA aY aNg ++ [.block chkBlk]))) ++
        [.loop (sqBody M.mm) .ne, .block candNext])) by
    simp only [candBody, List.append_assoc, List.cons_append, List.nil_append]]
  refine RelCT.seqs_append (by simp) (by simp [eqA]) (RelCT.seq (R := Two fun p s => ∃ (minv : BitVec 64)
      (N r t y : Nat), VG.Proof.Rsa.X86_64.Cst s p.B p.Z (wk p.k) minv N p.el r t ∧
        wv s.mem p.B (VG.Proof.Bignum.X86_64.slot (wk p.k) aY) (wk p.k) = y * 2 ^ (64 * wk p.k) % N ∧ y < N)
    (two_post (VG.Proof.Rsa.X86_64.Rp.candA_ct M) fun p s ⟨minv, N, r, t, c, hc, hcand, hc100⟩ => ?_) ?_)
  · have hN : 0 < N := by have := hc.n1; omega
    exact WP.mono (VG.Proof.Rsa.X86_64.candA_ok M hc hcand hc100) fun u ⟨hf, k, hY⟩ =>
      ⟨minv, N, r, t, _, hc.congr hf (by decide) (by decide) k (by decide), hY,
        by rw [VG.Proof.Bignum.powMod_eq]; exact Nat.mod_lt _ hN⟩
  refine RelCT.seqs_append (by simp [eqA]) (by simp) (RelCT.seq (R := Two fun p s =>
      0 < 64 * (wk p.k + (p.el + 7) / 8) ∧ VG.Proof.Rsa.X86_64.Rp.SQI p 0 s)
    (two_post (two_map id (fun _ _ ⟨minv, N, r, t, _, hc, _⟩ => ⟨minv, N, r, t, hc⟩) VG.Proof.Rsa.X86_64.Rp.candB_ct)
      fun p s h => ?_) ?_)
  · obtain ⟨minv, N, r, t, y, hc, hY, hy⟩ := h
    have hZ16 := hc.hZ16
    have hw1 := hc.ws.w1
    refine WP.mono (VG.Proof.Rsa.X86_64.candB_ok hc hY hy) fun u ⟨hf, k, hc2, hc3, hc1⟩ => ⟨by omega, ?_⟩
    have hc₂ := hc.congr hf (by decide) (by decide) k (by decide)
    refine ⟨u, minv, N, r, t, VG.Proof.Rsa.sqStart N y, hc₂, Frm.refl _ _ _, Keep.refl _ _, ?_, hy, hc1, hc2, hc3⟩
    rw [hf.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega)]; exact hY
  show RelCT isa _ (.seq (.loop (sqBody M.mm) .ne) (.block candNext)) _
  exact RelCT.seq (VG.Proof.Rsa.X86_64.Rp.sqLoop_ct M) (two_taint [.rdi] (fun _ _ _ ⟨_, _, _, _, _, _, hc₁, hI₁⟩ ⟨_, _, _, _, _, _, hc₂, hI₂⟩
    r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [(hc₁.congr hI₁.frm (by decide) VG.Proof.Rsa.X86_64.sq_hs hI₁.keep (by decide)).ws.rdi,
        (hc₂.congr hI₂.frm (by decide) VG.Proof.Rsa.X86_64.sq_hs hI₂.keep (by decide)).ws.rdi]) (by taint_decide))

/-! ## The candidates -/

/-- The candidates' invariant: `j` tried from `s₀`, and the public count. -/
def CL (p : VG.Proof.Rsa.X86_64.RpP) (j : Nat) (u : State) : Prop :=
  ∃ (s₀ : State) (minv : BitVec 64) (N r t : Nat), VG.Proof.Rsa.X86_64.Cst s₀ p.B p.Z (wk p.k) minv N p.el r t ∧
    p.cnt = (recoverPrimes.go N t r recoverTries).2 ∧ VG.Proof.Rsa.X86_64.CandI s₀ p.B (wk p.k) N t r j u

theorem candLoopL_ct (M : Mont) : RelCT isa (Two fun p s => 0 < p.cnt ∧ VG.Proof.Rsa.X86_64.Rp.CL p 0 s) (.loop (candBody M.mm) .ne)
    (Two fun (_ : VG.Proof.Rsa.X86_64.RpP) (_ : State) => True) :=
  two_loop RpP.cnt (two_map (fun q => q.1) (fun q s hq => by
      obtain ⟨hj, s₀, minv, N, r, t, hc, hcnt, hI⟩ := hq
      have := VG.Proof.Rsa.X86_64.go_le N t r recoverTries (Nat.le_refl _)
      exact ⟨minv, N, r, t, q.2, hc.congr hI.frm (by decide) VG.Proof.Rsa.X86_64.cand_hs hI.keep (by decide), hI.cand,
        by have : recoverTries = 100 := rfl; omega⟩) (VG.Proof.Rsa.X86_64.Rp.candBody_ct M))
    fun p j s hj ⟨s₀, minv, N, r, t, hc, hcnt, hI⟩ => by
      have hle := VG.Proof.Rsa.X86_64.go_le N t r recoverTries (Nat.le_refl _)
      have hj100 : j < 100 := by have : recoverTries = 100 := rfl; omega
      have hcu := hc.congr hI.frm (by decide) VG.Proof.Rsa.X86_64.cand_hs hI.keep (by decide)
      refine WP.mono (VG.Proof.Rsa.X86_64.candBody_ok M hcu hI.cand hj100) fun u' ⟨hz, hf, k, hcand, _, _⟩ => ⟨?_, fun hlt => ?_,
        fun _ => trivial⟩
      · rw [hcnt] at hj ⊢
        simp only [VG.X86_64.eval, hz, Option.map_some]
        exact congrArg some (VG.Proof.Rsa.X86_64.cand_cond N t r hj hI.go)
      · refine ⟨s₀, minv, N, r, t, hc, hcnt, (hI.frm.rg_trans hf).rg_mono (by decide) (by decide),
          (hI.keep.trans k).mono (by decide), hcand, ?_⟩
        rw [hI.go, VG.Proof.Rsa.go_eq N t r hj100]
        rw [hcnt, hI.go, VG.Proof.Rsa.go_eq N t r hj100] at hlt
        cases hs : recoverStep N t r (j + 2) with
        | some y => rw [hs] at hlt; exact absurd hlt (by simp)
        | none => rfl

/-- The public count is `recoverPrimes.go`'s, once `d e` passes step 1. -/
theorem cnt_eq {I : VG.Proof.Rsa.X86_64.RpIn} (hv : Spec.Rsa.modulusValid I.N I.k = true) (L : VG.Proof.Rsa.X86_64.RpLens I) (hm0 : 0 < I.D * I.E - 1)
    (heven : (I.D * I.E - 1) % 2 = 0) :
    I.pub.cnt = (recoverPrimes.go I.N (splitTwos (I.D * I.E - 1)).1 (splitTwos (I.D * I.E - 1)).2
      recoverTries).2 := by
  have h1 : ¬(I.D * I.E < 2 ∨ (I.D * I.E - 1) % 2 = 1) := by omega
  show (Spec.Rsa.primesKey I.nb I.eb I.db).2 = _
  simp only [Spec.Rsa.primesKey, L.nbl, hv, ite_true]
  rw [← VG.Proof.Rsa.recoverPrimes_go h1]
  split <;> simp_all

/-- After the candidates: `recoverPrimes.go`'s result, and what the factors
need. -/
def GR3 (p : VG.Proof.Rsa.X86_64.RpP) (s : State) : Prop :=
  ∃ (I : VG.Proof.Rsa.X86_64.RpIn) (m₀ : Mem) (minv : BitVec 64) (res : Option Nat) (cnt : Nat), I.pub = p ∧ VG.Proof.Rsa.X86_64.RpS I m₀ s ∧
    VG.Proof.Rsa.X86_64.RpLens I ∧ VG.Proof.Rsa.X86_64.RpOuts I ∧ Spec.Rsa.modulusValid I.N I.k = true ∧
    VG.Proof.Rsa.X86_64.Cst s I.B I.Z (wk I.k) minv I.N I.el (splitTwos (I.D * I.E - 1)).2 (splitTwos (I.D * I.E - 1)).1 ∧
    recoverPrimes.go I.N (splitTwos (I.D * I.E - 1)).1 (splitTwos (I.D * I.E - 1)).2 recoverTries =
      (res.map (VG.Proof.Rsa.X86_64.pqOf I.N), cnt) ∧ VG.Proof.Bignum.X86_64.word s.mem I.B (8 * sC3) = VG.Proof.Bignum.X86_64.mask res.isSome ∧
    (∀ y, res = some y → wv s.mem I.B (VG.Proof.Bignum.X86_64.slot (wk I.k) aY) (wk I.k) = y * 2 ^ (64 * wk I.k) % I.N ∧ y < I.N ∧
      y * y % I.N = 1)

theorem candLoop_ct (M : Mont) : RelCT isa (Two VG.Proof.Rsa.X86_64.Rp.GR2) (candLoop M.mm) (Two VG.Proof.Rsa.X86_64.Rp.GR3) := by
  refine two_post (RelCT.seq (VG.Proof.Rsa.X86_64.Rp.blk_gct RpP.B RpP.Z (fun p => wk p.k)
    (fun _ _ ⟨_, _, e, S, _⟩ => e ▸ S.ws) (by taint_decide) fun p s h => ?_) ((VG.Proof.Rsa.X86_64.Rp.candLoopL_ct M).mono (fun _ _ h => h) fun _ _ _ => trivial)) fun p s h => ?_
  · obtain ⟨I, m₀, rfl, S, L, O, hv, hc, hm0, heven⟩ := h
    dsimp only [RpIn.pub]
    have h256 := hc.ws.h256
    refine WP.mono (WP.keep [.rax] (Q := fun u => u.mem = s.mem.writeW (VG.Proof.Bignum.X86_64.off I.B (8 * sCand))
        (BitVec.ofNat 64 0)) (by
      xrun [State.ea, hdr, hc.ws.rdi, hdrOff,
        hc.ws.scr.st (d := 8 * sCand) (by simp only [sCand, Impl.Bignum.X86_64.Public.sV, sFn]; omega)]
      rfl) rfl) fun u ⟨m₁, k₁⟩ => ⟨?_, s, _, I.N, _, _, hc, VG.Proof.Rsa.X86_64.Rp.cnt_eq hv L hm0 heven, ?_, k₁.mono (by decide),
        by rw [m₁, VG.Proof.Bignum.X86_64.word_writeW_self], rfl⟩
    · rw [show (Spec.Rsa.primesKey I.nb I.eb I.db).2 = I.pub.cnt from rfl, VG.Proof.Rsa.X86_64.Rp.cnt_eq hv L hm0 heven]
      exact VG.Proof.Rsa.go_pos _ _ _ _ (Nat.le_refl _)
    · rw [m₁]; exact Frm.rg_of_hdr (VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (by simp only [sCand, Impl.Bignum.X86_64.Public.sV, sFn]; omega))
        _ _ (by decide)
  · obtain ⟨I, m₀, rfl, S, L, O, hv, hc, hm0, heven⟩ := h
    exact WP.mono (VG.Proof.Rsa.X86_64.candLoop_ok M hc) fun u ⟨res, cnt, hgo, _, hc3, hy, hf, k⟩ =>
      ⟨I, m₀, _, res, cnt, rfl, S.step hf (by decide) (by decide) k (by decide), L, O, hv,
        hc.congr hf (by decide) VG.Proof.Rsa.X86_64.cand_hs k (by decide), hgo, hc3, hy⟩

end Rp

end VG.Proof.Rsa.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rsa.X86_64.RpCT7`. -/
section

/-!
# `vg_rsa_recover_primes` on x86-64: constant time, the factors

`y - 1`, `p = gcd(y - 1, n)`, `q = n / p`, the larger first, and the
masked stores (`fin_ct`): every loop counts a public number of words, and
the stores' pointers and lengths are pinned by correctness.
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aR2 aXm aY aOne sCnt sMask)

namespace Rp

/-- Between the pieces of `fin`: the inputs, the mask, and `X`. -/
def FX (X : VG.Proof.Rsa.X86_64.RpIn → State → Prop) (p : VG.Proof.Rsa.X86_64.RpP) (s : State) : Prop :=
  ∃ (I : VG.Proof.Rsa.X86_64.RpIn) (m₀ : Mem) (c : Bool), I.pub = p ∧ VG.Proof.Rsa.X86_64.RpS I m₀ s ∧ VG.Proof.Rsa.X86_64.RpLens I ∧ VG.Proof.Rsa.X86_64.RpOuts I ∧
    VG.Proof.Bignum.X86_64.word s.mem I.B (8 * sMask) = VG.Proof.Bignum.X86_64.mask c ∧ X I s

theorem FX.ws {X : VG.Proof.Rsa.X86_64.RpIn → State → Prop} {p : VG.Proof.Rsa.X86_64.RpP} {s : State} (h : VG.Proof.Rsa.X86_64.Rp.FX X p s) : Ws s p.B p.Z (wk p.k) := by
  obtain ⟨I, m₀, c, rfl, S, -⟩ := h
  exact S.ws

/-- `FX` after a piece that changes only arrays and slots of `rSlot` other
than `sMask`. -/
theorem FX.step {X Y : VG.Proof.Rsa.X86_64.RpIn → State → Prop} {p : VG.Proof.Rsa.X86_64.RpP} {s t : State} (h : VG.Proof.Rsa.X86_64.Rp.FX X p s) {js hs : List Nat}
    (hf : Frm p.B (VG.Proof.Rsa.X86_64.rg (wk p.k) js hs) s.mem t.mem) (hjs : ∀ j ∈ js, j < 16) (hhs : ∀ i ∈ hs, rSlot i = true)
    (hm : sMask ∉ hs) {regs : List Reg} (k : VG.Proof.MlKem.X86_64.Keep regs s t) (hr : .rdi ∉ regs ∧ .rsp ∉ regs)
    (hX : ∀ I : VG.Proof.Rsa.X86_64.RpIn, I.pub = p → X I s → Y I t) : VG.Proof.Rsa.X86_64.Rp.FX Y p t := by
  obtain ⟨I, m₀, c, e, S, L, O, hmk, hx⟩ := h
  subst e
  dsimp only [RpIn.pub] at hf
  exact ⟨I, m₀, c, rfl, S.step hf hjs hhs k hr, L, O, by rw [hf.rg_word (by decide) hm]; exact hmk, hX I rfl hx⟩

theorem pins_FM {X : VG.Proof.Rsa.X86_64.RpIn → State → Prop} : Pins (VG.Proof.Rsa.X86_64.Rp.FX X) [.rdi] := fun _ _ _ h₁ h₂ r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [h₁.ws.rdi, h₂.ws.rdi]

theorem zeroA_gct {α : Type} {Φ Ψ : α → State → Prop} (B : α → Addr) (Z w : α → Nat)
    (hws : ∀ a s, Φ a s → Ws s (B a) (Z a) (w a)) {j : Nat} {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base j .r8)) zeroAccLoop) hc).isSome = true)
    (hw : ∀ x s, Φ x s → WP isa (zeroA j) s (Ψ x)) : RelCT isa (Two Φ) (zeroA j) (Two Ψ) :=
  ws_ct B Z w hws ht hw

/-! ## `y - 1` -/

/-- With the constants. -/
def XC (I : VG.Proof.Rsa.X86_64.RpIn) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (r t : Nat), VG.Proof.Rsa.X86_64.Cst s I.B I.Z (wk I.k) minv I.N I.el r t

/-- `u` zero. -/
def XU (I : VG.Proof.Rsa.X86_64.RpIn) (s : State) : Prop := wv s.mem I.B (VG.Proof.Bignum.X86_64.slot (wk I.k) fU) (wk I.k + 2) = 0

/-- `u`'s top word zero. -/
def XT (I : VG.Proof.Rsa.X86_64.RpIn) (s : State) : Prop := VG.Proof.Bignum.X86_64.word s.mem I.B (VG.Proof.Bignum.X86_64.slot (wk I.k) fU + 8 * wk I.k) = 0

theorem finA_ct (M : Mont) : RelCT isa (Two VG.Proof.Rsa.X86_64.Rp.GR3) (seqs [.block [.mov .rax (.mem (hdr sC3)), .store (hdr sMask) .rax],
    M.mm aY aY aOne, zeroA fU, .block (VG.Impl.Rsa.X86_64.Keys.ws ++ base aY .r8 ++ base aOne .r10 ++ base fU .rsi ++ ([.mov32 .rbp (.imm 0)] : List Instr)),
    wordLoop 0 subBody]) (Two (VG.Proof.Rsa.X86_64.Rp.FX VG.Proof.Rsa.X86_64.Rp.XT)) := by
  simp only [seqs]
  refine RelCT.seq (R := Two (VG.Proof.Rsa.X86_64.Rp.FX VG.Proof.Rsa.X86_64.Rp.XC)) (VG.Proof.Rsa.X86_64.Rp.blk_gct RpP.B RpP.Z (fun p => wk p.k)
    (fun _ _ ⟨_, _, _, _, _, e, S, _⟩ => e ▸ S.ws) (by taint_decide) fun p s h => ?_) ?_
  · obtain ⟨I, m₀, minv, res, cnt, rfl, S, L, O, hv, hc, hgo, hc3, hy⟩ := h
    dsimp only [RpIn.pub]
    have h256 := hc.ws.h256
    refine WP.mono (WP.keep [.rax] (Q := fun u => u.mem = s.mem.writeW (VG.Proof.Bignum.X86_64.off I.B (8 * sMask))
        (VG.Proof.Bignum.X86_64.mask res.isSome)) (by
      xrun [State.ea, hdr, hc.ws.rdi, hdrOff, hc.ws.scr.ld (d := 8 * sC3) (by simp only [sC3, sFn]; omega),
        hc.ws.scr.st (d := 8 * sMask) (by simp only [sMask, sFn]; omega), hc3]) rfl) fun u ⟨m₁, k₁⟩ => ?_
    have hf₁ : Frm I.B (VG.Proof.Rsa.X86_64.rg (wk I.k) [] [sMask]) s.mem u.mem := by
      rw [m₁]; exact Frm.rg_of_hdr (VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (by simp only [sMask, sFn]; omega)) _ _
        (List.mem_singleton_self _)
    exact ⟨I, m₀, res.isSome, rfl, S.step hf₁ (by decide) (by decide) k₁ (by decide), L, O,
      by rw [m₁, VG.Proof.Bignum.X86_64.word_writeW_self], minv, _, _, hc.congr hf₁ (by decide) (by decide) k₁ (by decide)⟩
  refine RelCT.seq (R := Two (VG.Proof.Rsa.X86_64.Rp.FX fun _ _ => True)) (VG.Proof.Rsa.X86_64.Rp.mm_gct RpP.B RpP.Z (fun p => wk p.k) (fun _ _ h => h.ws) M
    (o := aY) (a := aY) (b := aOne) (by unfold MmUse; decide) fun p s h => ?_) ?_
  · have h' := h
    obtain ⟨I, m₀, c, rfl, S, L, O, hmk, minv, r, t, hc⟩ := h'
    have hg := hc.good
    have hw2 := hc.ws.w2
    exact WP.mono (M.mm_ok hg.1 hg.2 hc.ws.w1 (by omega) (o := aY) (a := aY) (b := aOne) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.hinv
      (by rw [hc.hone, hc.hn]; have := hc.n1; omega)) fun u ⟨_, _, _, ha, k⟩ =>
      h.step (Frm.rg_of_arrays ha [aAcc, aTmp, aY] [] (by decide)) (by decide) (by simp) (by simp) k (by decide)
        fun _ _ _ => trivial
  refine RelCT.seq (R := Two (VG.Proof.Rsa.X86_64.Rp.FX VG.Proof.Rsa.X86_64.Rp.XU)) (VG.Proof.Rsa.X86_64.Rp.zeroA_gct RpP.B RpP.Z (fun p => wk p.k) (fun _ _ h => h.ws)
    (by taint_decide) fun p s h => WP.mono (zeroA_ok h.ws (j := fU) (by decide)) fun u ⟨z, o, k⟩ =>
      h.step (Frm.rg_of_out o (Nat.le_refl _) [fU] [] (by decide)) (by decide) (by simp) (by simp) k (by decide)
        fun I e _ => by subst e; exact z) ?_
  have e : (.seq (.block (VG.Impl.Rsa.X86_64.Keys.ws ++ base aY .r8 ++ base aOne .r10 ++ base fU .rsi ++ [.mov32 .rbp (.imm 0)]))
      (wordLoop 0 subBody) : Prog isa) = .seq (.block (VG.Impl.Rsa.X86_64.Keys.ws ++ (base aY .r8 ++ (base aOne .r10 ++
        (base fU .rsi ++ ([.mov32 .rbp (.imm 0)] : List Instr)))))) (wordLoop 0 subBody) := by
    simp only [List.append_assoc]
  rw [e]
  refine ws_ct RpP.B RpP.Z (fun p => wk p.k) (fun _ _ h => h.ws) (by taint_decide) fun p s h => ?_
  rw [← e]
  have hw := h.ws
  have hn0 := hw.scr.nowrap
  have hZ := hw.hZ
  have hw1 := hw.w1
  have hw2 := hw.w2
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86_64.subSet_ok hw aY aOne fU) fun t ⟨h12, h8, h10, hsi, hbp, m₄, k₄⟩ => ?_)
  have sY := hw.sl (j := aY) (by decide)
  have sO := hw.sl (j := aOne) (by decide)
  have sU := hw.sl (j := fU) (by decide)
  refine WP.mono (VG.Proof.Rsa.X86_64.sub_ok (hw.scr.congr k₄.2.2) h8 h10 hsi h12 hbp (by omega) (by omega) (by omega) (by omega)
    (by omega) (by have := slot_far (w := wk p.k) (show fU ≠ aY by decide); omega)
    (by have := slot_far (w := wk p.k) (show fU ≠ aOne by decide); omega)) fun u ⟨_, _, _, o₅, k₅⟩ => ?_
  rw [m₄] at o₅
  have hf : Frm p.B (VG.Proof.Rsa.X86_64.rg (wk p.k) [fU] []) s.mem u.mem := Frm.rg_of_out o₅ (by omega) _ _ (by decide)
  refine h.step hf (by decide) (by simp) (by simp) (k₄.trans k₅) (by decide) fun I e z => ?_
  subst e
  dsimp only [RpIn.pub] at *
  show VG.Proof.Bignum.X86_64.word u.mem I.B (VG.Proof.Bignum.X86_64.slot (wk I.k) fU + 8 * wk I.k) = 0
  rw [o₅.word (Or.inr (by omega)) (by omega)]
  exact VG.Proof.Rsa.X86_64.word_above_zero (n := wk I.k) (L := wk I.k + 2) (by omega) (by rw [z]; exact Nat.two_pow_pos _)

/-! ## `p = gcd(u, n)` and `q = n / p` -/

/-- `v = n`. -/
def XV (I : VG.Proof.Rsa.X86_64.RpIn) (s : State) : Prop :=
  VG.Proof.Rsa.X86_64.Rp.XT I s ∧ wv s.mem I.B (VG.Proof.Bignum.X86_64.slot (wk I.k) fV) (wk I.k) = wv s.mem I.B (VG.Proof.Bignum.X86_64.slot (wk I.k) aN) (wk I.k)

/-- `x₁ = 0` (`o`) or `x₁ = 1`, and `x₂ = 0` if `z`. -/
def XW (o z : Bool) (I : VG.Proof.Rsa.X86_64.RpIn) (s : State) : Prop :=
  VG.Proof.Rsa.X86_64.Rp.XV I s ∧ (o = false → wv s.mem I.B (VG.Proof.Bignum.X86_64.slot (wk I.k) fX₁) (wk I.k + 2) = 0) ∧
    (o = true → wv s.mem I.B (VG.Proof.Bignum.X86_64.slot (wk I.k) fX₁) (wk I.k) = 1) ∧
    (z = true → wv s.mem I.B (VG.Proof.Bignum.X86_64.slot (wk I.k) fX₂) (wk I.k + 2) = 0)

/-- The facts after a piece that writes only array `j`. -/
theorem xv_keep {I : VG.Proof.Rsa.X86_64.RpIn} {s t : State} (hZ16 : VG.Proof.Bignum.X86_64.slot (wk I.k) 16 ≤ 2 ^ 64) {js : List Nat}
    (hf : Frm I.B (VG.Proof.Rsa.X86_64.rg (wk I.k) js []) s.mem t.mem) (hU : fU ∉ js) (hV : fV ∉ js) (hN : aN ∉ js)
    (h : VG.Proof.Rsa.X86_64.Rp.XV I s) : VG.Proof.Rsa.X86_64.Rp.XV I t := by
  obtain ⟨ht, hv⟩ := h
  refine ⟨?_, ?_⟩
  · show VG.Proof.Bignum.X86_64.word t.mem I.B (VG.Proof.Bignum.X86_64.slot (wk I.k) fU + 8 * wk I.k) = 0
    rw [hf.rg_wordA hZ16 (by simp) (by decide) hU (by omega)]; exact ht
  · rw [hf.rg_wv hZ16 (by simp) (by decide) hV (by omega), hf.rg_wv hZ16 (by simp) (by decide) hN (by omega)]
    exact hv

theorem inverse_gct {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (([.mov .r11 (.reg .r12)] : List Instr) ++
      (List.replicate 7 (.alu .add .r11 (.reg .r11)) ++ ([.mov32 .r13 (.imm 0)] : List Instr))))
      (.loop (VG.Impl.Rsa.X86_64.Keys.invStep fU fV fX₁ fX₂ aN fT) .ne)) hc).isSome = true) :
    RelCT isa (Two (VG.Proof.Rsa.X86_64.Rp.FX (VG.Proof.Rsa.X86_64.Rp.XW true true))) (inverse fU fV fX₁ fX₂ aN fT) (Two (VG.Proof.Rsa.X86_64.Rp.FX fun _ _ => True)) := by
  have e : inverse fU fV fX₁ fX₂ aN fT = .seq (.block (VG.Impl.Rsa.X86_64.Keys.ws ++ ([.mov .r11 (.reg .r12)] ++
      (List.replicate 7 (.alu .add .r11 (.reg .r11)) ++ [.mov32 .r13 (.imm 0)]))))
      (.loop (VG.Impl.Rsa.X86_64.Keys.invStep fU fV fX₁ fX₂ aN fT) .ne) := by
    simp only [inverse, invInit, List.append_assoc]
  rw [e]
  refine ws_ct RpP.B RpP.Z (fun p => wk p.k) (fun _ _ h => h.ws) ht fun p s h => ?_
  rw [← e]
  have hw := h.ws
  have hZ16 : VG.Proof.Bignum.X86_64.slot (wk p.k) 16 ≤ 2 ^ 64 := by have := hw.scr.nowrap; have := hw.hZ; omega
  have h' := h
  obtain ⟨I, m₀, c, e, S, L, O, hmk, ⟨u0, vm⟩, -, x1, x2⟩ := h'
  subst e
  dsimp only [RpIn.pub] at hw hZ16
  have hw1 := hw.w1
  have hw2 := hw.w2
  have vX₂ : wv s.mem I.B (VG.Proof.Bignum.X86_64.slot (wk I.k) fX₂) (wk I.k) = 0 := by
    have := wv_add s.mem I.B (VG.Proof.Bignum.X86_64.slot (wk I.k) fX₂) (wk I.k) 2; have := x2 rfl; omega
  refine WP.mono (inverse_ok hw.scr hw.rdi hw.hw hw.hS (by omega) hw2 hw.hZ
    (iU := fU) (iV := fV) (iX₁ := fX₁) (iX₂ := fX₂) (iM := aN) (iT := fT) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    u0 vm (x1 rfl) vX₂) fun u ⟨_, f', k, _⟩ => ?_
  have f : Frm I.B (VG.Proof.Rsa.X86_64.rg (wk I.k) [fU, fV, fX₁, fX₂, fT] [sMo]) s.mem u.mem := f'.widen (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact VG.Proof.Rsa.X86_64.rg_cover_arr _ (by decide) (Nat.le_refl _) (by omega)
    · exact VG.Proof.Rsa.X86_64.rg_cover_arr _ (by decide) (Nat.le_refl _) (by omega)
    · exact VG.Proof.Rsa.X86_64.rg_cover_arr _ (by decide) (Nat.le_refl _) (by omega)
    · exact VG.Proof.Rsa.X86_64.rg_cover_arr _ (by decide) (Nat.le_refl _) (by omega)
    · exact VG.Proof.Rsa.X86_64.rg_cover_arr _ (by decide) (Nat.le_refl _) (Nat.le_refl _)
    · exact VG.Proof.Rsa.X86_64.rg_cover_hdr _ (by decide))
  exact h.step f (by decide) (by decide) (by decide) k (by decide) fun _ _ _ => trivial

theorem divmod_gct {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base fR .r8 ++ (([.mov .r11 (.reg .r12)] : List Instr) ++
      (List.replicate 6 (.alu .add .r11 (.reg .r11)) ++ ([.mov32 .r13 (.imm 0)] : List Instr)))))
      (.seq zeroAccLoop (.loop (VG.Impl.Rsa.X86_64.Keys.divStep fQ fR fV fT) .ne))) hc).isSome = true) :
    RelCT isa (Two (VG.Proof.Rsa.X86_64.Rp.FX fun _ _ => True)) (divmod fQ fR fV fT) (Two (VG.Proof.Rsa.X86_64.Rp.FX fun _ _ => True)) := by
  have e : divmod fQ fR fV fT = .seq (.block (VG.Impl.Rsa.X86_64.Keys.ws ++ (base fR .r8 ++ ([.mov .r11 (.reg .r12)] ++
      (List.replicate 6 (.alu .add .r11 (.reg .r11)) ++ [.mov32 .r13 (.imm 0)])))))
      (.seq zeroAccLoop (.loop (VG.Impl.Rsa.X86_64.Keys.divStep fQ fR fV fT) .ne)) := by
    simp only [divmod, divInit, seqs, List.append_assoc]
  rw [e]
  refine ws_ct RpP.B RpP.Z (fun p => wk p.k) (fun _ _ h => h.ws) ht fun p s h => ?_
  rw [← e]
  have hw := h.ws
  refine WP.mono (divmod_ok hw.scr hw.rdi hw.hw hw.hS (by have := hw.w1; omega) hw.w2 hw.hZ (iQ := fQ) (iR := fR)
    (iD := fV) (iT := fT) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun u ⟨_, f', k, _⟩ => ?_
  have f : Frm p.B (VG.Proof.Rsa.X86_64.rg (wk p.k) [fQ, fR, fT] []) s.mem u.mem := f'.widen (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact VG.Proof.Rsa.X86_64.rg_cover_arr _ (by decide) (Nat.le_refl _) (Nat.le_refl _)
    · exact VG.Proof.Rsa.X86_64.rg_cover_arr _ (by decide) (Nat.le_refl _) (Nat.le_refl _)
    · exact VG.Proof.Rsa.X86_64.rg_cover_arr _ (by decide) (Nat.le_refl _) (Nat.le_refl _))
  exact h.step f (by decide) (by simp) (by simp) k (by decide) fun _ _ _ => trivial

theorem finB_ct : RelCT isa (Two (VG.Proof.Rsa.X86_64.Rp.FX VG.Proof.Rsa.X86_64.Rp.XT)) (seqs [zeroA fV, copyA fV aN, zeroA fX₁, .block (setOneA fX₁),
    zeroA fX₂, inverse fU fV fX₁ fX₂ aN fT, zeroA fQ, copyA fQ aN, divmod fQ fR fV fT])
    (Two (VG.Proof.Rsa.X86_64.Rp.FX fun _ _ => True)) := by
  have hB : ∀ (X : VG.Proof.Rsa.X86_64.RpIn → State → Prop) p s, VG.Proof.Rsa.X86_64.Rp.FX X p s → Ws s p.B p.Z (wk p.k) := fun _ _ _ h => h.ws
  simp only [seqs]
  -- `v = n`.
  refine RelCT.seq (R := Two (VG.Proof.Rsa.X86_64.Rp.FX VG.Proof.Rsa.X86_64.Rp.XT)) (VG.Proof.Rsa.X86_64.Rp.zeroA_gct RpP.B RpP.Z (fun p => wk p.k) (hB _) (by taint_decide)
    fun p s h => WP.mono (zeroA_ok h.ws (j := fV) (by decide)) fun u ⟨_, o, k⟩ =>
      h.step (Frm.rg_of_out o (Nat.le_refl _) [fV] [] (by decide)) (by decide) (by simp) (by simp) k (by decide)
        fun I e ht => by
          subst e
          have hw := h.ws
          dsimp only [RpIn.pub] at o hw
          have hZ16 : VG.Proof.Bignum.X86_64.slot (wk I.k) 16 ≤ 2 ^ 64 := by have := hw.scr.nowrap; have := hw.hZ; omega
          show VG.Proof.Bignum.X86_64.word u.mem I.B (VG.Proof.Bignum.X86_64.slot (wk I.k) fU + 8 * wk I.k) = 0
          rw [(Frm.rg_of_out o (Nat.le_refl _) [fV] [] (by decide)).rg_wordA hZ16 (by simp) (by decide) (by decide)
            (by omega)]
          exact ht) ?_
  refine RelCT.seq (R := Two (VG.Proof.Rsa.X86_64.Rp.FX VG.Proof.Rsa.X86_64.Rp.XV)) (VG.Proof.Rsa.X86_64.Rp.copyA_gct RpP.B RpP.Z (fun p => wk p.k) (hB _) (by taint_decide)
    fun p s h => ?_) ?_
  · have hw := h.ws
    have hZ16 : VG.Proof.Bignum.X86_64.slot (wk p.k) 16 ≤ 2 ^ 64 := by have := hw.scr.nowrap; have := hw.hZ; omega
    refine WP.mono (copyA_ok hw (o := fV) (a := aN) (by decide) (by decide) (by decide)) fun u ⟨cv, o, k⟩ => ?_
    have hf : Frm p.B (VG.Proof.Rsa.X86_64.rg (wk p.k) [fV] []) s.mem u.mem := Frm.rg_of_out o (by omega) _ _ (by decide)
    refine h.step hf (by decide) (by simp) (by simp) k (by decide) fun I e ht => ?_
    subst e; dsimp only [RpIn.pub] at hf cv hZ16
    refine ⟨?_, ?_⟩
    · show VG.Proof.Bignum.X86_64.word u.mem I.B (VG.Proof.Bignum.X86_64.slot (wk I.k) fU + 8 * wk I.k) = 0
      rw [hf.rg_wordA hZ16 (by simp) (by decide) (by decide) (by omega)]; exact ht
    · rw [cv, hf.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega)]
  -- `x₁ = 1`, `x₂ = 0`.
  refine RelCT.seq (R := Two (VG.Proof.Rsa.X86_64.Rp.FX (VG.Proof.Rsa.X86_64.Rp.XW false false))) (VG.Proof.Rsa.X86_64.Rp.zeroA_gct RpP.B RpP.Z (fun p => wk p.k) (hB _)
    (by taint_decide) fun p s h => ?_) ?_
  · have hw := h.ws
    have hZ16 : VG.Proof.Bignum.X86_64.slot (wk p.k) 16 ≤ 2 ^ 64 := by have := hw.scr.nowrap; have := hw.hZ; omega
    refine WP.mono (zeroA_ok hw (j := fX₁) (by decide)) fun u ⟨z, o, k⟩ => ?_
    have hf : Frm p.B (VG.Proof.Rsa.X86_64.rg (wk p.k) [fX₁] []) s.mem u.mem := Frm.rg_of_out o (Nat.le_refl _) _ _ (by decide)
    refine h.step hf (by decide) (by simp) (by simp) k (by decide) fun I e hv => ?_
    subst e; dsimp only [RpIn.pub] at hf z hZ16
    refine ⟨VG.Proof.Rsa.X86_64.Rp.xv_keep hZ16 hf (by decide) (by decide) (by decide) hv, fun _ => z, ?_, ?_⟩ <;> intro e <;> cases e
  refine RelCT.seq (R := Two (VG.Proof.Rsa.X86_64.Rp.FX (VG.Proof.Rsa.X86_64.Rp.XW true false))) ?_ ?_
  · have e : setOneA fX₁ = VG.Impl.Rsa.X86_64.Keys.ws ++ (base fX₁ .rbx ++ ([.mov32 .rax (.imm 1), .store (at0 .rbx) .rax] :
        List Instr)) := by
      simp only [setOneA, List.append_assoc]
    rw [e]
    refine ws_block_ct RpP.B RpP.Z (fun p => wk p.k) (hB _) (by taint_decide) fun p s h => ?_
    rw [← e]
    have hw := h.ws
    have hn := hw.scr.nowrap
    have hZ16 : VG.Proof.Bignum.X86_64.slot (wk p.k) 16 ≤ 2 ^ 64 := by have := hw.hZ; omega
    have sX₁ := hw.sl (j := fX₁) (by decide)
    have hw1 := hw.w1
    refine WP.mono (setOneA_ok hw (j := fX₁) (by decide)) fun u ⟨m, k⟩ => ?_
    have hf : Frm p.B (VG.Proof.Rsa.X86_64.rg (wk p.k) [fX₁] []) s.mem u.mem := by
      rw [m]; exact Frm.rg_of_out (VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (by omega)) (by omega) _ _ (by decide)
    refine h.step hf (by decide) (by simp) (by simp) k (by decide) fun I e hv => ?_
    subst e; dsimp only [RpIn.pub] at hf m hZ16 hn sX₁ hw1
    refine ⟨VG.Proof.Rsa.X86_64.Rp.xv_keep hZ16 hf (by decide) (by decide) (by decide) hv.1, ?_, fun _ => ?_, ?_⟩
    · intro e; cases e
    · rw [m]; exact VG.Proof.Rsa.X86_64.wv_set_one (by omega) (hv.2.1 rfl) (by omega)
    · intro e; cases e
  refine RelCT.seq (R := Two (VG.Proof.Rsa.X86_64.Rp.FX (VG.Proof.Rsa.X86_64.Rp.XW true true))) (VG.Proof.Rsa.X86_64.Rp.zeroA_gct RpP.B RpP.Z (fun p => wk p.k) (hB _)
    (by taint_decide) fun p s h => ?_) ?_
  · have hw := h.ws
    have hZ16 : VG.Proof.Bignum.X86_64.slot (wk p.k) 16 ≤ 2 ^ 64 := by have := hw.scr.nowrap; have := hw.hZ; omega
    refine WP.mono (zeroA_ok hw (j := fX₂) (by decide)) fun u ⟨z, o, k⟩ => ?_
    have hf : Frm p.B (VG.Proof.Rsa.X86_64.rg (wk p.k) [fX₂] []) s.mem u.mem := Frm.rg_of_out o (Nat.le_refl _) _ _ (by decide)
    refine h.step hf (by decide) (by simp) (by simp) k (by decide) fun I e hv => ?_
    subst e; dsimp only [RpIn.pub] at hf z hZ16
    refine ⟨VG.Proof.Rsa.X86_64.Rp.xv_keep hZ16 hf (by decide) (by decide) (by decide) hv.1, ?_, fun _ => ?_, fun _ => z⟩
    · intro e; cases e
    rw [hf.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega)]; exact hv.2.2.1 rfl
  -- The inverse, and `q = n / v`.
  refine RelCT.seq (VG.Proof.Rsa.X86_64.Rp.inverse_gct (by taint_decide)) (RelCT.seq (R := Two (VG.Proof.Rsa.X86_64.Rp.FX fun _ _ => True))
    (VG.Proof.Rsa.X86_64.Rp.zeroA_gct RpP.B RpP.Z (fun p => wk p.k) (hB _) (by taint_decide) fun p s h =>
      WP.mono (zeroA_ok h.ws (j := fQ) (by decide)) fun u ⟨_, o, k⟩ =>
        h.step (Frm.rg_of_out o (Nat.le_refl _) [fQ] [] (by decide)) (by decide) (by simp) (by simp) k (by decide)
          fun _ _ _ => trivial) (RelCT.seq (R := Two (VG.Proof.Rsa.X86_64.Rp.FX fun _ _ => True))
    (VG.Proof.Rsa.X86_64.Rp.copyA_gct RpP.B RpP.Z (fun p => wk p.k) (hB _) (by taint_decide) fun p s h =>
      WP.mono (copyA_ok h.ws (o := fQ) (a := aN) (by decide) (by decide) (by decide)) fun u ⟨_, o, k⟩ =>
        h.step (Frm.rg_of_out o (by omega) [fQ] [] (by decide)) (by decide) (by simp) (by simp) k (by decide)
          fun _ _ _ => trivial) (VG.Proof.Rsa.X86_64.Rp.divmod_gct (by taint_decide))))

/-! ## The larger first, and the stores -/

theorem finC_ct : RelCT isa (Two (VG.Proof.Rsa.X86_64.Rp.FX fun _ _ => True)) (seqs [.block (VG.Impl.Rsa.X86_64.Keys.ws ++ base fV .rbx ++ base fQ .r10 ++
    ([.mov32 .rbp (.imm 0)] : List Instr)), wordLoop 0 ltBody, .block [.mov .r15 (.reg .rbp)], wordLoop 0 cswapBody])
    (Two (VG.Proof.Rsa.X86_64.Rp.FX fun _ _ => True)) := by
  have e : seqs [.block (VG.Impl.Rsa.X86_64.Keys.ws ++ base fV .rbx ++ base fQ .r10 ++ [.mov32 .rbp (.imm 0)]), wordLoop 0 ltBody,
      .block [.mov .r15 (.reg .rbp)], wordLoop 0 cswapBody] = .seq (.block (VG.Impl.Rsa.X86_64.Keys.ws ++ (base fV .rbx ++ (base fQ .r10 ++
        ([.mov32 .rbp (.imm 0)] : List Instr))))) (.seq (wordLoop 0 ltBody) (.seq (.block [.mov .r15 (.reg .rbp)])
          (wordLoop 0 cswapBody))) := by
    simp only [seqs, List.append_assoc]
  rw [e]
  refine ws_ct RpP.B RpP.Z (fun p => wk p.k) (fun _ _ h => h.ws) (by taint_decide) fun p s h => ?_
  rw [← e]
  exact WP.mono (VG.Proof.Rsa.X86_64.finC_ok h.ws) fun u ⟨f, k, _⟩ => h.step f (by decide) (by simp) (by simp) k (by decide)
    fun _ _ _ => trivial

/-- Before the stores: the working space, the arguments and the mask. -/
def GSr (p : VG.Proof.Rsa.X86_64.RpP) (s : State) : Prop :=
  ∃ (I : VG.Proof.Rsa.X86_64.RpIn) (c : Bool), I.pub = p ∧ Ws s I.B I.Z (wk I.k) ∧
    VG.Proof.Rsa.X86_64.RpArgs s.mem I.B I.k I.el I.dl I.pP I.pQ I.pN I.pE I.pD I.sv ∧ s.wr = I.W ∧ VG.Proof.Rsa.X86_64.RpLens I ∧ VG.Proof.Rsa.X86_64.RpOuts I ∧
    VG.Proof.Bignum.X86_64.word s.mem I.B (8 * sMask) = VG.Proof.Bignum.X86_64.mask c

theorem GSr.ws {p : VG.Proof.Rsa.X86_64.RpP} {s : State} (h : VG.Proof.Rsa.X86_64.Rp.GSr p s) : Ws s p.B p.Z (wk p.k) := by
  obtain ⟨I, c, rfl, h, -⟩ := h
  exact h

theorem pins_GSr : Pins VG.Proof.Rsa.X86_64.Rp.GSr [.rdi] := fun _ _ _ h₁ h₂ r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [h₁.ws.rdi, h₂.ws.rdi]

theorem storeR_ct {j sPtr : Nat} (hj : j < 16) (hP : sPtr < 32) (ptr : VG.Proof.Rsa.X86_64.RpP → Addr)
    (hA : ∀ p s, VG.Proof.Rsa.X86_64.Rp.GSr p s → VG.Proof.Bignum.X86_64.word s.mem p.B (8 * sPtr) = ptr p ∧
      (∀ i < p.k, InRegions p.W (ptr p + BitVec.ofNat 64 i) 1) ∧
      (∀ i < p.k, p.Z ≤ VG.Proof.Bignum.X86_64.ofs p.B (ptr p + BitVec.ofNat 64 i)))
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi]) (.block (VG.Impl.Rsa.X86_64.Keys.ws ++ base j .rbx ++ ([.mov .rsi (.mem (hdr sPtr)),
      .mov .rcx (.mem (hdr Impl.Bignum.X86_64.Public.sK)), .mov .r15 (.mem (hdr sMask))] : List Instr))) hc).isSome
      = true) :
    RelCT isa (Two VG.Proof.Rsa.X86_64.Rp.GSr) (seqs (storeA j sPtr Impl.Bignum.X86_64.Public.sK sMask)) (Two VG.Proof.Rsa.X86_64.Rp.GSr) :=
  pin_ct [.rdi] [.rdi, .rbx, .rsi, .rcx] (fun p => ioVal p.B (VG.Proof.Bignum.X86_64.off p.B (VG.Proof.Bignum.X86_64.slot (wk p.k) j)) (ptr p) p.k) VG.Proof.Rsa.X86_64.Rp.pins_GSr ht
    (fun p s h => by
      obtain ⟨hp, -⟩ := hA p s h
      have h' := h
      obtain ⟨I, c, rfl, hw, ha, -⟩ := h'
      exact WP.mono (storeBlk_ok hw hP (by decide) hp ha.k) fun t ⟨hbx, hsi, hcx, hdi⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hdi
        · exact hbx
        · exact hsi
        · exact hcx)
    (by taint_decide) fun p s h => by
      obtain ⟨hp, hwr, hsep⟩ := hA p s h
      obtain ⟨I, c, rfl, hw, ha, hW, L, O, hm⟩ := h
      dsimp only [RpIn.pub] at hp hwr hsep ⊢
      have hn := hw.scr.nowrap
      have h256 := hw.h256
      have hk1 := L.k1
      have hk2 := L.k2
      refine WP.mono (storeA_ws hw hj hP (by decide) hp ha.k hm (by omega) (by unfold wk; omega)
        (fun i hi => by rw [hW]; exact hwr i hi) hsep) fun t ⟨_, _, ht, hf, k⟩ => ?_
      have fw : ∀ i < 32, VG.Proof.Bignum.X86_64.word t.mem I.B (8 * i) = VG.Proof.Bignum.X86_64.word s.mem I.B (8 * i) :=
        fun i hi => hf.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact Or.inl (by omega)) (by omega)
      exact ⟨I, c, rfl, ht, ha.congr fun i hi => fw i (by unfold VG.Proof.Rsa.X86_64.rArg at hi; omega), k.2.2.trans hW, L, O,
        (fw _ (by decide)).trans hm⟩

/-- `fin` leaks the same in runs that agree on the public data. -/
theorem fin_ct (M : Mont) : RelCT isa (Two VG.Proof.Rsa.X86_64.Rp.GR3) (seqs (VG.Impl.Rsa.X86_64.Keys.Recover.fin M.mm)) fun _ _ => True := by
  rw [show VG.Impl.Rsa.X86_64.Keys.Recover.fin M.mm = [.block [.mov .rax (.mem (hdr sC3)), .store (hdr sMask) .rax], M.mm aY aY aOne, zeroA fU,
      .block (VG.Impl.Rsa.X86_64.Keys.ws ++ base aY .r8 ++ base aOne .r10 ++ base fU .rsi ++ [.mov32 .rbp (.imm 0)]),
      wordLoop 0 subBody] ++ ([zeroA fV, copyA fV aN, zeroA fX₁, .block (setOneA fX₁), zeroA fX₂,
        inverse fU fV fX₁ fX₂ aN fT, zeroA fQ, copyA fQ aN, divmod fQ fR fV fT] ++
      ([.block (VG.Impl.Rsa.X86_64.Keys.ws ++ base fV .rbx ++ base fQ .r10 ++ [.mov32 .rbp (.imm 0)]), wordLoop 0 ltBody,
        .block [.mov .r15 (.reg .rbp)], wordLoop 0 cswapBody] ++
      (storeA fV sP Impl.Bignum.X86_64.Public.sK sMask ++ (storeA fQ sQ Impl.Bignum.X86_64.Public.sK sMask ++
        ([.block retMask] : List (Prog isa)))))) by simp only [VG.Impl.Rsa.X86_64.Keys.Recover.fin, List.append_assoc, List.cons_append,
          List.nil_append]]
  refine (ct_app (by simp) (by simp) (VG.Proof.Rsa.X86_64.Rp.finA_ct M) (ct_app (by simp) (by simp) VG.Proof.Rsa.X86_64.Rp.finB_ct (ct_app (by simp)
    (by simp [storeA]) VG.Proof.Rsa.X86_64.Rp.finC_ct (?_ : RelCT isa (Two (VG.Proof.Rsa.X86_64.Rp.FX fun _ _ => True)) _ (Two fun (_ : VG.Proof.Rsa.X86_64.RpP) (_ : State) => True))))).mono
      (fun _ _ h => h) fun _ _ _ => trivial
  refine RelCT.seqs_append (by simp [storeA]) (by simp [storeA]) (RelCT.seq (R := Two VG.Proof.Rsa.X86_64.Rp.GSr) ?_ ?_)
  · refine (VG.Proof.Rsa.X86_64.Rp.storeR_ct (by decide) (by decide) RpP.pP (fun p s h => ?_) (by taint_decide)).mono
      (fun _ _ h => two_mono (fun p s ⟨I, m₀, c, e, S, L, O, hm, _⟩ => ⟨I, c, e, S.ws, S.args, S.wr, L, O, hm⟩) h)
      fun _ _ h => h
    obtain ⟨I, c, rfl, -, ha, -, L, O, -⟩ := h
    exact ⟨ha.p, O.p, O.sp⟩
  refine RelCT.seqs_append (by simp [storeA]) (by simp) (RelCT.seq (R := Two VG.Proof.Rsa.X86_64.Rp.GSr)
    (VG.Proof.Rsa.X86_64.Rp.storeR_ct (by decide) (by decide) RpP.pQ (fun p s h => ?_) (by taint_decide)) ?_)
  · obtain ⟨I, c, rfl, -, ha, -, L, O, -⟩ := h
    exact ⟨ha.q, O.q, O.sq⟩
  exact (two_taint [.rdi] VG.Proof.Rsa.X86_64.Rp.pins_GSr (by taint_decide)).mono (fun _ _ h => h) fun _ _ _ => ⟨default, trivial, trivial⟩

end Rp

end VG.Proof.Rsa.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rsa.X86_64.RpCode`. -/
section

/-!
# `vg_rsa_recover_primes` on x86-64: correctness

`Recover.code mul`, from a state its contract allows, writes `primesKey` of
its inputs (`rpCode_correct`), against `rpContract`, which states the shared
contract's precondition on the registers and the stack.
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN)

/-! ## The contract on the registers and the stack -/

/-- `vg_rsa_recover_primes(p = rdi, p_len = rsi, q = rdx, q_len = rcx,
n = r8, n_len = r9, e = [rsp + 8], e_len = [rsp + 16], d = [rsp + 24],
d_len = [rsp + 32], scratch = [rsp + 40], scratch_len = [rsp + 48])`. -/
def rpContract : Contract isa where
  pre s :=
    let p : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let q : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let n : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
    let e : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
    let d : Region := ⟨stackArg s 2, (stackArg s 3).toNat⟩
    let scr : Region := ⟨stackArg s 4, (stackArg s 5).toNat * 8⟩
    let args : Region := ⟨stackArgAddr s 0, 48⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    (s.gpr .rsp).toNat + 56 ≤ 2 ^ 64 ∧
      s.rd = [n, e, d, args] ∧ s.wr = [p, q, scr] ∧
      p.Disjoint q ∧ p.Disjoint n ∧ p.Disjoint e ∧ p.Disjoint d ∧ p.Disjoint scr ∧ p.Disjoint args ∧
      q.Disjoint n ∧ q.Disjoint e ∧ q.Disjoint d ∧ q.Disjoint scr ∧ q.Disjoint args ∧
      n.Disjoint scr ∧ e.Disjoint scr ∧ d.Disjoint scr ∧ scr.Disjoint args ∧
      ret.Disjoint p ∧ ret.Disjoint q ∧ ret.Disjoint n ∧ ret.Disjoint e ∧ ret.Disjoint d ∧
      ret.Disjoint scr ∧ ret.Disjoint args ∧
      (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧
      (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 64 ∧
      (stackArg s 4).toNat + (stackArg s 5).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (s.gpr .r9).toNat ∧ (s.gpr .rsi).toNat = (s.gpr .r9).toNat ∧
      (s.gpr .rcx).toNat = (s.gpr .r9).toNat ∧ 1 ≤ (stackArg s 1).toNat ∧
      (stackArg s 1).toNat ≤ (s.gpr .r9).toNat ∧ 1 ≤ (stackArg s 3).toNat ∧
      (stackArg s 3).toNat ≤ (s.gpr .r9).toNat ∧
      Spec.Rsa.scratchWords (s.gpr .r9).toNat ≤ (stackArg s 5).toNat
  post s s' :=
    Spec.Rsa.writtenAll s'.mem [(s.gpr .rdi, (s.gpr .r9).toNat), (s.gpr .rdx, (s.gpr .r9).toNat)]
      ((s'.gpr .rax).setWidth 32)
      ((Spec.Rsa.primesKey (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)).1.map fun v => [v.1, v.2])
  pub s₁ s₂ :=
    (∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₁.gpr r = s₂.gpr r) ∧
      stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2 ∧
      stackArg s₁ 3 = stackArg s₂ 3 ∧ stackArg s₁ 4 = stackArg s₂ 4 ∧ stackArg s₁ 5 = stackArg s₂ 5 ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r8) (s₁.gpr .r9).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r8) (s₂.gpr .r9).toNat ∧
      Spec.Rsa.bytesAt s₁.mem (stackArg s₁ 0) (stackArg s₁ 1).toNat =
        Spec.Rsa.bytesAt s₂.mem (stackArg s₂ 0) (stackArg s₂ 1).toNat ∧
      (Spec.Rsa.primesKey (Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r8) (s₁.gpr .r9).toNat)
        (Spec.Rsa.bytesAt s₁.mem (stackArg s₁ 0) (stackArg s₁ 1).toNat)
        (Spec.Rsa.bytesAt s₁.mem (stackArg s₁ 2) (stackArg s₁ 3).toNat)).2 =
      (Spec.Rsa.primesKey (Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r8) (s₂.gpr .r9).toNat)
        (Spec.Rsa.bytesAt s₂.mem (stackArg s₂ 0) (stackArg s₂ 1).toNat)
        (Spec.Rsa.bytesAt s₂.mem (stackArg s₂ 2) (stackArg s₂ 3).toNat)).2

/-! ## The entry -/

theorem rpEntry_eq : entry = ([.mov .r11 (.mem { base := .rsp, disp := 40 }),
    .store (hdr11 0) .rbx, .store (hdr11 1) .rbp, .store (hdr11 2) .r12, .store (hdr11 3) .r13,
    .store (hdr11 4) .r14, .store (hdr11 5) .r15,
    .store (hdr11 sP) .rdi, .store (hdr11 sQ) .rdx, .store (hdr11 Impl.Bignum.X86_64.Public.sN) .r8,
    .store (hdr11 Impl.Bignum.X86_64.Public.sK) .r9] : List Instr) ++
    (crtPairs [(0, Impl.Bignum.X86_64.Public.sE), (1, Impl.Bignum.X86_64.Public.sElen), (2, sD), (3, sDl)] ++
      ([.mov .rdi (.reg .r11)] : List Instr)) := rfl

/-- The header after the stores from registers. -/
def rpEntryMemA (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 vp vq vn vk : BitVec 64) : Mem :=
  (((((((((m.writeW (VG.Proof.Bignum.X86_64.off B (8 * 0)) v0).writeW (VG.Proof.Bignum.X86_64.off B (8 * 1)) v1).writeW (VG.Proof.Bignum.X86_64.off B (8 * 2)) v2).writeW
    (VG.Proof.Bignum.X86_64.off B (8 * 3)) v3).writeW (VG.Proof.Bignum.X86_64.off B (8 * 4)) v4).writeW (VG.Proof.Bignum.X86_64.off B (8 * 5)) v5).writeW (VG.Proof.Bignum.X86_64.off B (8 * sP)) vp).writeW
    (VG.Proof.Bignum.X86_64.off B (8 * sQ)) vq).writeW (VG.Proof.Bignum.X86_64.off B (8 * Impl.Bignum.X86_64.Public.sN)) vn).writeW
    (VG.Proof.Bignum.X86_64.off B (8 * Impl.Bignum.X86_64.Public.sK)) vk

/-- The header after the entry's stores. -/
def rpEntryMem (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 vp vq vn vk ve vel vd vdl : BitVec 64) : Mem :=
  ((((VG.Proof.Rsa.X86_64.rpEntryMemA m B v0 v1 v2 v3 v4 v5 vp vq vn vk).writeW (VG.Proof.Bignum.X86_64.off B (8 * Impl.Bignum.X86_64.Public.sE)) ve).writeW
    (VG.Proof.Bignum.X86_64.off B (8 * Impl.Bignum.X86_64.Public.sElen)) vel).writeW (VG.Proof.Bignum.X86_64.off B (8 * sD)) vd).writeW (VG.Proof.Bignum.X86_64.off B (8 * sDl)) vdl

theorem rpEntryMemA_outside (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 vp vq vn vk : BitVec 64) :
    VG.Proof.Bignum.X86_64.Outside B 0 (8 * 32) m (VG.Proof.Rsa.X86_64.rpEntryMemA m B v0 v1 v2 v3 v4 v5 vp vq vn vk) := by
  unfold VG.Proof.Rsa.X86_64.rpEntryMemA
  repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _)

theorem rpEntryMem_facts (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 vp vq vn vk ve vel vd vdl : BitVec 64) :
    let m' := VG.Proof.Rsa.X86_64.rpEntryMem m B v0 v1 v2 v3 v4 v5 vp vq vn vk ve vel vd vdl
    VG.Proof.Bignum.X86_64.word m' B (8 * 0) = v0 ∧ VG.Proof.Bignum.X86_64.word m' B (8 * 1) = v1 ∧ VG.Proof.Bignum.X86_64.word m' B (8 * 2) = v2 ∧ VG.Proof.Bignum.X86_64.word m' B (8 * 3) = v3 ∧
    VG.Proof.Bignum.X86_64.word m' B (8 * 4) = v4 ∧ VG.Proof.Bignum.X86_64.word m' B (8 * 5) = v5 ∧ VG.Proof.Bignum.X86_64.word m' B (8 * sP) = vp ∧ VG.Proof.Bignum.X86_64.word m' B (8 * sQ) = vq ∧
    VG.Proof.Bignum.X86_64.word m' B (8 * Impl.Bignum.X86_64.Public.sN) = vn ∧ VG.Proof.Bignum.X86_64.word m' B (8 * Impl.Bignum.X86_64.Public.sK) = vk ∧
    VG.Proof.Bignum.X86_64.word m' B (8 * Impl.Bignum.X86_64.Public.sE) = ve ∧ VG.Proof.Bignum.X86_64.word m' B (8 * Impl.Bignum.X86_64.Public.sElen) = vel ∧
    VG.Proof.Bignum.X86_64.word m' B (8 * sD) = vd ∧ VG.Proof.Bignum.X86_64.word m' B (8 * sDl) = vdl ∧
    VG.Proof.Bignum.X86_64.Outside B 0 (8 * 32) m m' := by
  intro m'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> unfold m' VG.Proof.Rsa.X86_64.rpEntryMem VG.Proof.Rsa.X86_64.rpEntryMemA
  all_goals first
    | (repeat (first | refine word_skip ?_ (by decide) (by decide) (by decide) |
        exact VG.Proof.Bignum.X86_64.word_writeW_self _ _ _ _)); done
    | (repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _))

/-- `entry`: the header, from the arguments, and the working space's base
(stack argument 4) in `rdi`. -/
theorem rpEntry_ok {s : State} {B : Addr} (hB : stackArg s 4 = B)
    (hw : ∀ i < 32, InRegions s.wr (VG.Proof.Bignum.X86_64.off B (8 * i)) 8)
    (ha : ∀ j < 5, InRegions (s.rd ++ s.wr) (stackArgAddr s j) 8)
    (hsep : ∀ j < 5, ∀ m', VG.Proof.Bignum.X86_64.Outside B 0 (8 * 32) s.mem m' → m'.readW (stackArgAddr s j) 64 = stackArg s j) :
    WP isa (.block entry) s fun t => t.gpr .rdi = B ∧
      (∀ i < 6, VG.Proof.Bignum.X86_64.word t.mem B (8 * i) = s.gpr (saved.getD i .rax)) ∧
      VG.Proof.Bignum.X86_64.word t.mem B (8 * sP) = s.gpr .rdi ∧ VG.Proof.Bignum.X86_64.word t.mem B (8 * sQ) = s.gpr .rdx ∧
      VG.Proof.Bignum.X86_64.word t.mem B (8 * Impl.Bignum.X86_64.Public.sN) = s.gpr .r8 ∧
      VG.Proof.Bignum.X86_64.word t.mem B (8 * Impl.Bignum.X86_64.Public.sK) = s.gpr .r9 ∧
      VG.Proof.Bignum.X86_64.word t.mem B (8 * Impl.Bignum.X86_64.Public.sE) = stackArg s 0 ∧
      VG.Proof.Bignum.X86_64.word t.mem B (8 * Impl.Bignum.X86_64.Public.sElen) = stackArg s 1 ∧
      VG.Proof.Bignum.X86_64.word t.mem B (8 * sD) = stackArg s 2 ∧ VG.Proof.Bignum.X86_64.word t.mem B (8 * sDl) = stackArg s 3 ∧
      VG.Proof.Bignum.X86_64.Outside B 0 (8 * 32) s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep [.r11, .rax, .rdi] s t := by
  have e4 : s.gpr .rsp + BitVec.ofInt 64 40 = stackArgAddr s 4 := rfl
  have hB' : s.mem.readW (stackArgAddr s 4) 64 = B := hB
  have ha4 := ha 4 (by decide)
  rw [VG.Proof.Rsa.X86_64.rpEntry_eq, WP.block_append_iff]
  refine WP.mono (WP.keep [.r11] (Q := fun t => t.gpr .r11 = B ∧
      t.mem = VG.Proof.Rsa.X86_64.rpEntryMemA s.mem B (s.gpr .rbx) (s.gpr .rbp) (s.gpr .r12) (s.gpr .r13) (s.gpr .r14)
        (s.gpr .r15) (s.gpr .rdi) (s.gpr .rdx) (s.gpr .r8) (s.gpr .r9)) ?_ rfl)
    fun t₁ ⟨⟨h11, hm₁⟩, k₁⟩ => ?_
  · xrun [State.ea, hdr11, e4, ha4, hB', hdrOff, hw 0 (by decide), hw 1 (by decide),
      hw 2 (by decide), hw 3 (by decide), hw 4 (by decide), hw 5 (by decide), hw sP (by decide),
      hw sQ (by decide), hw Impl.Bignum.X86_64.Public.sN (by decide), hw Impl.Bignum.X86_64.Public.sK (by decide)]
    rfl
  rw [WP.block_append_iff]
  refine WP.mono (crtPairs_ok _ t₁ ?_ h11 (k₁.gpr (by decide)) k₁.2.1 k₁.2.2
    (by rw [hm₁]; exact VG.Proof.Rsa.X86_64.rpEntryMemA_outside _ _ _ _ _ _ _ _ _ _ _ _)) fun t₂ ⟨hm₂, k₂⟩ => ?_
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;>
      exact ⟨by decide, ha _ (by decide), hsep _ (by decide), hw _ (by decide)⟩
  have h11₂ : t₂.gpr .r11 = B := (k₂.gpr (by decide)).trans h11
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = B ∧ t.mem = t₂.mem) (by xrun [h11₂]) rfl)
    fun t ⟨⟨hdi, hm⟩, k₃⟩ => ?_
  have hmem : t.mem = VG.Proof.Rsa.X86_64.rpEntryMem s.mem B (s.gpr .rbx) (s.gpr .rbp) (s.gpr .r12) (s.gpr .r13) (s.gpr .r14)
      (s.gpr .r15) (s.gpr .rdi) (s.gpr .rdx) (s.gpr .r8) (s.gpr .r9) (stackArg s 0) (stackArg s 1)
      (stackArg s 2) (stackArg s 3) := by
    rw [hm, hm₂, hm₁]; rfl
  rw [hmem]
  obtain ⟨h0, h1, h2, h3, h4, h5, hP, hQ, hN, hK, hE, hEl, hD, hDl, ho⟩ :=
    VG.Proof.Rsa.X86_64.rpEntryMem_facts s.mem B (s.gpr .rbx) (s.gpr .rbp) (s.gpr .r12) (s.gpr .r13) (s.gpr .r14)
      (s.gpr .r15) (s.gpr .rdi) (s.gpr .rdx) (s.gpr .r8) (s.gpr .r9) (stackArg s 0) (stackArg s 1)
      (stackArg s 2) (stackArg s 3)
  refine ⟨hdi, fun i hi => ?_, hP, hQ, hN, hK, hE, hEl, hD, hDl, ho, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

/-! ## The result -/

/-- What `Recover.code` leaves, from a valid modulus. -/
theorem rpWritten_of {m : Mem} {pp pq : Addr} {rax : BitVec 64} {nb eb db : List Byte}
    {res : Option (Nat × Nat)}
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) nb.length = true)
    (hres : (Spec.Rsa.recoverPrimes (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip eb) (Spec.Rsa.os2ip db)).1 = res)
    (b1 : Spec.Rsa.bytesAt m pp nb.length = Spec.Rsa.i2osp (VG.Proof.Rsa.X86_64.fstOr res) nb.length)
    (b2 : Spec.Rsa.bytesAt m pq nb.length = Spec.Rsa.i2osp (VG.Proof.Rsa.X86_64.sndOr res) nb.length)
    (hr : rax = BitVec.ofNat 64 res.isSome.toNat) :
    Spec.Rsa.writtenAll m [(pp, nb.length), (pq, nb.length)] (rax.setWidth 32)
      ((Spec.Rsa.primesKey nb eb db).1.map fun v => [v.1, v.2]) := by
  simp only [Spec.Rsa.primesKey, hv, ite_true]
  rw [hr, setWidth_flag]
  subst hres
  generalize Spec.Rsa.recoverPrimes (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip eb) (Spec.Rsa.os2ip db) = rp at b1 b2 ⊢
  obtain ⟨r1, r2⟩ := rp
  dsimp only at b1 b2 ⊢
  cases r1 with
  | none =>
    simp only [VG.Proof.Rsa.X86_64.fstOr, VG.Proof.Rsa.X86_64.sndOr, Option.isSome_none, Bool.false_eq_true, ite_false, Option.map_none, Spec.Rsa.writtenAll,
      List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at b1 b2 ⊢
    exact ⟨trivial, by rw [b1, i2osp_zero'], by rw [b2, i2osp_zero']⟩
  | some v =>
    obtain ⟨p, q⟩ := v
    simp only [VG.Proof.Rsa.X86_64.fstOr, VG.Proof.Rsa.X86_64.sndOr, Option.isSome_some, ite_true, Option.map_some, Spec.Rsa.writtenAll, List.map_cons,
      List.map_nil] at b1 b2 ⊢
    exact ⟨trivial, by rw [b1, b2]⟩

/-! ## The precondition, as the code uses it -/

/-- The inputs of `main`, from the entry state. -/
def rpIn (s : State) : VG.Proof.Rsa.X86_64.RpIn where
  B := stackArg s 4
  Z := (stackArg s 5).toNat * 8
  k := (s.gpr .r9).toNat
  el := (stackArg s 1).toNat
  dl := (stackArg s 3).toNat
  pP := s.gpr .rdi
  pQ := s.gpr .rdx
  pN := s.gpr .r8
  pE := stackArg s 0
  pD := stackArg s 2
  sv i := s.gpr (saved.getD i .rax)
  nb := Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat
  eb := Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat
  db := Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat
  W := s.wr
  sp := s.gpr .rsp

/-- What `Recover.code` uses of its contract's precondition. -/
structure RpCtx (s : State) : Prop where
  L : VG.Proof.Rsa.X86_64.RpLens (VG.Proof.Rsa.X86_64.rpIn s)
  rsi : (s.gpr .rsi).toNat = (s.gpr .r9).toNat
  rcx : (s.gpr .rcx).toNat = (s.gpr .r9).toNat
  hs : VG.Proof.Bignum.X86_64.Scr s (stackArg s 4) ((stackArg s 5).toNat * 8)
  ha : ∀ j < 5, InRegions (s.rd ++ s.wr) (stackArgAddr s j) 8
  hsep : ∀ j < 5, ∀ m', VG.Proof.Bignum.X86_64.Outside (stackArg s 4) 0 (8 * 32) s.mem m' →
    m'.readW (stackArgAddr s j) 64 = stackArg s j
  n : Src s (stackArg s 4) ((stackArg s 5).toNat * 8) (s.gpr .r8) (VG.Proof.Rsa.X86_64.rpIn s).nb
  e : Src s (stackArg s 4) ((stackArg s 5).toNat * 8) (stackArg s 0) (VG.Proof.Rsa.X86_64.rpIn s).eb
  d : Src s (stackArg s 4) ((stackArg s 5).toNat * 8) (stackArg s 2) (VG.Proof.Rsa.X86_64.rpIn s).db
  oP : OutOk s (stackArg s 4) ((stackArg s 5).toNat * 8) (s.gpr .rdi) (s.gpr .r9).toNat
  oQ : OutOk s (stackArg s 4) ((stackArg s 5).toNat * 8) (s.gpr .rdx) (s.gpr .r9).toNat
  a : VG.Proof.Rsa.X86_64.Apart (s.gpr .rdi) (s.gpr .r9).toNat (s.gpr .rdx) (s.gpr .r9).toNat
  hret : ∀ b < 8, (stackArg s 5).toNat * 8 ≤ VG.Proof.Bignum.X86_64.ofs (stackArg s 4) (s.gpr .rsp + BitVec.ofNat 64 b) ∧
    (∀ j < (s.gpr .r9).toNat, s.gpr .rsp + BitVec.ofNat 64 b ≠ s.gpr .rdi + BitVec.ofNat 64 j) ∧
    (∀ j < (s.gpr .r9).toNat, s.gpr .rsp + BitVec.ofNat 64 b ≠ s.gpr .rdx + BitVec.ofNat 64 j)

theorem rpCtx_of {s : State} (h : rpContract.pre s) : VG.Proof.Rsa.X86_64.RpCtx s := by
  simp only [VG.Proof.Rsa.X86_64.rpContract] at h
  obtain ⟨hsp, hrd, hwr, dpq, dpn, dpe, dpd, dps, dpa, dqn, dqe, dqd, dqs, dqa, dns, des, dds, dsa,
    dRp, dRq, dRn, dRe, dRd, dRs, dRa, wP, wQ, wN, wE, wD, wS, hk, hsi, hcx, hel1, hel2, hdl1, hdl2, hsl⟩ := h
  obtain ⟨hk1, hk2⟩ := hk
  unfold Spec.Rsa.scratchWords at hsl
  have hs : VG.Proof.Bignum.X86_64.Scr s (stackArg s 4) ((stackArg s 5).toNat * 8) := Scr.of_mem (by rw [hwr]; simp) wS
  have hn := hs.nowrap
  have hargs : (⟨stackArgAddr s 0, 48⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  rw [hsi] at dpq dpn dpe dpd dps dpa dRp wP
  rw [hcx] at dpq dqn dqe dqd dqs dqa dRq wQ
  refine ⟨⟨hk1, hk2, hel1, hel2, hdl1, hdl2, VG.Proof.Bignum.X86_64.bytesAt_length _ _ _, VG.Proof.Bignum.X86_64.bytesAt_length _ _ _,
      VG.Proof.Bignum.X86_64.bytesAt_length _ _ _, by simp only [VG.Proof.Rsa.X86_64.rpIn]; omega⟩, hsi, hcx, hs,
    fun j hj => ⟨_, hargs, by rw [stkAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega)⟩,
    fun j hj m' ho => Mem.readW_congr fun b hb => ho _ (Or.inr (by
      have := out_scr dsa.symm (contains_byte (stackArgAddr s 0) (i := 8 * j + b) (len := 48) (by omega) (by omega))
      rw [← stkAddr_add s j b] at this; omega)),
    src_of_region (by rw [hrd]; simp) (by omega) dns,
    src_of_region (by rw [hrd]; simp) (by omega) des,
    src_of_region (by rw [hrd]; simp) (by omega) dds,
    ⟨fun j hj => ⟨_, by rw [hwr, hsi]; simp, contains_byte _ hj (by omega)⟩,
      fun j hj => out_scr dps (contains_byte _ hj (by omega))⟩,
    ⟨fun j hj => ⟨_, by rw [hwr, hcx]; simp, contains_byte _ hj (by omega)⟩,
      fun j hj => out_scr dqs (contains_byte _ hj (by omega))⟩,
    apart_of dpq (by omega) (by omega), fun b hb => ?_⟩
  have hc := contains_byte (s.gpr .rsp) (i := b) (len := 8) (by omega) (by omega)
  exact ⟨out_scr dRs hc, fun j hj he => dRp _ hc (by rw [he]; exact contains_byte _ hj (by omega)),
    fun j hj he => dRq _ hc (by rw [he]; exact contains_byte _ hj (by omega))⟩

/-- After `entry` and the reloads of `n` and `k`, from `s`. -/
structure RpHeadPost (s t : State) : Prop where
  scr : VG.Proof.Bignum.X86_64.Scr t (stackArg s 4) ((stackArg s 5).toNat * 8)
  rdi : t.gpr .rdi = stackArg s 4
  rdx : t.gpr .rdx = s.gpr .r8
  rcx : t.gpr .rcx = BitVec.ofNat 64 (s.gpr .r9).toNat
  args : VG.Proof.Rsa.X86_64.RpArgs t.mem (VG.Proof.Rsa.X86_64.rpIn s).B (VG.Proof.Rsa.X86_64.rpIn s).k (VG.Proof.Rsa.X86_64.rpIn s).el (VG.Proof.Rsa.X86_64.rpIn s).dl (VG.Proof.Rsa.X86_64.rpIn s).pP (VG.Proof.Rsa.X86_64.rpIn s).pQ (VG.Proof.Rsa.X86_64.rpIn s).pN
    (VG.Proof.Rsa.X86_64.rpIn s).pE (VG.Proof.Rsa.X86_64.rpIn s).pD (VG.Proof.Rsa.X86_64.rpIn s).sv
  inScr : InScr (stackArg s 4) ((stackArg s 5).toNat * 8) s.mem t.mem
  keep : VG.Proof.MlKem.X86_64.Keep [.r11, .rax, .rdi, .rdx, .rcx] s t

/-- `entry`, and `n` and `k` into `rdx` and `rcx`. -/
theorem rpHead_ok' {s : State} (c : VG.Proof.Rsa.X86_64.RpCtx s) :
    WP isa (.block (entry ++ ([.mov .rdx (.mem (hdr Impl.Bignum.X86_64.Public.sN)),
      .mov .rcx (.mem (hdr Impl.Bignum.X86_64.Public.sK))] : List Instr))) s (VG.Proof.Rsa.X86_64.RpHeadPost s) := by
  have hn := c.hs.nowrap
  have hZ : 128 * (s.gpr .r9).toNat ≤ (stackArg s 5).toNat * 8 := c.L.z
  have hk1 : 64 ≤ (s.gpr .r9).toNat := c.L.k1
  have hw : ∀ i < 32, InRegions s.wr (VG.Proof.Bignum.X86_64.off (stackArg s 4) (8 * i)) 8 := fun i hi => c.hs.st (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Rsa.X86_64.rpEntry_ok rfl hw c.ha c.hsep) fun t₀ ⟨hdi, hsv, hP, hQ, hN, hK, hE, hEl, hD, hDl, ho₀, k₀⟩ => ?_
  have hs₀ := c.hs.congr k₀.2.2
  have eN : Impl.Bignum.X86_64.Public.sN = 17 := rfl
  have eK : Impl.Bignum.X86_64.Public.sK = 18 := rfl
  refine WP.mono (WP.keep [.rdx, .rcx] (Q := fun t => t.gpr .rdx = s.gpr .r8 ∧
      t.gpr .rcx = s.gpr .r9 ∧ t.mem = t₀.mem) (by
    xrun [State.ea, hdr, hdi, hdrOff, hs₀.ld (d := 8 * Impl.Bignum.X86_64.Public.sN) (by omega),
      hs₀.ld (d := 8 * Impl.Bignum.X86_64.Public.sK) (by omega), hN, hK]) rfl)
    fun t₁ ⟨⟨hdx, hcx, hm⟩, k₁⟩ => ?_
  rw [← hm] at hsv hP hQ hN hK hE hEl hD hDl
  refine ⟨hs₀.congr k₁.2.2, (k₁.gpr (by decide)).trans hdi, hdx, by rw [hcx, VG.Proof.Bignum.X86_64.ofNat_toNat64],
    ⟨hP, hQ, hN,
      show Bignum.X86_64.word _ (stackArg s 4) _ = BitVec.ofNat 64 (s.gpr .r9).toNat by rw [hK, VG.Proof.Bignum.X86_64.ofNat_toNat64],
      hE,
      show Bignum.X86_64.word _ (stackArg s 4) _ = BitVec.ofNat 64 (stackArg s 1).toNat by rw [hEl, VG.Proof.Bignum.X86_64.ofNat_toNat64],
      hD,
      show Bignum.X86_64.word _ (stackArg s 4) _ = BitVec.ofNat 64 (stackArg s 3).toNat by rw [hDl, VG.Proof.Bignum.X86_64.ofNat_toNat64],
      hsv⟩,
    by rw [hm]; exact InScr.of_outside ho₀ (by omega), (k₀.trans k₁).mono (by decide)⟩

/-- `main`'s hypotheses after the head and the modulus' check. -/
theorem rpPre_of {s t₁ t : State} (c : VG.Proof.Rsa.X86_64.RpCtx s) (h : VG.Proof.Rsa.X86_64.RpHeadPost s t₁) (hm : t.mem = t₁.mem)
    (k : VG.Proof.MlKem.X86_64.Keep [.rax, .rbp, .rsi] t₁ t) : VG.Proof.Rsa.X86_64.RpPre (VG.Proof.Rsa.X86_64.rpIn s) t := by
  have kk := h.keep.trans k
  have hi : InScr (stackArg s 4) ((stackArg s 5).toNat * 8) s.mem t.mem := by rw [hm]; exact h.inScr
  exact
    { scr := h.scr.congr k.2.2, rdi := (k.gpr (by decide)).trans h.rdi, args := by rw [hm]; exact h.args,
      n := c.n.congrK hi kk, e := c.e.congrK hi kk, d := c.d.congrK hi kk, L := c.L,
      oP := ⟨fun i hi => by rw [kk.2.2]; exact c.oP.wr i hi, c.oP.sep⟩,
      oQ := ⟨fun i hi => by rw [kk.2.2]; exact c.oQ.wr i hi, c.oQ.sep⟩,
      a := c.a, wr := kk.2.2, rsp := kk.gpr (by decide) }

/-- The saved registers and the return address, from what `fail` or `main`
leaves. -/
theorem rpGpr_of {s t₂ t : State} (c : VG.Proof.Rsa.X86_64.RpCtx s) (hsv : ∀ i < 6, t.gpr (saved.getD i .rax) = (VG.Proof.Rsa.X86_64.rpIn s).sv i)
    (hsp : t.gpr .rsp = t₂.gpr .rsp) (hsp₂ : t₂.gpr .rsp = s.gpr .rsp)
    (hfr : ∀ x, (stackArg s 5).toNat * 8 ≤ VG.Proof.Bignum.X86_64.ofs (stackArg s 4) x →
      (∀ i < (s.gpr .r9).toNat, x ≠ s.gpr .rdi + BitVec.ofNat 64 i) →
      (∀ i < (s.gpr .r9).toNat, x ≠ s.gpr .rdx + BitVec.ofNat 64 i) → t.mem x = s.mem x) :
    gprPreserved s t := by
  refine ⟨fun reg hreg => ?_, Mem.readW_congr fun b hb => ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hreg
    rcases hreg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsv 0 (by decide)
    · exact hsv 1 (by decide)
    · exact hsp.trans hsp₂
    · exact hsv 2 (by decide)
    · exact hsv 3 (by decide)
    · exact hsv 4 (by decide)
    · exact hsv 5 (by decide)
  · obtain ⟨hZx, n1, n2⟩ := c.hret b hb
    exact hfr _ hZx n1 n2

/-- `vg_rsa_recover_primes` with Montgomery multiplication `M`, given that
its code never loads MXCSR (which the registration file evaluates). -/
theorem rpCode_correct (M : Mont) (hmx : (VG.Impl.Rsa.X86_64.Keys.Recover.code M.mm).allInstrs (fun i => !loadsMxcsr i) = true)
    (s : State) (h : rpContract.pre s) :
    ∃ t s', Exec isa (VG.Impl.Rsa.X86_64.Keys.Recover.code M.mm) s t s' ∧ abiPreserved s s' ∧ rpContract.post s s' := by
  have c := VG.Proof.Rsa.X86_64.rpCtx_of h
  clear h
  have hk1 : 64 ≤ (s.gpr .r9).toNat := c.L.k1
  have hk2 : (s.gpr .r9).toNat ≤ 1024 := c.L.k2
  suffices hwp : WP isa (VG.Impl.Rsa.X86_64.Keys.Recover.code M.mm) s fun s' => gprPreserved s s' ∧ rpContract.post s s' by
    obtain ⟨t, s', he, hg, hp⟩ := hwp
    exact ⟨t, s', he, abiPreserved_of_exec hmx he hg, hp⟩
  unfold VG.Impl.Rsa.X86_64.Keys.Recover.code
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Rsa.X86_64.rpHead_ok' c) fun t₁ h₁ => ?_
  have hnb₁ := c.n.congrK h₁.inScr h₁.keep
  have hnl : (VG.Proof.Rsa.X86_64.rpIn s).nb.length = (s.gpr .r9).toNat := VG.Proof.Bignum.X86_64.bytesAt_length _ _ _
  refine WP.mono (invalid_ok h₁.rdx h₁.rcx hk1 hk2 hnl (fun i hi => hnb₁.rd i (by rw [hnl]; exact hi))
    (fun i hi => hnb₁.val i _)) fun t₂ ⟨hz₂, hm₂, k₂⟩ => ?_
  have hpre := VG.Proof.Rsa.X86_64.rpPre_of c h₁ hm₂ k₂
  have hsp₂ : t₂.gpr .rsp = s.gpr .rsp := hpre.rsp
  refine WP.ite (!Spec.Rsa.modulusValid (VG.Proof.Rsa.X86_64.rpIn s).N (s.gpr .r9).toNat) (by simp [VG.X86_64.eval, hz₂]) (fun hb => ?_)
    (fun hb => ?_)
  · have hv : Spec.Rsa.modulusValid (VG.Proof.Rsa.X86_64.rpIn s).N (s.gpr .r9).toNat = false := by simpa using hb
    have z : 128 * (s.gpr .r9).toNat ≤ (stackArg s 5).toNat * 8 := c.L.z
    exact WP.mono (VG.Proof.Rsa.X86_64.rpFail_ok hpre.scr hpre.rdi (show 8 * 32 ≤ (stackArg s 5).toNat * 8 by omega) hpre.args
      (show 1 ≤ (s.gpr .r9).toNat by omega) (show (s.gpr .r9).toNat < 2 ^ 31 by omega) hpre.oP hpre.oQ hpre.a)
      fun t ⟨z1, z2, hax, hsv, hfr, hsp⟩ => ⟨VG.Proof.Rsa.X86_64.rpGpr_of c hsv hsp hsp₂ fun x hx n1 n2 => by
        rw [hfr x n1 n2, hm₂]; exact h₁.inScr x hx, by
        show Spec.Rsa.writtenAll _ _ _ _
        have hnone : (Spec.Rsa.primesKey (VG.Proof.Rsa.X86_64.rpIn s).nb (VG.Proof.Rsa.X86_64.rpIn s).eb (VG.Proof.Rsa.X86_64.rpIn s).db).1 = none := by
          simp only [Spec.Rsa.primesKey]
          rw [hnl, hv]; simp
        simp only [VG.Proof.Rsa.X86_64.rpIn] at hnone
        rw [hnone, hax]
        simp only [Option.map_none, Spec.Rsa.writtenAll, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq]
        exact ⟨rfl, bytesAt_zero z1, bytesAt_zero z2⟩⟩
  · have hv : Spec.Rsa.modulusValid (VG.Proof.Rsa.X86_64.rpIn s).N (s.gpr .r9).toNat = true := by simpa using hb
    exact WP.mono (VG.Proof.Rsa.X86_64.rpMain_ok M hpre hv) fun t ⟨res, hres, b1, b2, hax, hsv, hfr, hsp⟩ =>
      ⟨VG.Proof.Rsa.X86_64.rpGpr_of c hsv hsp hsp₂ fun x hx n1 n2 => by
        rw [hfr x hx n1 n2, hm₂]; exact h₁.inScr x hx, by
        have := VG.Proof.Rsa.X86_64.rpWritten_of (m := t.mem) (pp := s.gpr .rdi) (pq := s.gpr .rdx) (eb := (VG.Proof.Rsa.X86_64.rpIn s).eb)
          (db := (VG.Proof.Rsa.X86_64.rpIn s).db) (by rw [hnl]; exact hv) hres (by rw [hnl]; exact b1) (by rw [hnl]; exact b2) hax
        rw [hnl] at this
        exact this⟩

end VG.Proof.Rsa.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rsa.X86_64.RpCT8`. -/
section

/-!
# `vg_rsa_recover_primes` on x86-64: constant time but for `n`, `e` and the tries

`rest` (`rest_ct`), `fail` (`failR_ct`) and `main` (`rpMain_ct`): `main`'s
branch on `d e` is the public number of tries being 0. Then the entry and
the modulus' check (`rpCode_ct`), and the contract's `ConstantTime`
(`rpCode_constantTime`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64
open VG.Spec.Rsa (recoverPrimes)

namespace Rp

/-- After the halvings, Montgomery form, the candidates and the factors. -/
theorem rest_ct (M : Mont) : RelCT isa (Two VG.Proof.Rsa.X86_64.Rp.GR0) (VG.Impl.Rsa.X86_64.Keys.Recover.rest M.mm) fun _ _ => True := by
  rw [show VG.Impl.Rsa.X86_64.Keys.Recover.rest M.mm = seqs ([halving] ++ (mont M.mm ++ ([candLoop M.mm] ++ VG.Impl.Rsa.X86_64.Keys.Recover.fin M.mm))) by
    simp only [VG.Impl.Rsa.X86_64.Keys.Recover.rest, List.append_assoc]]
  exact (ct_app (Ξ := fun (_ : VG.Proof.Rsa.X86_64.RpP) (_ : State) => True) (by simp) (by simp [mont]) VG.Proof.Rsa.X86_64.Rp.halving_ct (ct_app (by simp [mont]) (by simp [VG.Impl.Rsa.X86_64.Keys.Recover.fin]) (VG.Proof.Rsa.X86_64.Rp.mont_ct M)
    (ct_app (by simp) (by simp [VG.Impl.Rsa.X86_64.Keys.Recover.fin]) (ct_one (VG.Proof.Rsa.X86_64.Rp.candLoop_ct M)) ((VG.Proof.Rsa.X86_64.Rp.fin_ct M).mono (fun _ _ h => h)
      fun _ _ _ => ⟨default, trivial, trivial⟩)))).mono (fun _ _ h => h) fun _ _ _ => trivial

/-! ## `fail` -/

/-- Between the zeros of `fail`. -/
def GFr (p : VG.Proof.Rsa.X86_64.RpP) (s : State) : Prop :=
  ∃ I : VG.Proof.Rsa.X86_64.RpIn, I.pub = p ∧ VG.Proof.Bignum.X86_64.Scr s I.B I.Z ∧ s.gpr .rdi = I.B ∧
    VG.Proof.Rsa.X86_64.RpArgs s.mem I.B I.k I.el I.dl I.pP I.pQ I.pN I.pE I.pD I.sv ∧ s.wr = I.W ∧ VG.Proof.Rsa.X86_64.RpLens I ∧ VG.Proof.Rsa.X86_64.RpOuts I

theorem pins_GFr : Pins VG.Proof.Rsa.X86_64.Rp.GFr [.rdi] := fun _ _ _ ⟨_, e₁, _, h₁, _⟩ ⟨_, e₂, _, h₂, _⟩ r hr => by
  simp only [List.mem_singleton] at hr; subst hr
  rw [h₁, h₂]
  exact (congrArg RpP.B e₁).trans (congrArg RpP.B e₂).symm

theorem zeroOutR_ct {sPtr : Nat} (hP : sPtr < 32) (ptr : VG.Proof.Rsa.X86_64.RpP → Addr)
    (hA : ∀ p s, VG.Proof.Rsa.X86_64.Rp.GFr p s → VG.Proof.Bignum.X86_64.word s.mem p.B (8 * sPtr) = ptr p ∧
      (∀ i < p.k, InRegions p.W (ptr p + BitVec.ofNat 64 i) 1) ∧
      (∀ i < p.k, p.Z ≤ VG.Proof.Bignum.X86_64.ofs p.B (ptr p + BitVec.ofNat 64 i)))
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .rsi (.mem (hdr sPtr)),
      .mov .rcx (.mem (hdr Impl.Bignum.X86_64.Public.sK)), .mov32 .rax (.imm 0)]) hc).isSome = true) :
    RelCT isa (Two VG.Proof.Rsa.X86_64.Rp.GFr) (zeroOut sPtr Impl.Bignum.X86_64.Public.sK) (Two VG.Proof.Rsa.X86_64.Rp.GFr) :=
  pin_ct [.rdi] [.rsi, .rcx] (fun p => zoVal (ptr p) p.k) VG.Proof.Rsa.X86_64.Rp.pins_GFr ht
    (fun p s h => by
      obtain ⟨hp, -⟩ := hA p s h
      obtain ⟨I, rfl, hs, hdi, ha, -, L, -⟩ := h
      have hn := hs.nowrap
      have h256 : 8 * 32 ≤ I.Z := by have := L.z; have := L.k1; omega
      have hl' : ∀ i < 32, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off I.B (8 * i)) 8 := fun i hi => hs.ld (by omega)
      refine WP.mono (WP.keep [.rsi, .rcx, .rax] (Q := fun t => t.gpr .rsi = ptr I.pub ∧
        t.gpr .rcx = BitVec.ofNat 64 I.k) (by
        xrun [State.ea, hdr, hdi, hdrOff, hl' sPtr hP, hl' Impl.Bignum.X86_64.Public.sK (by decide)]
        exact ⟨hp, ha.k⟩) rfl) fun t ⟨⟨h1, h2⟩, _⟩ r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h1
      · exact h2)
    (by taint_decide) fun p s h => by
      obtain ⟨hp, hwr, hsep⟩ := hA p s h
      obtain ⟨I, rfl, hs, hdi, ha, hW, L, O⟩ := h
      dsimp only [RpIn.pub] at hp hwr hsep ⊢
      have hn := hs.nowrap
      have h256 : 8 * 32 ≤ I.Z := by have := L.z; have := L.k1; omega
      have hk1 := L.k1
      have hk2 := L.k2
      refine WP.mono (zeroOut_ok hs hdi h256 hP (by decide) hp ha.k (by omega) (by omega)
        ⟨fun i hi => by rw [hW]; exact hwr i hi, hsep⟩) fun t ⟨_, hx, k⟩ => ?_
      have fw : ∀ i < 32, VG.Proof.Bignum.X86_64.word t.mem I.B (8 * i) = VG.Proof.Bignum.X86_64.word s.mem I.B (8 * i) :=
        fun i hi => (frm_scr hsep hx).word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact Or.inl (by omega))
          (by omega)
      exact ⟨I, rfl, hs.congr k.2.2, (k.gpr (by decide)).trans hdi, ha.congr fun i hi => fw i (by
        unfold VG.Proof.Rsa.X86_64.rArg at hi; omega), k.2.2.trans hW, L, O⟩

/-- `fail` leaks the same in two runs with the same public data. -/
theorem failR_ct : RelCT isa (Two VG.Proof.Rsa.X86_64.Rp.GFr) fail fun _ _ => True := by
  unfold fail
  refine (VG.Proof.Rsa.X86_64.ct_cons (by simp) (VG.Proof.Rsa.X86_64.Rp.zeroOutR_ct (by decide) RpP.pP (fun p s h => ?_) (by taint_decide))
    (VG.Proof.Rsa.X86_64.ct_cons (by simp) (VG.Proof.Rsa.X86_64.Rp.zeroOutR_ct (by decide) RpP.pQ (fun p s h => ?_) (by taint_decide))
    (ct_one (Ψ := fun (_ : VG.Proof.Rsa.X86_64.RpP) (_ : State) => True)
      ((two_taint [.rdi] VG.Proof.Rsa.X86_64.Rp.pins_GFr (by taint_decide)).mono (fun _ _ h => h)
        fun _ _ _ => ⟨default, trivial, trivial⟩)))).mono (fun _ _ h => h) fun _ _ _ => trivial
  all_goals
    obtain ⟨I, rfl, -, -, ha, -, L, O⟩ := h
    dsimp only [RpIn.pub]
  · exact ⟨ha.p, O.p, O.sp⟩
  · exact ⟨ha.q, O.q, O.sq⟩

/-! ## `main` -/

/-- The public number of tries is 0 iff `d e` fails step 1. -/
theorem cnt_zero {I : VG.Proof.Rsa.X86_64.RpIn} (hv : Spec.Rsa.modulusValid I.N I.k = true) (L : VG.Proof.Rsa.X86_64.RpLens I) :
    I.pub.cnt = 0 ↔ ¬(I.D * I.E % 2 = 1 ∧ 2 ≤ I.D * I.E) := by
  have e : I.pub.cnt = (recoverPrimes I.N I.E I.D).2 := by
    show (Spec.Rsa.primesKey I.nb I.eb I.db).2 = _
    simp only [Spec.Rsa.primesKey, L.nbl, hv, ite_true]
    split <;> simp_all
  rw [e]
  by_cases h : I.D * I.E < 2 ∨ (I.D * I.E - 1) % 2 = 1
  · rw [VG.Proof.Rsa.recoverPrimes_none h]; omega
  · rw [VG.Proof.Rsa.recoverPrimes_go h]
    have := VG.Proof.Rsa.go_pos I.N (Spec.Rsa.splitTwos (I.D * I.E - 1)).1
      (Spec.Rsa.splitTwos (I.D * I.E - 1)).2 _ (Nat.le_refl _)
    omega

/-- After `main`'s prefix. -/
def GMP (p : VG.Proof.Rsa.X86_64.RpP) (s : State) : Prop :=
  ∃ (σ : State) (I : VG.Proof.Rsa.X86_64.RpIn), I.pub = p ∧ VG.Proof.Rsa.X86_64.RpPre I σ ∧ Spec.Rsa.modulusValid I.N I.k = true ∧ VG.Proof.Rsa.X86_64.RpS I σ.mem s ∧
    s.zf = some (decide (I.D * I.E % 2 = 1 ∧ 2 ≤ I.D * I.E)) ∧
    wv s.mem I.B (VG.Proof.Bignum.X86_64.slot (wk I.k) aM) (2 * (wk I.k + 2)) = I.D * I.E - I.D * I.E % 2 ∧
    wv s.mem I.B (VG.Proof.Bignum.X86_64.slot (wk I.k) Impl.Bignum.X86_64.Public.aN) (wk I.k) = I.N ∧
    ((VG.Proof.Bignum.X86_64.word s.mem I.B (VG.Proof.Bignum.X86_64.slot (wk I.k) Impl.Bignum.X86_64.Public.aN)).toNat *
      (VG.Proof.Bignum.X86_64.word s.mem I.B (8 * sMinv)).toNat + 1) % 2 ^ 64 = 0 ∧
    I.D * I.E < 2 ^ (64 * (wk I.k + (I.el + 7) / 8))

theorem gmp_eval {p : VG.Proof.Rsa.X86_64.RpP} {s : State} (h : VG.Proof.Rsa.X86_64.Rp.GMP p s) : isa.eval .ne s = some (decide (p.cnt = 0)) := by
  obtain ⟨σ, I, rfl, hp, hv, -, hz, -⟩ := h
  simp only [VG.X86_64.eval, hz, Option.map_some]
  congr 1
  have := VG.Proof.Rsa.X86_64.Rp.cnt_zero hv hp.L
  by_cases hc : (I.D * I.E % 2 = 1 ∧ 2 ≤ I.D * I.E)
  · simp_all
  · simp_all; omega

/-- `main` leaks the same in runs that agree on the public data. -/
theorem rpMain_ct (M : Mont) : RelCT isa (Two VG.Proof.Rsa.X86_64.Rp.GM) (VG.Impl.Rsa.X86_64.Keys.Recover.main M.mm) fun _ _ => True := by
  rw [VG.Proof.Rsa.X86_64.rpMain_eq']
  refine RelCT.seqs_append (by simp) (by simp) (RelCT.seq (R := Two VG.Proof.Rsa.X86_64.Rp.GMP) (two_post (prefix_ct.mono (fun _ _ h => h) fun _ _ _ => trivial)
    fun p s ⟨I, e, h, hv⟩ => WP.mono (VG.Proof.Rsa.X86_64.rpPrefix_ok h hv) fun t ⟨S, hz, vM, vN, hi, hDE⟩ =>
      ⟨s, I, e, h, hv, S, hz, vM, vN, hi, hDE⟩) ?_)
  simp only [seqs]
  refine two_ite (fun p s₁ s₂ h₁ h₂ => by rw [VG.Proof.Rsa.X86_64.Rp.gmp_eval h₁, VG.Proof.Rsa.X86_64.Rp.gmp_eval h₂]) ?_ ?_
  · refine failR_ct.mono (fun _ _ h => two_mono (fun p t ⟨⟨σ, I, e, hp, hv, S, _⟩, _⟩ =>
      ⟨I, e, S.ws.scr, S.ws.rdi, S.args, S.wr, hp.L, hp.outs⟩) h) fun _ _ h => h
  · refine (VG.Proof.Rsa.X86_64.Rp.rest_ct M).mono (fun _ _ h => two_mono (fun p t ⟨h, hf⟩ => ?_) h) fun _ _ h => h
    have hev := VG.Proof.Rsa.X86_64.Rp.gmp_eval h
    obtain ⟨σ, I, rfl, hp, hv, S, hz, vM, vN, hi, hDE⟩ := h
    rw [hev] at hf
    have hb : I.D * I.E % 2 = 1 ∧ 2 ≤ I.D * I.E := by
      have := VG.Proof.Rsa.X86_64.Rp.cnt_zero hv hp.L; simp only [Option.some.injEq, decide_eq_false_iff_not] at hf
      by_contra hn; exact hf (this.mpr hn)
    have L := hp.L
    have k1 := L.k1
    have k2 := L.k2
    obtain ⟨hNo, hlo⟩ := valid_lo hv
    have hlo' : 2 ^ (64 * (wk I.k - 1)) ≤ I.N := by
      refine Nat.le_trans ?_ hlo
      rw [pow256_eq]; exact Nat.pow_le_pow_right (by decide) (by unfold wk; omega)
    exact ⟨I, σ.mem, rfl, ⟨S, L, hNo, hlo', vN, hi, by rw [vM]; omega, by omega, by omega, by omega,
      ⟨fun i hi => by rw [S.wr, ← hp.wr]; exact hp.oP.wr i hi, hp.oP.sep⟩,
      ⟨fun i hi => by rw [S.wr, ← hp.wr]; exact hp.oQ.wr i hi, hp.oQ.sep⟩, hp.a⟩, hp.outs, hv⟩

end Rp

/-! ## The code -/

/-- A state the contract allows, with the public data `p`. -/
def RPRel (p : VG.Proof.Rsa.X86_64.RpP) (s : State) : Prop := rpContract.pre s ∧ (VG.Proof.Rsa.X86_64.rpIn s).pub = p

theorem rpEntry_split : entry ++ ([.mov .rdx (.mem (hdr Impl.Bignum.X86_64.Public.sN)),
    .mov .rcx (.mem (hdr Impl.Bignum.X86_64.Public.sK))] : List Instr) =
    ([.mov .r11 (.mem { base := .rsp, disp := 40 })] : List Instr) ++
      ((entry.drop 1) ++ [.mov .rdx (.mem (hdr Impl.Bignum.X86_64.Public.sN)),
        .mov .rcx (.mem (hdr Impl.Bignum.X86_64.Public.sK))]) := rfl

/-- After `entry`'s first instruction. -/
def RP1 (p : VG.Proof.Rsa.X86_64.RpP) (t : State) : Prop :=
  ∃ s, VG.Proof.Rsa.X86_64.RPRel p s ∧ t.gpr .r11 = p.B ∧ t.gpr .rsp = p.sp ∧
    WP isa (.block ((entry.drop 1) ++ [.mov .rdx (.mem (hdr Impl.Bignum.X86_64.Public.sN)),
      .mov .rcx (.mem (hdr Impl.Bignum.X86_64.Public.sK))])) t (VG.Proof.Rsa.X86_64.RpHeadPost s)

/-- After `entry` and the reloads. -/
def RP2 (p : VG.Proof.Rsa.X86_64.RpP) (t : State) : Prop := ∃ s, VG.Proof.Rsa.X86_64.RPRel p s ∧ VG.Proof.Rsa.X86_64.RpHeadPost s t

/-- After the modulus' check. -/
def RP3 (p : VG.Proof.Rsa.X86_64.RpP) (t : State) : Prop :=
  ∃ s t₁, VG.Proof.Rsa.X86_64.RPRel p s ∧ VG.Proof.Rsa.X86_64.RpHeadPost s t₁ ∧ t.mem = t₁.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rbp, .rsi] t₁ t ∧
    t.zf = some (Spec.Rsa.modulusValid (Spec.Rsa.os2ip p.nb) p.k)

/-- `vg_rsa_recover_primes` leaks the same in runs that agree on the public
data. -/
theorem rpCode_ct (M : Mont) : RelCT isa (Two VG.Proof.Rsa.X86_64.RPRel) (VG.Impl.Rsa.X86_64.Keys.Recover.code M.mm) fun _ _ => True := by
  unfold VG.Impl.Rsa.X86_64.Keys.Recover.code
  refine RelCT.seq (R := Two VG.Proof.Rsa.X86_64.RP3) (RelCT.block_append (RelCT.seq (R := Two VG.Proof.Rsa.X86_64.RP2) ?_ ?_)) ?_
  · rw [VG.Proof.Rsa.X86_64.rpEntry_split]
    refine RelCT.block_append (RelCT.seq (two_piece (Ψ := VG.Proof.Rsa.X86_64.RP1) [.rsp] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (congrArg RpP.sp h₁.2).trans (congrArg RpP.sp h₂.2).symm) (by taint_decide) ?_)
      (two_piece [.r11, .rsp] (fun p s₁ s₂ ⟨_, _, a₁, b₁, _⟩ ⟨_, _, a₂, b₂, _⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [a₁, a₂]
        · rw [b₁, b₂]) (by taint_decide) fun p t ⟨s, hs, _, _, hw⟩ => WP.mono hw fun t' h => ⟨s, hs, h⟩))
    intro p s hs
    have c := VG.Proof.Rsa.X86_64.rpCtx_of hs.1
    have hh : WP isa (.block (([.mov .r11 (.mem { base := .rsp, disp := 40 })] : List Instr) ++
        ((entry.drop 1) ++ [.mov .rdx (.mem (hdr Impl.Bignum.X86_64.Public.sN)),
          .mov .rcx (.mem (hdr Impl.Bignum.X86_64.Public.sK))]))) s (VG.Proof.Rsa.X86_64.RpHeadPost s) := by
      rw [← VG.Proof.Rsa.X86_64.rpEntry_split]; exact VG.Proof.Rsa.X86_64.rpHead_ok' c
    have e4 : s.gpr .rsp + BitVec.ofInt 64 40 = stackArgAddr s 4 := rfl
    have hB' : s.mem.readW (stackArgAddr s 4) 64 = stackArg s 4 := rfl
    refine WP.mono (WP.and (WP.block_append_iff.mp hh) (WP.keep [.r11] (Q := fun t => t.gpr .r11 = stackArg s 4)
      (by xrun [State.ea, e4, c.ha 4 (by decide), hB']) rfl)) fun t ⟨hw, h11, k⟩ =>
        ⟨s, hs, h11.trans (congrArg RpP.B hs.2), (k.gpr (by decide)).trans (congrArg RpP.sp hs.2), hw⟩
  -- The modulus' check.
  · refine two_piece [.rdx, .rcx] (fun p s₁ s₂ ⟨σ₁, c₁, h₁⟩ ⟨σ₂, c₂, h₂⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.rdx, h₂.rdx]
        exact (congrArg RpP.pN c₁.2).trans (congrArg RpP.pN c₂.2).symm
      · rw [h₁.rcx, h₂.rcx]
        exact congrArg (BitVec.ofNat 64) ((congrArg RpP.k c₁.2).trans (congrArg RpP.k c₂.2).symm))
      (by taint_decide) ?_
    rintro p t ⟨s, hs, h⟩
    have c := VG.Proof.Rsa.X86_64.rpCtx_of hs.1
    have hnb := c.n.congrK h.inScr h.keep
    have hnl : (VG.Proof.Rsa.X86_64.rpIn s).nb.length = (s.gpr .r9).toNat := VG.Proof.Bignum.X86_64.bytesAt_length _ _ _
    refine WP.mono (invalid_ok h.rdx h.rcx c.L.k1 c.L.k2 hnl (fun i hi => hnb.rd i (by rw [hnl]; exact hi))
      (fun i hi => hnb.val i _)) fun t' ⟨hz, hm, k⟩ => ⟨s, t, hs, h, hm, k, ?_⟩
    rw [hz, ← hs.2]
    rfl
  -- `fail` or `main`.
  refine two_ite (fun p s₁ s₂ ⟨_, _, _, _, _, _, z₁⟩ ⟨_, _, _, _, _, _, z₂⟩ => by
    simp only [VG.X86_64.eval, z₁, z₂]) ?_ ?_
  · exact Rp.failR_ct.mono (fun _ _ h => two_mono (fun p t ⟨⟨s, t₁, hs, h, hm, k, _⟩, _⟩ => by
      have hpre := VG.Proof.Rsa.X86_64.rpPre_of (VG.Proof.Rsa.X86_64.rpCtx_of hs.1) h hm k
      exact ⟨VG.Proof.Rsa.X86_64.rpIn s, hs.2, hpre.scr, hpre.rdi, hpre.args, hpre.wr, hpre.L, hpre.outs⟩) h) fun _ _ h => h
  · exact (Rp.rpMain_ct M).mono (fun _ _ h => two_mono (fun p t ⟨⟨s, t₁, hs, h, hm, k, z⟩, hf⟩ => by
      refine ⟨VG.Proof.Rsa.X86_64.rpIn s, hs.2, VG.Proof.Rsa.X86_64.rpPre_of (VG.Proof.Rsa.X86_64.rpCtx_of hs.1) h hm k, ?_⟩
      have hz : Spec.Rsa.modulusValid (Spec.Rsa.os2ip p.nb) p.k = true := by
        simp only [VG.X86_64.eval, z, Option.map_some, Option.some.injEq] at hf; simpa using hf
      have e : (VG.Proof.Rsa.X86_64.rpIn s).pub = p := hs.2
      subst e
      exact hz) h) fun _ _ h => h

/-- `vg_rsa_recover_primes` is constant time but for `n`, `e` and the number
of tries. -/
theorem rpCode_constantTime (M : Mont) : ConstantTime isa rpContract.pre rpContract.pub (VG.Impl.Rsa.X86_64.Keys.Recover.code M.mm) := by
  refine RelCT.constantTime ((VG.Proof.Rsa.X86_64.rpCode_ct M).mono (fun s₁ s₂ ⟨h₁, h₂, hp⟩ => ⟨(VG.Proof.Rsa.X86_64.rpIn s₁).pub, ⟨h₁, rfl⟩, ⟨h₂, ?_⟩⟩)
    fun _ _ h => h)
  obtain ⟨hr, a0, a1, a2, a3, a4, a5, hn, he, hc⟩ := hp
  have r : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₂.gpr r = s₁.gpr r := fun r h => (hr r h).symm
  have w₁ := h₁.2.2.1
  have w₂ := h₂.2.2.1
  simp only [RpIn.pub, VG.Proof.Rsa.X86_64.rpIn, RpP.mk.injEq]
  refine ⟨a4.symm, by rw [a5], by rw [r .r9 (by decide)], by rw [a1], by rw [a3], r .rdi (by decide),
    r .rdx (by decide), r .r8 (by decide), a0.symm, a2.symm, hn.symm, he.symm, ?_, r .rsp (by decide), hc.symm⟩
  rw [w₁, w₂, r .rdi (by decide), r .rsi (by decide), r .rdx (by decide), r .rcx (by decide), a4, a5]

end VG.Proof.Rsa.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rsa.X86_64.RpVerified`. -/
section

/-!
# `vg_rsa_recover_primes` on x86-64: verified against the shared contract

`rpContract` states the shared contract on the registers and the stack
(`rp_implies`); with correctness (`rpCode_correct`) and constant time
(`rpCode_constantTime`), `Recover.code` is verified for any Montgomery
multiplication (`rp_verified`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Proof.Bignum.X86_64

theorem stackArgs_six (s : State) :
    List.map (stackArg s) (List.range 6) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5] := rfl

/-- A state meeting `rpContract.pre`: a 512-bit modulus, one-byte exponents,
and the stack arguments at `0x6008`. -/
def rpSatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 64 | .rdx => 0x1100 | .rcx => 64 | .r8 => 0x2000 | .r9 => 64
    | .rsp => 0x6000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x6009 then 0x30 else if a = 0x6010 then 1 else if a = 0x6019 then 0x31
    else if a = 0x6020 then 1 else if a = 0x6029 then 0x80 else if a = 0x6031 then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x3100, 1⟩, ⟨0x6008, 48⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1100, 64⟩, ⟨0x8000, 8192⟩]

theorem rp_implies : rpContract.Implies (Spec.Rsa.recoverPrimesContract abi) where
  pre := by
    intro s h
    -- Twice: the stack arguments' list evaluates only on the second pass.
    sig_pre [Spec.Rsa.recoverPrimesContract, Spec.Rsa.recoverPrimesSig, abi, argRegs, VG.Proof.Rsa.X86_64.rpContract, VG.Proof.Rsa.X86_64.stackArgs_six,
      List.append_eq] at h
    sig_pre [Spec.Rsa.recoverPrimesContract, Spec.Rsa.recoverPrimesSig, abi, argRegs, VG.Proof.Rsa.X86_64.rpContract, VG.Proof.Rsa.X86_64.stackArgs_six,
      List.append_eq] at h
    sig_split h
    sig_reduce [Spec.Rsa.recoverPrimesContract, Spec.Rsa.recoverPrimesSig, abi, argRegs, VG.Proof.Rsa.X86_64.rpContract, VG.Proof.Rsa.X86_64.stackArgs_six,
      List.append_eq]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by sig_implies_post [Spec.Rsa.recoverPrimesContract, Spec.Rsa.recoverPrimesSig, abi, argRegs, VG.Proof.Rsa.X86_64.rpContract,
    VG.Proof.Rsa.X86_64.stackArgs_six, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.Rsa.recoverPrimesContract, Spec.Rsa.recoverPrimesSig, abi, argRegs, VG.Proof.Rsa.X86_64.rpContract, VG.Proof.Rsa.X86_64.stackArgs_six,
      List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4, a5⟩ := h
    obtain ⟨hl₁, hc⟩ := List.append_inj' hl (List.length_singleton.trans List.length_singleton.symm)
    have hm := List.map_injective_iff.2 (fun _ _ h => BitVec.toNat_inj.1 h) hl₁
    obtain ⟨hn, he⟩ := List.append_inj hm (by rw [VG.Proof.Bignum.X86_64.bytesAt_length, VG.Proof.Bignum.X86_64.bytesAt_length, h9])
    refine ⟨?_, a0, a1, a2, a3, a4, a5, hn, he, List.singleton_inj.mp hc⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
  sat := by sig_implies_sat [Spec.Rsa.recoverPrimesContract, Spec.Rsa.recoverPrimesSig, abi, argRegs, VG.Proof.Rsa.X86_64.rpContract,
    VG.Proof.Rsa.X86_64.stackArgs_six, List.append_eq] [rpSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using VG.Proof.Rsa.X86_64.rpSatState

/-- `vg_rsa_recover_primes` with the Montgomery multiplication `M`, given that
its code never loads MXCSR (which the registration file evaluates). -/
theorem rp_verified (M : Mont) (hmx : (Recover.code M.mm).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target (Recover.code M.mm) (Spec.Rsa.recoverPrimesContract abi) :=
  Verified.of_correct (VG.Proof.Rsa.X86_64.rpCode_correct M hmx) (VG.Proof.Rsa.X86_64.rpCode_constantTime M) VG.Proof.Rsa.X86_64.rp_implies

end VG.Proof.Rsa.X86_64

end
