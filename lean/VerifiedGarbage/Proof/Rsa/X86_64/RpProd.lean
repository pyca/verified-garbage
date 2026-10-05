import VerifiedGarbage.Proof.Rsa.X86_64.RpBase
import VerifiedGarbage.Proof.Bignum.X86_64.Row

/-!
# `vg_rsa_recover_primes` on x86-64: `M = d e`

`prod` zeroes `M`'s two arrays and adds `e_j d` at word `j` of `M`, by
`mulAddRow`, for each word `j` of `e` (`prod_ok`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64

/-- `prodInit`: the bases, `e`'s words and the row counter. -/
theorem prodInit_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {el : Nat}
    (hel : word s.mem B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 el) (hel' : el < 2 ^ 32) :
    WP isa (.block prodInit) s fun t =>
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .rbx = off B (slot w aE) ∧ t.gpr .r10 = off B (slot w aM) ∧
      t.gpr .r15 = off B (slot w aD) ∧ t.gpr .r11 = BitVec.ofNat 64 ((el + 7) / 8) ∧
      t.gpr .r13 = BitVec.ofNat 64 0 ∧ t.gpr .rdi = B ∧ t.mem = s.mem ∧
      Keep [.r12, .r9, .rbx, .r10, .r15, .r11, .r13] s t := by
  unfold prodInit
  rw [List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono h.ws_ok fun t₁ ⟨h12, h9, m₁, k₁⟩ => WP.block_append_iff.mpr ?_
  have hdi₁ : t₁.gpr .rdi = B := (k₁.gpr (by decide)).trans h.rdi
  refine WP.mono (base_ok aE (r := .rbx) (by decide) hdi₁ h9) fun t₂ ⟨hbx, m₂, k₂⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (base_ok aM (r := .r10) (by decide) ((k₂.gpr (by decide)).trans hdi₁)
    ((k₂.gpr (by decide)).trans h9)) fun t₃ ⟨h10, m₃, k₃⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (base_ok aD (r := .r15) (by decide) ((k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans hdi₁))
    ((k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans h9))) fun t₄ ⟨h15, m₄, k₄⟩ => ?_
  have k14 := ((k₁.trans k₂).trans k₃).trans k₄
  have hdi₄ : t₄.gpr .rdi = B := (k14.gpr (by decide)).trans h.rdi
  have hs₄ := h.scr.congr k14.2.2
  have hl : InRegions (t₄.rd ++ t₄.wr) (off B (8 * Impl.Bignum.X86_64.Public.sElen)) 8 :=
    hs₄.ld (by have := h.h256; simp only [Impl.Bignum.X86_64.Public.sElen, sFn]; omega)
  refine WP.mono (WP.keep [.r11, .r13] (Q := fun t => t.gpr .r11 = BitVec.ofNat 64 ((el + 7) / 8) ∧
    t.gpr .r13 = BitVec.ofNat 64 0 ∧ t.mem = t₄.mem) (by
      xrun [State.ea, hdr, hdi₄, hdrOff, hl, m₄, m₃, m₂, m₁, hel, shr3_w el hel']) rfl)
    fun t ⟨⟨h11, h13, m⟩, k₅⟩ => ⟨?_, ?_, ?_, ?_, h11, h13, (k₅.gpr (by decide)).trans hdi₄,
      by rw [m, m₄, m₃, m₂, m₁], (k14.trans k₅).mono (by simp)⟩
  · exact (k₅.gpr (by decide)).trans ((k₄.gpr (by decide)).trans ((k₃.gpr (by decide)).trans
      ((k₂.gpr (by decide)).trans h12)))
  · exact (k₅.gpr (by decide)).trans ((k₄.gpr (by decide)).trans ((k₃.gpr (by decide)).trans hbx))
  · exact (k₅.gpr (by decide)).trans ((k₄.gpr (by decide)).trans h10)
  · exact (k₅.gpr (by decide)).trans h15

/-- `rowHead`: `e`'s word `j`, the accumulator's base at word `j` of `M`,
and `d`'s base. -/
theorem rowHead_ok {t : State} {B : Addr} {Z w j : Nat} (hs : Scr t B Z) (hZ : slot w 16 ≤ Z)
    (hbx : t.gpr .rbx = off B (slot w aE)) (h10 : t.gpr .r10 = off B (slot w aM))
    (h15 : t.gpr .r15 = off B (slot w aD)) (h13 : t.gpr .r13 = BitVec.ofNat 64 j) (hj : j < w) :
    WP isa (.block rowHead) t fun t' =>
      t'.gpr .rcx = word t.mem B (slot w aE + 8 * j) ∧ t'.gpr .r8 = off B (slot w aM + 8 * j) ∧
      t'.gpr .r9 = off B (slot w aD) ∧ t'.mem = t.mem ∧ Keep [.rcx, .r8, .r9] t t' := by
  have hn := hs.nowrap
  have sE := slot_lt (w := w) (show aE < 16 by decide)
  unfold rowHead
  refine WP.mono (WP.keep [.rcx, .r8, .r9] (Q := fun t' => t'.gpr .rcx = word t.mem B (slot w aE + 8 * j) ∧
    t'.gpr .r8 = off B (slot w aM + 8 * j) ∧ t'.gpr .r9 = off B (slot w aD) ∧ t'.mem = t.mem) ?_ rfl)
    fun t' ⟨⟨a, b, c, d⟩, k⟩ => ⟨a, b, c, d, k⟩
  xrun [State.ea, ix, addr0 hbx h13, hs.ld (d := slot w aE + 8 * j) (by omega), h10, h15]
  rw [h13, BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat, off, BitVec.add_comm,
    BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  congr 2
  omega

/-- A number below `P R` of the form `A + P (W + Q H)` with `R ≤ Q`: `H = 0`
and `W < R`. -/
theorem window_split {T A W H P Q R : Nat} (hT : T = A + P * (W + Q * H)) (hlt : T < P * R) (hRQ : R ≤ Q) :
    H = 0 ∧ W < R := by
  have h1 : P * (W + Q * H) < P * R := Nat.lt_of_le_of_lt (by rw [hT]; exact Nat.le_add_left _ _) hlt
  have h2 : W + Q * H < R := Nat.lt_of_mul_lt_mul_left h1
  refine ⟨?_, by omega⟩
  rcases Nat.eq_zero_or_pos H with h | h
  · exact h
  · have : Q ≤ Q * H := Nat.le_mul_of_pos_right _ h
    omega

theorem row_alg {A P W c D Ej Q : Nat} (hT : D * Ej = A + P * (W + Q * 0)) :
    A + P * (W + c * D + Q * 0) = D * (Ej + P * c) := by
  grind

/-- After `j` rows: `M = d (e mod 2^(64 j))`. -/
structure ProdInv (s₁ : State) (B : Addr) (Z w : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rax, .rdx, .rbp, .r14, .rcx, .r8, .r9, .r13] s₁ t
  r13 : t.gpr .r13 = BitVec.ofNat 64 j
  out : Outside B (slot w aM) (16 * (w + 2)) s₁.mem t.mem
  val : wv t.mem B (slot w aM) (2 * (w + 2)) = wv s₁.mem B (slot w aD) w * wv s₁.mem B (slot w aE) j

/-- A row. -/
theorem prodStep_ok {s₁ t : State} {B : Addr} {Z w we j : Nat} (hI : ProdInv s₁ B Z w j t) (hw : 2 ≤ w)
    (hw' : w < 2 ^ 24) (hZ : slot w 16 ≤ Z) (hwe : we ≤ w) (hj : j < we)
    (h12 : s₁.gpr .r12 = BitVec.ofNat 64 w) (hbx : s₁.gpr .rbx = off B (slot w aE))
    (h10 : s₁.gpr .r10 = off B (slot w aM)) (h15 : s₁.gpr .r15 = off B (slot w aD))
    (h11 : s₁.gpr .r11 = BitVec.ofNat 64 we) :
    WP isa (.seq (.block rowHead) (.seq mulAddRow (.block rowNext))) t fun t' =>
      t'.zf = some (decide (j + 1 = we)) ∧ ProdInv s₁ B Z w (j + 1) t' := by
  have hn := hI.scr.nowrap
  have sE := slot_lt (w := w) (show aE < 16 by decide)
  have sD := slot_lt (w := w) (show aD < 16 by decide)
  have sM := slot_lt (w := w) (show aM + 1 < 16 by decide)
  have eM1 : slot w (aM + 1) = slot w aM + 8 * (w + 2) := by simp only [slot, hdrBytes, aM]; omega
  have eDM : slot w aD + 8 * (w + 2) = slot w aM := by simp only [slot, hdrBytes, aD, aM]; omega
  have eEM : slot w aE + 8 * (w + 2) = slot w aD := by simp only [slot, hdrBytes, aE, aD]; omega
  refine WP.seq (WP.mono (rowHead_ok hI.scr hZ ((hI.keep.gpr (by decide)).trans hbx)
    ((hI.keep.gpr (by decide)).trans h10) ((hI.keep.gpr (by decide)).trans h15) hI.r13 (by omega))
    fun t₁ ⟨hcx, h8, h9, m₁, k₁⟩ => ?_)
  have k01 := hI.keep.trans k₁
  have hs₁ := hI.scr.congr k₁.2.2
  -- `d` and `e`'s word `j`, as at the start.
  have hD : wv t₁.mem B (slot w aD) w = wv s₁.mem B (slot w aD) w := by
    rw [m₁]; exact hI.out.wv (Or.inl (by omega)) (by omega)
  have hc : (t₁.gpr .rcx).toNat = (word s₁.mem B (slot w aE + 8 * j)).toNat := by
    rw [hcx, hI.out.word (Or.inl (by omega)) (by omega)]
  -- The accumulator's window, words `j` to `j + w + 1` of `M`.
  have hsplit : ∀ m : Mem, wv m B (slot w aM) (2 * (w + 2)) = wv m B (slot w aM) j + 2 ^ (64 * j) *
      (wv m B (slot w aM + 8 * j) (w + 2) + 2 ^ (64 * (w + 2)) *
        wv m B (slot w aM + 8 * j + 8 * (w + 2)) (w + 2 - j)) := fun m => by
    have e1 := wv_add m B (slot w aM) j (2 * (w + 2) - j)
    have e2 := wv_add m B (slot w aM + 8 * j) (w + 2) (w + 2 - j)
    rw [show j + (2 * (w + 2) - j) = 2 * (w + 2) by omega] at e1
    rw [show w + 2 + (w + 2 - j) = 2 * (w + 2) - j by omega] at e2
    rw [e1, e2]
  have hT := hsplit t₁.mem
  rw [m₁, hI.val] at hT
  have hlt : wv s₁.mem B (slot w aD) w * wv s₁.mem B (slot w aE) j < 2 ^ (64 * j) * 2 ^ (64 * w) := by
    rw [Nat.mul_comm (2 ^ (64 * j))]
    exact Nat.mul_lt_mul'' (wv_lt _ _ _ _) (wv_lt _ _ _ _)
  obtain ⟨hH, hW⟩ := window_split hT hlt (Nat.pow_le_pow_right (by decide) (by omega))
  have hbound : wv t₁.mem B (slot w aM + 8 * j) (w + 2) + (t₁.gpr .rcx).toNat * wv t₁.mem B (slot w aD) w <
      2 ^ (64 * (w + 2)) := by
    rw [hc, hD, m₁]
    have h1 : (word s₁.mem B (slot w aE + 8 * j)).toNat * wv s₁.mem B (slot w aD) w < 2 ^ 64 * 2 ^ (64 * w) :=
      Nat.mul_lt_mul'' (BitVec.isLt _) (wv_lt _ _ _ _)
    have h2 : 2 ^ (64 * (w + 2)) = 2 ^ (64 * w) * 2 ^ 128 := by rw [← Nat.pow_add]; congr 1
    have h3 : 2 ^ (64 * w) + 2 ^ 64 * 2 ^ (64 * w) ≤ 2 ^ (64 * w) * 2 ^ 128 := by
      rw [show 2 ^ (64 * w) + 2 ^ 64 * 2 ^ (64 * w) = 2 ^ (64 * w) * (1 + 2 ^ 64) by grind]
      exact Nat.mul_le_mul_left _ (by decide)
    omega
  refine WP.seq (WP.mono (mulAddRow_ok hs₁ h8 h9 ((k01.gpr (by decide)).trans h12) (by omega) (by omega)
    (by omega) (by omega) (Or.inr (by omega)) hbound) fun t₂ ⟨hv₂, o₂, k₂⟩ => ?_)
  have k02 := k01.trans k₂
  refine WP.mono (WP.keep [.r13] (Q := fun t' => t'.zf = some (decide (j + 1 = we)) ∧
      t'.gpr .r13 = BitVec.ofNat 64 (j + 1) ∧ t'.mem = t₂.mem) (by
    unfold rowNext
    xrun [(k₂.gpr (by decide) : t₂.gpr .r13 = _), (k₁.gpr (by decide) : t₁.gpr .r13 = _), hI.r13,
      (k02.gpr (by decide) : t₂.gpr .r11 = _), h11, ofNat_add_one,
      ofNat_sub_beq (show j + 1 < 2 ^ 64 by omega) (show we < 2 ^ 64 by omega)]) rfl)
    fun t ⟨⟨hz, h13, mt⟩, k₃⟩ => ⟨hz, ⟨hs₁.congr (k₂.trans k₃).2.2, (k02.trans k₃).mono (by simp), h13,
      fun x hx => by
        rw [mt, o₂ x (by omega), m₁]; exact hI.out x hx, ?_⟩⟩
  -- The value.
  have hT₂ := hsplit t.mem
  have eA : wv t.mem B (slot w aM) j = wv t₁.mem B (slot w aM) j := by
    rw [mt]; exact o₂.wv (Or.inl (by omega)) (by omega)
  have eH : wv t.mem B (slot w aM + 8 * j + 8 * (w + 2)) (w + 2 - j) =
      wv t₁.mem B (slot w aM + 8 * j + 8 * (w + 2)) (w + 2 - j) := by
    rw [mt]; exact o₂.wv (Or.inr (by omega)) (by omega)
  have eW : wv t.mem B (slot w aM + 8 * j) (w + 2) = wv t₁.mem B (slot w aM + 8 * j) (w + 2) +
      (t₁.gpr .rcx).toNat * wv t₁.mem B (slot w aD) w := by rw [mt]; exact hv₂
  rw [eA, eH, eW, hc, hD, m₁, hH] at hT₂
  rw [hT₂, wv]
  rw [hH] at hT
  exact row_alg hT

/-- `prod`: `M = d e` over `M`'s two arrays, for `e` of `⌈e_len / 8⌉` words. -/
theorem prod_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {el : Nat}
    (hel : word s.mem B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 el) (he1 : 1 ≤ el)
    (he2 : el ≤ 8 * w) (hE : wv s.mem B (slot w aE) w < 2 ^ (64 * ((el + 7) / 8))) :
    WP isa (seqs prod) s fun t =>
      wv t.mem B (slot w aM) (2 * (w + 2)) = wv s.mem B (slot w aD) w * wv s.mem B (slot w aE) w ∧
      Outside B (slot w aM) (16 * (w + 2)) s.mem t.mem ∧
      Keep [.r12, .r9, .r8, .rax, .r14, .rbx, .r10, .r15, .r11, .r13, .rdx, .rbp, .rcx] s t := by
  have hn := h.scr.nowrap
  have hZ := h.hZ
  have hw1 := h.w1
  have hw2 := h.w2
  have sE := slot_lt (w := w) (show aE < 16 by decide)
  have sD := slot_lt (w := w) (show aD < 16 by decide)
  have sM := slot_lt (w := w) (show aM + 1 < 16 by decide)
  have eM1 : slot w (aM + 1) = slot w aM + 8 * (w + 2) := by simp only [slot, hdrBytes, aM]; omega
  have eDM : slot w aD + 8 * (w + 2) = slot w aM := by simp only [slot, hdrBytes, aD, aM]; omega
  have eEM : slot w aE + 8 * (w + 2) = slot w aD := by simp only [slot, hdrBytes, aE, aD]; omega
  unfold prod
  simp only [seqs]
  refine WP.seq (WP.mono (zeroA_ok h (j := aM) (by decide)) fun s₁ ⟨z₁, o₁, k₁⟩ => ?_)
  have h₁ := h.congr (Frm.of_outside o₁ (List.mem_singleton_self _))
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact Mut.ofSlot _ _ _) k₁ (by decide)
  refine WP.seq (WP.mono (zeroA_ok h₁ (j := aM + 1) (by decide)) fun s₂ ⟨z₂, o₂, k₂⟩ => ?_)
  have h₂ := h₁.congr (Frm.of_outside o₂ (List.mem_singleton_self _))
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact Mut.ofSlot _ _ _) k₂ (by decide)
  -- Memory but `M` as on entry.
  have o12 : Outside B (slot w aM) (16 * (w + 2)) s.mem s₂.mem := fun x hx => by
    rw [o₂ x (by omega), o₁ x (by omega)]
  have hel₂ : word s₂.mem B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 el := by
    rw [o12.word (Or.inl (by have := hdr_lt_slot w aM (show Impl.Bignum.X86_64.Public.sElen < 32 by decide); omega))
      (by simp only [Impl.Bignum.X86_64.Public.sElen, sFn]; omega)]; exact hel
  have hz : wv s₂.mem B (slot w aM) (2 * (w + 2)) = 0 := by
    rw [show 2 * (w + 2) = (w + 2) + (w + 2) by omega, wv_add, ← eM1, z₂,
      o₂.wv (Or.inl (by omega)) (by omega), z₁, Nat.mul_zero]
  refine WP.seq (WP.mono (prodInit_ok h₂ hel₂ (by omega)) fun s₃ ⟨h12, hbx, h10, h15, h11, h13, hdi, m₃, k₃⟩ => ?_)
  have hs₃ := h₂.scr.congr k₃.2.2
  refine wp_upto (a := 0) (N := (el + 7) / 8) (by omega) (ProdInv s₃ B Z w)
    (fun j _ hj t hI => prodStep_ok hI (by omega) (by omega) hZ (by omega) hj h12 hbx h10 h15 h11)
    (fun t hI => ?_) ⟨hs₃, Keep.refl _ _, h13, Outside.refl _ _ _ _, by rw [m₃, hz, wv, Nat.mul_zero]⟩
  have k03 := ((k₁.trans k₂).trans k₃).trans hI.keep
  have hDs : wv s₃.mem B (slot w aD) w = wv s.mem B (slot w aD) w := by
    rw [m₃]; exact o12.wv (Or.inl (by omega)) (by omega)
  have hEs : wv s₃.mem B (slot w aE) w = wv s.mem B (slot w aE) w := by
    rw [m₃]; exact o12.wv (Or.inl (by omega)) (by omega)
  refine ⟨?_, fun x hx => by rw [hI.out x hx, m₃]; exact o12 x hx, k03.mono (by simp)⟩
  rw [hI.val, hDs, wv_low_of_lt (v := (el + 7) / 8) (w := w) (by omega) (by rw [hEs]; exact hE), hEs]

end VG.Proof.Rsa.X86_64
