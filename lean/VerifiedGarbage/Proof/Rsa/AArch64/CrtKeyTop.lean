import VerifiedGarbage.Proof.Rsa.AArch64.Div
import VerifiedGarbage.Impl.Rsa.AArch64.CheckCrtKey

/-!
# `vg_rsa_check_crt_key` on AArch64: the shortened remainder

`reduceTop top` (`Impl/Rsa/AArch64/CheckCrtKey.lean`): for `c` words (in
`x13` by `top`), `[aRem]` starts as the words of `[aA]` from `c` up and the
top `c` words of `[aQ]` as its low ones, then `64 c` of `divmod`'s steps.
When the words from `c` up are below the divisor, the remainder is that of
`[aA]` (`reduceTop_ok`, by `divIter_top`).
-/

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Rsa.AArch64.CheckKey (aA aRem aM aT)
open VG.Impl.Rsa.AArch64.CheckCrtKey (aQ hiTail loTail cntTail reduceTop)
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- What `top` must do: `x13 := c`, keeping the memory, the carry and the
registers but `x3` and `x13`, from any state whose header is `s`'s. -/
def TopOk (top : List Instr) (B : Addr) (Z : Nat) (m₀ : Mem) (c : Nat) : Prop :=
  ∀ t : State, Scr t B Z → t.gpr .x0 = B → (∀ i < 32, word t.mem B (8 * i) = word m₀ B (8 * i)) →
    WP isa (.block top) t fun t' =>
      (t'.gpr .x13 = BitVec.ofNat 64 c ∧ t'.mem = t.mem ∧ t'.c = t.c) ∧ Keep [.x3, .x13] t t'

/-- The registers `reduceTop` changes. -/
def topRegs : List Reg := .x11 :: .x12 :: stepRegs

/-- The high part of a number zero in memory is zero. -/
theorem wv_hi_zero {m : Mem} {B : Addr} {d n k : Nat} (h : wv m B d (n + k) = 0) : wv m B (d + 8 * n) k = 0 := by
  rw [wv_add] at h
  have := Nat.two_pow_pos (64 * n)
  rcases Nat.eq_zero_or_pos (wv m B (d + 8 * n) k) with h0 | h0
  · exact h0
  · have : 0 < 2 ^ (64 * n) * wv m B (d + 8 * n) k := Nat.mul_pos ‹_› h0
    omega_arith

/-- The low part of a number zero in memory is zero. -/
theorem wv_lo_zero {m : Mem} {B : Addr} {d n k : Nat} (h : wv m B d (n + k) = 0) : wv m B d n = 0 := by
  rw [wv_add] at h; omega_arith

/-- The words of a number from `c` up are its quotient by `2^(64 c)`. -/
theorem wv_div_top {m : Mem} {B : Addr} {d c n : Nat} :
    wv m B d (c + n) / 2 ^ (64 * c) = wv m B (d + 8 * c) n := by
  rw [wv_add, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt (wv_lt _ _ _ _), Nat.zero_add]

/-- Its low `c` words are its remainder. -/
theorem wv_mod_low {m : Mem} {B : Addr} {d c n : Nat} :
    wv m B d (c + n) % 2 ^ (64 * c) = wv m B d c := by
  rw [wv_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (wv_lt _ _ _ _)]

/-- `reduceTop`'s first block: the bases of `[aA]`'s words from `c` up and of
`[aRem]`, and `w - c` words to copy. -/
theorem blkHi_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {top : List Instr} {c : Nat}
    (hT : TopOk top B Z s.mem c) (hc : c < w) :
    WP isa (.block (ws ++ top ++ base aA .x16 ++ base aRem .x17 ++ hiTail)) s fun t =>
    (t.gpr .x16 = off B (slot w aA + 8 * c) ∧ t.gpr .x17 = off B (slot w aRem) ∧
      t.gpr .x12 = BitVec.ofNat 64 (w - c) ∧ t.mem = s.mem) ∧ Keep [.x11, .x12, .x3, .x13, .x16, .x17] s t := by
  have hw := h.w2
  simp only [List.append_assoc]
  refine WP.block_append_iff.mpr (WP.mono h.ws_ok fun t₁ ⟨⟨e12, e11, m₁', _⟩, k₁'⟩ => ?_)
  refine WP.block_append_iff.mpr (WP.mono (hT t₁ (h.scr.congr k₁'.wr) ((k₁'.gpr .x0 (by decide)).trans h.x0) (fun i hi => by
    rw [m₁'])) fun t₂ ⟨⟨e13, m₂', _⟩, k₂'⟩ => ?_)
  refine WP.block_append_iff.mpr (WP.mono (base_ok aA .x16 (((k₁'.trans k₂').gpr .x0 (by decide)).trans h.x0)
    ((k₂'.gpr .x11 (by decide)).trans e11)) fun t₃ ⟨⟨e16, m₃', _⟩, k₃'⟩ => ?_)
  refine WP.block_append_iff.mpr (WP.mono (base_ok aRem .x17 ((((k₁'.trans k₂').trans k₃').gpr .x0 (by decide)).trans h.x0)
    (((k₂'.trans k₃').gpr .x11 (by decide)).trans e11)) fun t₄ ⟨⟨e17, m₄', _⟩, k₄'⟩ => ?_)
  have f13 : t₄.gpr .x13 = BitVec.ofNat 64 c := ((k₃'.trans k₄').gpr .x13 (by decide)).trans e13
  have f16 : t₄.gpr .x16 = off B (slot w aA) := (k₄'.gpr .x16 (by decide)).trans e16
  have f12 : t₄.gpr .x12 = BitVec.ofNat 64 w := (((k₂'.trans k₃').trans k₄').gpr .x12 (by decide)).trans e12
  refine WP.mono (WP.keep [.x3, .x16, .x12] (Q := fun t => t.gpr .x16 = off B (slot w aA + 8 * c) ∧
      t.gpr .x12 = BitVec.ofNat 64 (w - c) ∧ t.mem = t₄.mem) (by
    unfold hiTail
    brun [f13, f16, f12, shl_ofNat (show c * 2 ^ 3 < 2 ^ 64 by omega_arith), off, VG.Offset.add_ofNat_add_ofNat,
      VG.Offset.ofNat_sub_ofNat (show c ≤ w by omega_arith)]
    rw [show c * 2 ^ 3 = 8 * c by omega_arith]) (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨g16, g12, mt⟩,
        kt⟩ => ?_
  exact ⟨⟨g16, (kt.gpr .x17 (by decide)).trans e17, g12, mt.trans (m₄'.trans (m₃'.trans (m₂'.trans m₁')))⟩,
    ((((k₁'.trans k₂').trans k₃').trans k₄').trans kt).mono (by simp)⟩

/-- `reduceTop`'s second block: the bases of `[aA]` and of `[aQ]`'s top `c`
words, and `c` words to copy. -/
theorem blkLo_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {top : List Instr} {c : Nat}
    (hT : TopOk top B Z s.mem c) (hc : c < w) :
    WP isa (.block (ws ++ top ++ base aA .x16 ++ base aQ .x17 ++ loTail)) s fun t =>
    (t.gpr .x16 = off B (slot w aA) ∧ t.gpr .x17 = off B (slot w aQ + 8 * (w - c)) ∧
      t.gpr .x12 = BitVec.ofNat 64 c ∧ t.mem = s.mem) ∧ Keep [.x11, .x12, .x3, .x13, .x16, .x17] s t := by
  have hw := h.w2
  simp only [List.append_assoc]
  refine WP.block_append_iff.mpr (WP.mono h.ws_ok fun t₁ ⟨⟨e12, e11, m₁', _⟩, k₁'⟩ => ?_)
  refine WP.block_append_iff.mpr (WP.mono (hT t₁ (h.scr.congr k₁'.wr) ((k₁'.gpr .x0 (by decide)).trans h.x0) (fun i hi => by
    rw [m₁'])) fun t₂ ⟨⟨e13, m₂', _⟩, k₂'⟩ => ?_)
  refine WP.block_append_iff.mpr (WP.mono (base_ok aA .x16 (((k₁'.trans k₂').gpr .x0 (by decide)).trans h.x0)
    ((k₂'.gpr .x11 (by decide)).trans e11)) fun t₃ ⟨⟨e16, m₃', _⟩, k₃'⟩ => ?_)
  refine WP.block_append_iff.mpr (WP.mono (base_ok aQ .x17 ((((k₁'.trans k₂').trans k₃').gpr .x0 (by decide)).trans h.x0)
    (((k₂'.trans k₃').gpr .x11 (by decide)).trans e11)) fun t₄ ⟨⟨e17, m₄', _⟩, k₄'⟩ => ?_)
  have f13 : t₄.gpr .x13 = BitVec.ofNat 64 c := ((k₃'.trans k₄').gpr .x13 (by decide)).trans e13
  have f17 : t₄.gpr .x17 = off B (slot w aQ) := e17
  have f12 : t₄.gpr .x12 = BitVec.ofNat 64 w := (((k₂'.trans k₃').trans k₄').gpr .x12 (by decide)).trans e12
  refine WP.mono (WP.keep [.x3, .x17, .x12] (Q := fun t => t.gpr .x17 = off B (slot w aQ + 8 * (w - c)) ∧
      t.gpr .x12 = BitVec.ofNat 64 c ∧ t.mem = t₄.mem) (by
    unfold loTail
    brun [f13, f17, f12, VG.Offset.ofNat_sub_ofNat (show c ≤ w by omega_arith),
      shl_ofNat (show (w - c) * 2 ^ 3 < 2 ^ 64 by omega_arith), off, VG.Offset.add_ofNat_add_ofNat]
    rw [show (w - c) * 2 ^ 3 = 8 * (w - c)
        by omega_arith]) (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨g17, g12, mt⟩, kt⟩ => ?_
  exact ⟨⟨(kt.gpr .x16 (by decide)).trans ((k₄'.gpr .x16 (by decide)).trans e16), g17, g12,
    mt.trans (m₄'.trans (m₃'.trans (m₂'.trans m₁')))⟩, ((((k₁'.trans k₂').trans k₃').trans k₄').trans kt).mono (by simp)⟩

/-- `reduceTop`'s third block: `x6 := 64 c`, the steps to run. -/
theorem blkCnt_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {top : List Instr} {c : Nat}
    (hT : TopOk top B Z s.mem c) (hc : c < w) :
    WP isa (.block (ws ++ top ++ cntTail)) s fun t =>
    (t.gpr .x6 = BitVec.ofNat 64 (64 * c) ∧ t.gpr .x12 = BitVec.ofNat 64 w ∧
      t.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2)) ∧ t.mem = s.mem) ∧ Keep [.x11, .x12, .x3, .x13, .x6] s t := by
  have hw := h.w2
  simp only [List.append_assoc]
  refine WP.block_append_iff.mpr (WP.mono h.ws_ok fun t₁ ⟨⟨e12, e11, m₁', _⟩, k₁'⟩ => ?_)
  refine WP.block_append_iff.mpr (WP.mono (hT t₁ (h.scr.congr k₁'.wr) ((k₁'.gpr .x0 (by decide)).trans h.x0) (fun i hi => by
    rw [m₁'])) fun t₂ ⟨⟨e13, m₂', _⟩, k₂'⟩ => ?_)
  refine WP.mono (WP.keep [.x6] (Q := fun t => t.gpr .x6 = BitVec.ofNat 64 (64 * c) ∧ t.mem = t₂.mem) (by
    unfold cntTail
    brun [e13, shl_ofNat (show c * 2 ^ 6 < 2 ^ 64 by omega_arith)]
    rw [show c * 2 ^ 6 = 64 * c by omega_arith]) (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨g6, mt⟩, kt⟩ => ?_
  exact ⟨⟨g6, (kt.gpr .x12 (by decide)).trans ((k₂'.gpr .x12 (by decide)).trans e12),
    (kt.gpr .x11 (by decide)).trans ((k₂'.gpr .x11 (by decide)).trans e11), mt.trans (m₂'.trans m₁')⟩,
    ((k₁'.trans k₂').trans kt).mono (by simp)⟩

/-- `reduceTop`'s loop: `64 c` steps of `divmod` on `[aRem]` and `[aQ]`. -/
theorem stepsTop_ok {s : State} {B : Addr} {Z w c : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (h12 : s.gpr .x12 = BitVec.ofNat 64 w) (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2))) (hw1 : 1 ≤ w)
    (hw : w < 2 ^ 24) (hZ : slot w 16 ≤ Z) (hc1 : 1 ≤ c) (hc : c < w) (h6 : s.gpr .x6 = BitVec.ofNat 64 (64 * c)) :
    WP isa (.loop (VG.Impl.Rsa.AArch64.Keys.divStep aQ aRem aM aT) (.nonzero .x .x6)) s fun t =>
      t.gpr .x0 = B ∧ Frm B [ar w aQ, ar w aRem, ar w aT] s.mem t.mem ∧ Keep stepRegs s t ∧
      (wv s.mem B (slot w aRem) (w + 1) < wv s.mem B (slot w aM) w →
        (wv t.mem B (slot w aRem) (w + 1), wv t.mem B (slot w aQ) w) =
          VG.Proof.Rsa.divIter (wv s.mem B (slot w aM) w) (64 * w) (64 * c)
            (wv s.mem B (slot w aRem) (w + 1), wv s.mem B (slot w aQ) w)) := by
  have hn := hs.nowrap
  refine WP.mono (wp_countdown (N := 64 * c) (by omega_arith) (by omega_arith)
    (fun j t => Scr t B Z ∧ t.gpr .x0 = B ∧ t.gpr .x12 = BitVec.ofNat 64 w ∧
      t.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2)) ∧ Frm B [ar w aQ, ar w aRem, ar w aT] s.mem t.mem ∧
      Keep stepRegs s t ∧
      (wv s.mem B (slot w aRem) (w + 1) < wv s.mem B (slot w aM) w →
        (wv t.mem B (slot w aRem) (w + 1), wv t.mem B (slot w aQ) w) =
          VG.Proof.Rsa.divIter (wv s.mem B (slot w aM) w) (64 * w) j
            (wv s.mem B (slot w aRem) (w + 1), wv s.mem B (slot w aQ) w)))
    (fun j hj t ⟨hsT, h0T, h12T, h11T, fT, kT, vT⟩ _ => ?_)
    ⟨hs, h0, h12, h11, Frm.refl _ _ _, Keep.refl _ _, fun _ => rfl⟩ h6)
    fun t ⟨_, h0T, _, _, fT, kT, vT⟩ => ⟨h0T, fT, kT, vT⟩
  have hDt : wv t.mem B (slot w aM) w = wv s.mem B (slot w aM) w :=
    fT.wv_eq (fun r hr => by
      have := slot_lt (w := w) (show aM < 16 by decide)
      have pQM := slot_lt (w := w) (show aM < aQ by decide)
      have pRM := slot_lt (w := w) (show aM < aRem by decide)
      have pTM := slot_lt (w := w) (show aM < aT by decide)
      simp at hr; rcases hr with rfl | rfl | rfl <;> dsimp only <;> omega_arith) (by
      have := slot_lt (w := w) (show aM < 16 by decide); omega_arith)
  refine WP.mono (divStepCode_ok hsT h0T h12T h11T hw1 hw hZ (iQ := aQ) (iR := aRem) (iD := aM) (iT := aT)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)) fun t' ⟨h6', f', k', hv'⟩ => ⟨?_, h6'⟩
  refine ⟨hsT.congr k'.wr, (k'.gpr .x0 (by decide)).trans h0T, (k'.gpr .x12 (by decide)).trans h12T,
    (k'.gpr .x11 (by decide)).trans h11T, fT.trans f', (kT.trans k').mono (by simp [stepRegs]), fun hR0 => ?_⟩
  obtain ⟨q, hlt, -, -, -⟩ := VG.Proof.Rsa.divIter_from hR0 (wv_lt s.mem B (slot w aQ) w) j (by omega_arith)
  have hv := vT hR0
  have hRt : wv t.mem B (slot w aRem) (w + 1) < wv t.mem B (slot w aM) w := by
    rw [hDt, show wv t.mem B (slot w aRem) (w + 1) = _ from congrArg Prod.fst hv]; exact hlt
  rw [hv' hRt, hDt, hv]
  rfl

/-- `reduceTop top`: `[aA] mod [aM]` into `[aRem]` when the words of `[aA]`
from `c` up are below `[aM]`. -/
theorem reduceTop_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {top : List Instr} {c : Nat}
    (hT : TopOk top B Z s.mem c) (hc1 : 1 ≤ c) (hc : c < w) :
    WP isa (seqs (reduceTop top)) s fun t =>
      t.gpr .x0 = B ∧ Frm B [ar w aQ, ar w aRem, ar w aT] s.mem t.mem ∧ Keep topRegs s t ∧
      (wv s.mem B (slot w aA) w / 2 ^ (64 * c) < wv s.mem B (slot w aM) w →
        wv t.mem B (slot w aRem) (w + 1) = wv s.mem B (slot w aA) w % wv s.mem B (slot w aM) w) := by
  have hs := h.scr
  have hn := hs.nowrap
  have hZ := h.hZ
  have hw1 : 1 ≤ w := by have := h.w1; omega_arith
  have hw := h.w2
  have sA := h.sl (show aA < 16 by decide)
  have sR := h.sl (show aRem < 16 by decide)
  have sQ := h.sl (show aQ < 16 by decide)
  have sM := h.sl (show aM < 16 by decide)
  have sT := h.sl (show aT < 16 by decide)
  have pAR := slot_lt (w := w) (show aA < aRem by decide)
  have pAQ := slot_lt (w := w) (show aA < aQ by decide)
  have pRQ := slot_lt (w := w) (show aRem < aQ by decide)
  have pRM := slot_lt (w := w) (show aM < aRem by decide)
  have pQM := slot_lt (w := w) (show aM < aQ by decide)
  have pTA := slot_lt (w := w) (show aA < aT by decide)
  have pTM := slot_lt (w := w) (show aM < aT by decide)
  have hH : ∀ j < 16, ∀ i < 32, 8 * i + 8 ≤ slot w j := fun j hj i hi => by
    have := hdr_lt_slot w j hi; omega_arith
  have hmut : ∀ j, Mut (slot w j, 8 * (w + 2)) := fun j => Mut.ofSlot _ _ _
  simp only [reduceTop, seqs]
  -- `[aRem] := 0`.
  refine WP.seq (WP.mono (zeroA_ok h (j := aRem) (by decide)) fun s₁ ⟨z₁, o₁, _, _, _, k₁⟩ => ?_)
  have h₁ : Ws s₁ B Z w := h.congr (Frm.of_outside o₁ (List.mem_singleton_self _))
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact hmut _) k₁ (by decide)
  -- `[aQ] := 0`.
  refine WP.seq (WP.mono (zeroA_ok h₁ (j := aQ) (by decide)) fun s₂ ⟨z₂, o₂, _, _, _, k₂⟩ => ?_)
  have h₂ : Ws s₂ B Z w := h₁.congr (Frm.of_outside o₂ (List.mem_singleton_self _))
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact hmut _) k₂ (by decide)
  have hdr₂ : ∀ i < 32, word s₂.mem B (8 * i) = word s.mem B (8 * i) := fun i hi => by
    rw [o₂.word (.inl (hH aQ (by decide) i hi)) (by omega_arith), o₁.word (.inl (hH aRem (by decide) i hi))
        (by omega_arith)]
  have A₂ : wv s₂.mem B (slot w aA) w = wv s.mem B (slot w aA) w := by
    rw [o₂.wv (by omega_arith) (by omega_arith), o₁.wv (by omega_arith) (by omega_arith)]
  have M₂ : wv s₂.mem B (slot w aM) w = wv s.mem B (slot w aM) w := by
    rw [o₂.wv (by omega_arith) (by omega_arith), o₁.wv (by omega_arith) (by omega_arith)]
  have R₂ : wv s₂.mem B (slot w aRem) (w + 2) = 0 := by rw [o₂.wv (by omega_arith) (by omega_arith)]; exact z₁
  -- The words of `[aA]` from `c` up into `[aRem]`.
  have hblk₃ := blkHi_ok h₂ (fun t hs h0 hh => hT t hs h0 fun i hi => (hh i hi).trans (hdr₂ i hi)) hc
  refine WP.seq (WP.seq (WP.mono hblk₃ fun s₃ ⟨⟨e16, e17, e12, m₃⟩, k₃⟩ => ?_))
  have hs₃ := h₂.scr.congr k₃.wr
  refine WP.mono (copyWords_ok e16 e17 e12 (by omega_arith) (by omega_arith) (by omega_arith)
    (fun i hi => hs₃.ld (by omega_arith)) (fun i hi => hs₃.st (by omega_arith))
    (fun i hi b hb => by rw [ofs_off B (by omega_arith)]; omega_arith)) fun s₄ ⟨v₄, _, o₄, _, _, k₄⟩ => ?_
  rw [m₃] at v₄ o₄
  have h₄ : Ws s₄ B Z w := h₂.congr (Frm.of_outside o₄ (List.mem_singleton_self _))
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact Mut.ofSlot _ _ _) (k₃.trans k₄) (by decide)
  have hdr₄ : ∀ i < 32, word s₄.mem B (8 * i) = word s.mem B (8 * i) := fun i hi => by
    rw [o₄.word (.inl (hH aRem (by decide) i hi)) (by omega_arith), hdr₂ i hi]
  -- The low `c` words of `[aA]` to the top of `[aQ]`.
  have hblk₅ := blkLo_ok h₄ (fun t hs h0 hh => hT t hs h0 fun i hi => (hh i hi).trans (hdr₄ i hi)) hc
  refine WP.seq (WP.seq (WP.mono hblk₅ fun s₅ ⟨⟨e16', e17', e12', m₅⟩, k₅⟩ => ?_))
  have hs₅ := h₄.scr.congr k₅.wr
  refine WP.mono (copyWords_ok e16' e17' e12' hc1 (by omega_arith) (by omega_arith)
    (fun i hi => hs₅.ld (by omega_arith)) (fun i hi => hs₅.st (by omega_arith))
    (fun i hi b hb => by rw [ofs_off B (by omega_arith)]; omega_arith)) fun s₆ ⟨v₆, _, o₆, _, _, k₆⟩ => ?_
  rw [m₅] at v₆ o₆
  have h₆ : Ws s₆ B Z w := h₄.congr (Frm.of_outside o₆ (List.mem_singleton_self _))
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact Or.inl (by unfold slot hdrBytes; omega_arith)) (k₅.trans k₆)
        (by decide)
  have hdr₆ : ∀ i < 32, word s₆.mem B (8 * i) = word s.mem B (8 * i) := fun i hi => by
    rw [o₆.word (.inl (by have := hH aQ (by decide) i hi; omega_arith)) (by omega_arith), hdr₄ i hi]
  -- `x6 := 64 c`.
  have hblk₇ := blkCnt_ok h₆ (fun t hs h0 hh => hT t hs h0 fun i hi => (hh i hi).trans (hdr₆ i hi)) hc
  refine WP.seq (WP.mono hblk₇ fun s₇ ⟨⟨e6, e12₇, e11₇, m₇⟩, k₇⟩ => ?_)
  -- The values at the loop's start.
  have Rv : wv s₇.mem B (slot w aRem) (w + 1) = wv s.mem B (slot w aA) w / 2 ^ (64 * c) := by
    have hz : wv s₂.mem B (slot w aRem + 8 * (w - c)) (c + 1) = 0 :=
      wv_lo_zero (k := 1) (wv_hi_zero (n := w - c) (by rw [show w - c + (c + 1 + 1) = w + 2 by omega_arith]; exact R₂))
    have hD := wv_div_top (m := s.mem) (B := B) (d := slot w aA) (c := c) (n := w - c)
    rw [Nat.add_sub_cancel' hc.le] at hD
    rw [hD, m₇, o₆.wv (by omega_arith) (by omega_arith), show w + 1 = (w - c) + (c + 1) by omega_arith, wv_add, v₄,
      o₄.wv (by omega_arith) (by omega_arith), hz, Nat.mul_zero, Nat.add_zero, o₂.wv (by omega_arith) (by omega_arith),
      o₁.wv (by omega_arith) (by omega_arith)]
  have Qv : wv s₇.mem B (slot w aQ) w = wv s.mem B (slot w aA) w % 2 ^ (64 * c) * 2 ^ (64 * (w - c)) := by
    have hz : wv s₂.mem B (slot w aQ) (w - c) = 0 :=
      wv_lo_zero (k := c + 2) (by rw [show w - c + (c + 2) = w + 2 by omega_arith]; exact z₂)
    have hz₄ : wv s₄.mem B (slot w aQ) (w - c) = 0 := by rw [o₄.wv (by omega_arith) (by omega_arith)]; exact hz
    have A₄ : wv s₄.mem B (slot w aA) c = wv s.mem B (slot w aA) c := by
      rw [o₄.wv (by omega_arith) (by omega_arith), o₂.wv (by omega_arith) (by omega_arith), o₁.wv (by omega_arith)
          (by omega_arith)]
    have hM := wv_mod_low (m := s.mem) (B := B) (d := slot w aA) (c := c) (n := w - c)
    rw [Nat.add_sub_cancel' hc.le] at hM
    have hsplit := wv_add s₆.mem B (slot w aQ) (w - c) c
    rw [Nat.sub_add_cancel hc.le] at hsplit
    rw [hM, m₇, hsplit, o₆.wv (by omega_arith) (by omega_arith), hz₄, Nat.zero_add, v₆, A₄, Nat.mul_comm]
  have Mv : wv s₇.mem B (slot w aM) w = wv s.mem B (slot w aM) w := by
    rw [m₇, o₆.wv (by omega_arith) (by omega_arith), o₄.wv (by omega_arith) (by omega_arith), M₂]
  have k17 := ((((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k₆).trans k₇)
  -- The loop: `64 c` steps.
  refine WP.mono (stepsTop_ok (h₆.scr.congr k₇.wr) ((k₇.gpr .x0 (by decide)).trans h₆.x0) e12₇ e11₇ hw1 hw hZ
    hc1 (by omega_arith) e6) fun t ⟨h0T, fT, kT, vT⟩ => ⟨h0T, ?_, (k17.trans kT).mono (by simp [topRegs, stepRegs]),
      fun hlt => ?_⟩
  · have g4 : Outside B (slot w aRem) (8 * (w + 2)) s₂.mem s₄.mem := o₄.mono (by omega_arith) (by omega_arith)
    have g6 : Outside B (slot w aQ) (8 * (w + 2)) s₄.mem s₆.mem := o₆.mono (by omega_arith) (by omega_arith)
    rw [m₇] at fT
    exact ((((Frm.of_outside o₁ (by simp [ar])).trans (Frm.of_outside o₂ (by simp [ar]))).trans
      (Frm.of_outside g4 (by simp [ar]))).trans (Frm.of_outside g6 (by simp [ar]))).trans fT
  · have hR0 : wv s₇.mem B (slot w aRem) (w + 1) < wv s₇.mem B (slot w aM) w := by rw [Rv, Mv]; exact hlt
    have := congrArg Prod.fst (vT hR0)
    simp only at this
    rw [this, Qv, Rv, Mv, show 64 * (w - c) = 64 * w - 64 * c by omega_arith,
      VG.Proof.Rsa.divIter_top (by rw [← Mv, ← Rv]; exact hR0) (by omega_arith) (Nat.mod_lt _ (Nat.two_pow_pos _))]
    rw [Nat.mul_comm, Nat.div_add_mod]

end VG.Proof.Rsa.AArch64
