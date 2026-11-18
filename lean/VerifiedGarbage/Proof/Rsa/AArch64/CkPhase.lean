module

public import VerifiedGarbage.Impl.Rsa.AArch64.CheckKey
public import VerifiedGarbage.Proof.Rsa.AArch64.CkPhaseCore
public import VerifiedGarbage.Proof.Rsa.AArch64.CvTail
public import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Proof.Rsa.AArch64.Div
public import VerifiedGarbage.Impl.Rsa.AArch64.CheckCrtKey
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.AArch64.MulAdd
import Mathlib.Order.Defs.Prop
import Mathlib.Data.Int.ModEq

/-! ### `Rsa.AArch64.CrtKeyPhase`, which this module and modules that import it used -/

section

/-! ### `Rsa.AArch64.CrtKeyTop`, which this module and modules that import it used -/

section

/-!
# `vg_rsa_check_crt_key` on AArch64: the shortened remainder

`reduceTop top` (`Impl/Rsa/AArch64/CheckCrtKey.lean`): for `c` words (in
`x13` by `top`), `[aRem]` starts as the words of `[aA]` from `c` up and the
top `c` words of `[aQ]` as its low ones, then `64 c` of `divmod`'s steps.
When the words from `c` up are below the divisor, the remainder is that of
`[aA]` (`reduceTop_ok`, by `divIter_top`).
-/

@[expose] public section

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
  rw [wv_add] at h; omega_using [h]

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
  obtain f13 : t₄.gpr .x13 = BitVec.ofNat 64 c := ((k₃'.trans k₄').gpr .x13 (by decide)).trans e13
  obtain f16 : t₄.gpr .x16 = off B (slot w aA) := (k₄'.gpr .x16 (by decide)).trans e16
  obtain f12 : t₄.gpr .x12 = BitVec.ofNat 64 w := (((k₂'.trans k₃').trans k₄').gpr .x12 (by decide)).trans e12
  refine WP.mono (WP.keep [.x3, .x16, .x12] (Q := fun t => t.gpr .x16 = off B (slot w aA + 8 * c) ∧
      t.gpr .x12 = BitVec.ofNat 64 (w - c) ∧ t.mem = t₄.mem) (by
    unfold hiTail
    brun [f13, f16, f12, shl_ofNat (show c * 2 ^ 3 < 2 ^ 64 by omega_using [hc, hw]), off, VG.Offset.add_ofNat_add_ofNat,
      VG.Offset.ofNat_sub_ofNat (show c ≤ w by omega_using [hc])]
    rw [show c * 2 ^ 3 = 8 * c by omega_using []]) (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨g16, g12, mt⟩,
        kt⟩ => ?_
  exact ⟨⟨g16, (kt.gpr .x17 (by decide)).trans e17, g12, mt.trans (m₄'.trans (m₃'.trans (m₂'.trans m₁')))⟩,
    ((((k₁'.trans k₂').trans k₃').trans k₄').trans kt).mono (by decide)⟩

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
  obtain f13 : t₄.gpr .x13 = BitVec.ofNat 64 c := ((k₃'.trans k₄').gpr .x13 (by decide)).trans e13
  have f17 : t₄.gpr .x17 = off B (slot w aQ) := e17
  obtain f12 : t₄.gpr .x12 = BitVec.ofNat 64 w := (((k₂'.trans k₃').trans k₄').gpr .x12 (by decide)).trans e12
  refine WP.mono (WP.keep [.x3, .x17, .x12] (Q := fun t => t.gpr .x17 = off B (slot w aQ + 8 * (w - c)) ∧
      t.gpr .x12 = BitVec.ofNat 64 c ∧ t.mem = t₄.mem) (by
    unfold loTail
    brun [f13, f17, f12, VG.Offset.ofNat_sub_ofNat (show c ≤ w by omega_using [hc]),
      shl_ofNat (show (w - c) * 2 ^ 3 < 2 ^ 64 by omega_using [hw]), off, VG.Offset.add_ofNat_add_ofNat]
    rw [show (w - c) * 2 ^ 3 = 8 * (w - c)
        by omega_using []]) (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨g17, g12, mt⟩, kt⟩ => ?_
  exact ⟨⟨(kt.gpr .x16 (by decide)).trans ((k₄'.gpr .x16 (by decide)).trans e16), g17, g12,
    mt.trans (m₄'.trans (m₃'.trans (m₂'.trans m₁')))⟩, ((((k₁'.trans k₂').trans k₃').trans k₄').trans kt).mono (by decide)⟩

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
    brun [e13, shl_ofNat (show c * 2 ^ 6 < 2 ^ 64 by omega_using [hc, hw])]
    rw [show c * 2 ^ 6 = 64 * c by omega_using []]) (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨g6, mt⟩, kt⟩ => ?_
  exact ⟨⟨g6, (kt.gpr .x12 (by decide)).trans ((k₂'.gpr .x12 (by decide)).trans e12),
    (kt.gpr .x11 (by decide)).trans ((k₂'.gpr .x11 (by decide)).trans e11), mt.trans (m₂'.trans m₁')⟩,
    ((k₁'.trans k₂').trans kt).mono (by decide)⟩

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
  refine WP.mono (wp_countdown (N := 64 * c) (by omega_using [hw, hc]) (by omega_using [hc1])
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
  obtain hDt : wv t.mem B (slot w aM) w = wv s.mem B (slot w aM) w :=
    fT.wv_eq (fun r hr => by
      have := slot_lt (w := w) (show aM < 16 by decide)
      obtain pQM := slot_lt (w := w) (show aM < aQ by decide)
      obtain pRM := slot_lt (w := w) (show aM < aRem by decide)
      obtain pTM := slot_lt (w := w) (show aM < aT by decide)
      simp at hr; rcases hr with rfl | rfl | rfl <;> dsimp only <;> omega_using [pQM, pRM, pTM]) (by
      have := slot_lt (w := w) (show aM < 16 by decide); omega_using [hZ, hn, this])
  refine WP.mono (divStepCode_ok hsT h0T h12T h11T hw1 hw hZ (iQ := aQ) (iR := aRem) (iD := aM) (iT := aT)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)) fun t' ⟨h6', f', k', hv'⟩ => ⟨?_, h6'⟩
  refine ⟨hsT.congr k'.wr, (k'.gpr .x0 (by decide)).trans h0T, (k'.gpr .x12 (by decide)).trans h12T,
    (k'.gpr .x11 (by decide)).trans h11T, fT.trans f', (kT.trans k').mono (by decide), fun hR0 => ?_⟩
  obtain ⟨q, hlt, -, -, -⟩ := VG.Proof.Rsa.divIter_from hR0 (wv_lt s.mem B (slot w aQ) w) j (by omega_using [hc, hj])
  obtain hv := vT hR0
  obtain hRt : wv t.mem B (slot w aRem) (w + 1) < wv t.mem B (slot w aM) w := by
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
  obtain hw1 : 1 ≤ w := by have := h.w1; omega_using [this]
  have hw := h.w2
  obtain sA := h.sl (show aA < 16 by decide)
  obtain sR := h.sl (show aRem < 16 by decide)
  obtain sQ := h.sl (show aQ < 16 by decide)
  obtain sM := h.sl (show aM < 16 by decide)
  obtain sT := h.sl (show aT < 16 by decide)
  obtain pAR := slot_lt (w := w) (show aA < aRem by decide)
  obtain pAQ := slot_lt (w := w) (show aA < aQ by decide)
  obtain pRQ := slot_lt (w := w) (show aRem < aQ by decide)
  obtain pRM := slot_lt (w := w) (show aM < aRem by decide)
  obtain pQM := slot_lt (w := w) (show aM < aQ by decide)
  obtain pTA := slot_lt (w := w) (show aA < aT by decide)
  obtain pTM := slot_lt (w := w) (show aM < aT by decide)
  obtain hH : ∀ j < 16, ∀ i < 32, 8 * i + 8 ≤ slot w j := fun j hj i hi => by
    have := hdr_lt_slot w j hi; omega_using [this]
  obtain hmut : ∀ j, Mut (slot w j, 8 * (w + 2)) := fun j => Mut.ofSlot _ _ _
  simp only [reduceTop, seqs]
  -- `[aRem] := 0`.
  refine WP.seq (WP.mono (zeroA_ok h (j := aRem) (by decide)) fun s₁ ⟨z₁, o₁, _, _, _, k₁⟩ => ?_)
  obtain h₁ : Ws s₁ B Z w := h.congr (Frm.of_outside o₁ (List.mem_singleton_self _))
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact hmut _) k₁ (by decide)
  -- `[aQ] := 0`.
  refine WP.seq (WP.mono (zeroA_ok h₁ (j := aQ) (by decide)) fun s₂ ⟨z₂, o₂, _, _, _, k₂⟩ => ?_)
  obtain h₂ : Ws s₂ B Z w := h₁.congr (Frm.of_outside o₂ (List.mem_singleton_self _))
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact hmut _) k₂ (by decide)
  obtain hdr₂ : ∀ i < 32, word s₂.mem B (8 * i) = word s.mem B (8 * i) := fun i hi => by
    rw [o₂.word (.inl (hH aQ (by decide) i hi)) (by omega_using [hi]), o₁.word (.inl (hH aRem (by decide) i hi))
        (by omega_using [hi])]
  obtain A₂ : wv s₂.mem B (slot w aA) w = wv s.mem B (slot w aA) w := by
    rw [o₂.wv (by omega_using [pAQ]) (by omega_using [hn, sT, pTA]), o₁.wv (by omega_using [pAR]) (by omega_using [hn, sT, pTA])]
  obtain M₂ : wv s₂.mem B (slot w aM) w = wv s.mem B (slot w aM) w := by
    rw [o₂.wv (by omega_using [pQM]) (by omega_using [hn, sT, pTM]), o₁.wv (by omega_using [pRM]) (by omega_using [hn, sT, pTM])]
  obtain R₂ : wv s₂.mem B (slot w aRem) (w + 2) = 0 := by rw [o₂.wv (by omega_using [pRQ]) (by omega_using [hn, sQ, pRQ])]; exact z₁
  -- The words of `[aA]` from `c` up into `[aRem]`.
  obtain hblk₃ := blkHi_ok h₂ (fun t hs h0 hh => hT t hs h0 fun i hi => (hh i hi).trans (hdr₂ i hi)) hc
  refine WP.seq (WP.seq (WP.mono hblk₃ fun s₃ ⟨⟨e16, e17, e12, m₃⟩, k₃⟩ => ?_))
  obtain hs₃ := h₂.scr.congr k₃.wr
  refine WP.mono (copyWords_ok e16 e17 e12 (by omega_using [hc]) (by omega_using [hw]) (by omega_using [hn, sQ, pRQ])
    (fun i hi => hs₃.ld (by omega_using [sT, pTA, hi])) (fun i hi => hs₃.st (by omega_using [sQ, pRQ, hi]))
    (fun i hi b hb => by rw [ofs_off B (by omega_using [hn, sT, pTA, hi, hb])]; omega_using [pAR, hi, hb])) fun s₄ ⟨v₄, _, o₄, _, _, k₄⟩ => ?_
  rw [m₃] at v₄ o₄
  obtain h₄ : Ws s₄ B Z w := h₂.congr (Frm.of_outside o₄ (List.mem_singleton_self _))
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact Mut.ofSlot _ _ _) (k₃.trans k₄) (by decide)
  obtain hdr₄ : ∀ i < 32, word s₄.mem B (8 * i) = word s.mem B (8 * i) := fun i hi => by
    rw [o₄.word (.inl (hH aRem (by decide) i hi)) (by omega_using [hi]), hdr₂ i hi]
  -- The low `c` words of `[aA]` to the top of `[aQ]`.
  obtain hblk₅ := blkLo_ok h₄ (fun t hs h0 hh => hT t hs h0 fun i hi => (hh i hi).trans (hdr₄ i hi)) hc
  refine WP.seq (WP.seq (WP.mono hblk₅ fun s₅ ⟨⟨e16', e17', e12', m₅⟩, k₅⟩ => ?_))
  obtain hs₅ := h₄.scr.congr k₅.wr
  refine WP.mono (copyWords_ok e16' e17' e12' hc1 (by omega_using [hc, hw]) (by omega_using [hc, hn, sQ])
    (fun i hi => hs₅.ld (by omega_using [hc, sT, pTA, hi])) (fun i hi => hs₅.st (by omega_using [hc, sQ, hi]))
    (fun i hi b hb => by rw [ofs_off B (by omega_using [hc, hn, sT, pTA, hi, hb])]; omega_using [hc, pAQ, hi, hb])) fun s₆ ⟨v₆, _, o₆, _, _, k₆⟩ => ?_
  rw [m₅] at v₆ o₆
  obtain h₆ : Ws s₆ B Z w := h₄.congr (Frm.of_outside o₆ (List.mem_singleton_self _))
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact Or.inl (by unfold slot hdrBytes; omega_using [])) (k₅.trans k₆)
        (by decide)
  obtain hdr₆ : ∀ i < 32, word s₆.mem B (8 * i) = word s.mem B (8 * i) := fun i hi => by
    rw [o₆.word (.inl (by have := hH aQ (by decide) i hi; omega_using [this])) (by omega_using [hi]), hdr₄ i hi]
  -- `x6 := 64 c`.
  obtain hblk₇ := blkCnt_ok h₆ (fun t hs h0 hh => hT t hs h0 fun i hi => (hh i hi).trans (hdr₆ i hi)) hc
  refine WP.seq (WP.mono hblk₇ fun s₇ ⟨⟨e6, e12₇, e11₇, m₇⟩, k₇⟩ => ?_)
  -- The values at the loop's start.
  obtain Rv : wv s₇.mem B (slot w aRem) (w + 1) = wv s.mem B (slot w aA) w / 2 ^ (64 * c) := by
    obtain hz : wv s₂.mem B (slot w aRem + 8 * (w - c)) (c + 1) = 0 :=
      wv_lo_zero (k := 1) (wv_hi_zero (n := w - c) (by rw [show w - c + (c + 1 + 1) = w + 2 by omega_using [hc]]; exact R₂))
    obtain hD := wv_div_top (m := s.mem) (B := B) (d := slot w aA) (c := c) (n := w - c)
    rw [Nat.add_sub_cancel' hc.le] at hD
    rw [hD, m₇, o₆.wv (by omega_using [pRQ]) (by omega_using [hn, sQ, pRQ]), show w + 1 = (w - c) + (c + 1) by omega_using [hc], wv_add, v₄,
      o₄.wv (by omega_using []) (by omega_using [hc, hn, sQ, pRQ]), hz, Nat.mul_zero, Nat.add_zero, o₂.wv (by omega_using [hc, pAQ]) (by omega_using [hc, hn, sT, pTA]),
      o₁.wv (by omega_using [hc, pAR]) (by omega_using [hc, hn, sT, pTA])]
  obtain Qv : wv s₇.mem B (slot w aQ) w = wv s.mem B (slot w aA) w % 2 ^ (64 * c) * 2 ^ (64 * (w - c)) := by
    obtain hz : wv s₂.mem B (slot w aQ) (w - c) = 0 :=
      wv_lo_zero (k := c + 2) (by rw [show w - c + (c + 2) = w + 2 by omega_using [hc]]; exact z₂)
    obtain hz₄ : wv s₄.mem B (slot w aQ) (w - c) = 0 := by rw [o₄.wv (by omega_using [pRQ]) (by omega_using [hn, sQ])]; exact hz
    obtain A₄ : wv s₄.mem B (slot w aA) c = wv s.mem B (slot w aA) c := by
      rw [o₄.wv (by omega_using [hc, pAR]) (by omega_using [hc, hn, sT, pTA]), o₂.wv (by omega_using [hc, pAQ]) (by omega_using [hc, hn, sT, pTA]), o₁.wv (by omega_using [hc, pAR])
          (by omega_using [hc, hn, sT, pTA])]
    obtain hM := wv_mod_low (m := s.mem) (B := B) (d := slot w aA) (c := c) (n := w - c)
    rw [Nat.add_sub_cancel' hc.le] at hM
    obtain hsplit := wv_add s₆.mem B (slot w aQ) (w - c) c
    rw [Nat.sub_add_cancel hc.le] at hsplit
    rw [hM, m₇, hsplit, o₆.wv (by omega_using []) (by omega_using [hn, sQ]), hz₄, Nat.zero_add, v₆, A₄, Nat.mul_comm]
  obtain Mv : wv s₇.mem B (slot w aM) w = wv s.mem B (slot w aM) w := by
    rw [m₇, o₆.wv (by omega_using [pQM]) (by omega_using [hn, sT, pTM]), o₄.wv (by omega_using [pRM]) (by omega_using [hn, sT, pTM]), M₂]
  obtain k17 := ((((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k₆).trans k₇)
  -- The loop: `64 c` steps.
  refine WP.mono (stepsTop_ok (h₆.scr.congr k₇.wr) ((k₇.gpr .x0 (by decide)).trans h₆.x0) e12₇ e11₇ hw1 hw hZ
    hc1 (by omega_using [hc]) e6) fun t ⟨h0T, fT, kT, vT⟩ => ⟨h0T, ?_, (k17.trans kT).mono (by decide),
      fun hlt => ?_⟩
  · have g4 : Outside B (slot w aRem) (8 * (w + 2)) s₂.mem s₄.mem := o₄.mono (by omega_using []) (by omega_using [])
    obtain g6 : Outside B (slot w aQ) (8 * (w + 2)) s₄.mem s₆.mem := o₆.mono (by omega_using []) (by omega_using [hc])
    rw [m₇] at fT
    exact ((((Frm.of_outside o₁ (by simp [ar])).trans (Frm.of_outside o₂ (by simp [ar]))).trans
      (Frm.of_outside g4 (by simp [ar]))).trans (Frm.of_outside g6 (by simp [ar]))).trans fT
  · have hR0 : wv s₇.mem B (slot w aRem) (w + 1) < wv s₇.mem B (slot w aM) w := by rw [Rv, Mv]; exact hlt
    have := congrArg Prod.fst (vT hR0)
    simp only at this
    rw [this, Qv, Rv, Mv, show 64 * (w - c) = 64 * w - 64 * c by omega_using [],
      VG.Proof.Rsa.divIter_top (by rw [← Mv, ← Rv]; exact hR0) (by omega_using [hc]) (Nat.mod_lt _ (Nat.two_pow_pos _))]
    rw [Nat.mul_comm, Nat.div_add_mod]

end VG.Proof.Rsa.AArch64

end

end

/-!
# `vg_rsa_check_key` on AArch64: the shortened remainder

`reduceTop` (`ckReduceTop_ok`), the remainder `wmodOne` takes when
`wordGuard` fails (`Proof/Rsa/AArch64/CkPhase.lean`), and its counts of
quotient words (`topE_ok`, `topQ_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Rsa.AArch64.CheckKey (sQlen aM aA aRem aT)
open VG.Impl.Rsa.AArch64.CheckCrtKey (aQ reduceTop topE topQ)
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- `reduceTop top`: the remainder of `[aA]` by `[aM]` into `[aRem]`, when
the words of `[aA]` from `c` up are below `[aM]`. -/
theorem ckReduceTop_ok {I : CkIn} {m₀ : Mem} {s : State} (h : CkS I m₀ s) {top : List Instr} {c : Nat}
    (hT : TopOk top I.B I.Z s.mem c) (hc1 : 1 ≤ c) (hc : c < wW I.cap) :
    WP isa (seqs (reduceTop top)) s fun t =>
      CkS I m₀ t ∧ mword t.mem I.B = mword s.mem I.B ∧
      (I.av s.mem aA / 2 ^ (64 * c) < I.av s.mem aM → I.av t.mem aRem = I.av s.mem aA % I.av s.mem aM) ∧
      ∀ i < 16, i ≠ aRem → i ≠ aQ → i ≠ aT → I.av t.mem i = I.av s.mem i := by
  have hn := h.ws.scr.nowrap
  refine WP.mono (reduceTop_ok h.ws hT hc1 hc) fun t ⟨_, f, k, hv⟩ => ?_
  have hr : ∀ r ∈ [ar (wW I.cap) aQ, ar (wW I.cap) aRem, ar (wW I.cap) aT], ∃ j < 16, r = ar (wW I.cap) j := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨aQ, by decide, rfl⟩
    · exact ⟨aRem, by decide, rfl⟩
    · exact ⟨aT, by decide, rfl⟩
  refine ⟨h.step f (fun r hr' => by obtain ⟨j, _, rfl⟩ := hr r hr'; exact Mut.ofSlot _ _ _)
    (fun r hr' => by obtain ⟨j, hj, rfl⟩ := hr r hr'; exact h.ws.sl hj) k (by decide), ?_, fun hlt => ?_,
    fun i hi h1 h2 h3 => ?_⟩
  · exact f.word_eq (fun r hr' => by
      obtain ⟨j, hj, rfl⟩ := hr r hr'
      have := hdr_lt_slot (wW I.cap) j (show Public.sMask < 32 by decide); exact Or.inl (by omega_using [this]))
      (by simp only [Public.sMask, sFn]; omega_using [])
  · have hM : 0 < I.av s.mem aM := Nat.lt_of_le_of_lt (Nat.zero_le _) hlt
    have hr' := hv hlt
    have hlt' : wv t.mem I.B (slot (wW I.cap) aRem) (wW I.cap + 1) < 2 ^ (64 * wW I.cap) := by
      rw [hr']; exact Nat.lt_of_lt_of_le (Nat.mod_lt _ hM) (Nat.le_of_lt (wv_lt _ _ _ _))
    unfold CkIn.av
    rw [wv_low_of_lt (v := wW I.cap) (w := wW I.cap + 1) (by omega_using []) hlt', hr']
  · exact f.wv_eq (fun r hr' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl <;> dsimp only
      · have := slot_sep (w := wW I.cap) h2; omega_using [this]
      · have := slot_sep (w := wW I.cap) h1; omega_using [this]
      · have := slot_sep (w := wW I.cap) h3; omega_using [this]) (by have := h.ws.sl hi; omega_using [hn, this])

/-- `topE`: `x13 := 1`. -/
theorem topE_ok (B : Addr) (Z : Nat) (m₀ : Mem) : TopOk topE B Z m₀ 1 := fun t _ _ _ =>
  WP.mono (WP.keep [.x13] (Q := fun t' => t'.gpr .x13 = BitVec.ofNat 64 1 ∧ t'.mem = t.mem ∧ t'.c = t.c)
    (by unfold topE; brun) (by decide) (by decide) (by decide +kernel)) fun _ ⟨h, k⟩ => ⟨h, k.mono (by simp)⟩

/-- `topQ`: `x13 := ⌈q_len / 8⌉`, from the header slot of `q_len`. -/
theorem topQ_ok {B : Addr} {Z : Nat} {m₀ : Mem} {ql : Nat} (hq : word m₀ B (8 * sQlen) = BitVec.ofNat 64 ql)
    (hql : ql < 2 ^ 32) (hZ : 8 * 32 ≤ Z) : TopOk topQ B Z m₀ ((ql + 7) / 8) := fun t hs h0 hh => by
  have hl := hs.ld (d := 8 * sQlen) (by simp only [sQlen, sFn]; omega_using [hZ])
  refine WP.mono (WP.keep [.x13] (Q := fun t' => t'.gpr .x13 = BitVec.ofNat 64 ((ql + 7) / 8) ∧ t'.mem = t.mem ∧
    t'.c = t.c) ?_ (by decide) (by decide) (by decide +kernel)) fun _ ⟨h, k⟩ => ⟨h, k.mono (by simp)⟩
  unfold topQ
  brun [h0, hl, hh sQlen (by decide), hq, BitVec.ofNat_add_ofNat, shr_ofNat (show ql + 7 < 2 ^ 64 by omega_using [hql])]

/-- A product by a number below `2^(64 k)`, shifted down by `64 k` bits, is at
most the other factor. -/
theorem mul_div_top_le {a b k : Nat} (hb : b < 2 ^ (64 * k)) : a * b / 2 ^ (64 * k) ≤ a :=
  Nat.div_le_of_le_mul (by rw [Nat.mul_comm (2 ^ _)]; exact Nat.mul_le_mul_left a (Nat.le_of_lt hb))

end VG.Proof.Rsa.AArch64

end

end

/-! ### `Rsa.KeyBounds`, which only this module used -/

section

/-! # Bounds for the full private exponent in RSA key validation -/

@[expose] public section

namespace VG.Proof.Rsa

/-- A bound expressed only through the other factor's public byte length. -/
theorem fullExp_bound {e d x y L : Nat} (he : e < 2 ^ 33) (hx : 2 ≤ x)
    (hd : d < x * y) (hy : y < 2 ^ (64 * ((L + 7) / 8))) :
    e * d < 2 ^ (64 * ((L + 7) / 8 + 1)) * (x - 1) := by
  obtain hx' : x ≤ 2 * (x - 1) := by omega_using [hx]
  obtain hxy : x * y ≤ 2 * (x - 1) * y := Nat.mul_le_mul_right y hx'
  obtain hed : e * d ≤ e * (2 * (x - 1) * y) := Nat.mul_le_mul_left e (by omega_using [hd, hxy])
  obtain hey : e * y < 2 ^ 33 * 2 ^ (64 * ((L + 7) / 8)) := Nat.mul_lt_mul_of_lt_of_lt he hy
  obtain hsmall : 2 * (2 ^ 33 * 2 ^ (64 * ((L + 7) / 8))) ≤ 2 ^ (64 * ((L + 7) / 8 + 1)) := by
    rw [Nat.mul_add, Nat.mul_one, Nat.pow_add]
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      Nat.mul_le_mul_right (2 ^ (64 * ((L + 7) / 8))) (show 2 * 2 ^ 33 ≤ (2 : Nat) ^ 64 by decide)
  obtain hpos : 0 < x - 1 := by omega_using [hx]
  calc e * d ≤ (2 * (e * y)) * (x - 1) := by simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hed
    _ < (2 * (2 ^ 33 * 2 ^ (64 * ((L + 7) / 8)))) * (x - 1) :=
      Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_left hey (by decide)) hpos
    _ ≤ _ := Nat.mul_le_mul_right _ hsmall

end VG.Proof.Rsa

end

end


/-!
# `vg_rsa_check_key` on AArch64: the phases of `main`

`KS c`: `CkS`, the mask `c`, and `n`, `e` and 1 in their arrays. Each phase
of the checks and'es its conditions into the mask (`phDN_ok`, `phPQ_ok`,
`phMod_ok`, `phQIC_ok`), exactly when the facts the key's other checks give
hold.
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG.Impl.Rsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.CheckKey
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- The full-exponent quotient count comes from the other factor's length. -/
theorem topD_ok {B : Addr} {Z sl : Nat} {m₀ : Mem} {yl : Nat} (hsl : sl < 32)
    (hy : word m₀ B (8 * sl) = BitVec.ofNat 64 yl) (hyl : yl < 2 ^ 32) (hZ : 8 * 32 ≤ Z) :
    TopOk (topD sl) B Z m₀ ((yl + 7) / 8 + 1) := fun t hs h0 hh => by
  obtain hl := hs.ld (d := 8 * sl) (by omega_arith)
  refine WP.mono (WP.keep [.x13] (Q := fun t' => t'.gpr .x13 = BitVec.ofNat 64 ((yl + 7) / 8 + 1) ∧
    t'.mem = t.mem ∧ t'.c = t.c) ?_ (by rfl) (by rfl) (by rfl)) fun _ ⟨h, k⟩ => ⟨h, k.mono (by simp)⟩
  unfold topD
  brun [hdr_enc hsl, h0, hl, hh sl hsl, hy, BitVec.ofNat_add_ofNat, shr_ofNat (show yl + 7 < 2 ^ 64 by omega_arith)]

/-! ## `wmodOne`: the remainder by words when `wordGuard` passes -/

/-- `wM`: `w_m = (W - 2) / 4`. -/
theorem ckWm_ok (w : Nat) (hw2 : 2 ≤ w) (hw : w < 2 ^ 24) : WmOk wM w ((w - 2) / 4) := fun t h12 => by
  refine WP.keep [.x12] (Q := fun t' => t'.gpr .x12 = BitVec.ofNat 64 ((w - 2) / 4) ∧ t'.mem = t.mem)
    ?_ (by decide) (by decide) (by decide +kernel)
  unfold wM
  brun [h12, bv_sub_ofNat hw2 (by omega_arith), shr_ofNat (show w - 2 < 2 ^ 64 by omega_arith)]

/-- `L = W / 2` words of `e d`. -/
theorem ckLenD_ok (w : Nat) (hw : w < 2 ^ 24) : LenOk lenD w (w / 2) := fun t h12 =>
  WP.keep [.x13] (Q := fun t' => t'.gpr .x13 = BitVec.ofNat 64 (w / 2) ∧ t'.mem = t.mem)
    (by unfold lenD; brun [h12, shr_ofNat (show w < 2 ^ 64 by omega_arith)]) (by decide) (by decide) (by decide +kernel)

/-- `L = w_m + 1` words of `e dX`. -/
theorem ckLenE_ok (w : Nat) (hw2 : 2 ≤ w) (hw : w < 2 ^ 24) :
    LenOk lenE w ((w - 2) / 4 + 1) := fun t h12 =>
  WP.keep [.x13] (Q := fun t' => t'.gpr .x13 = BitVec.ofNat 64 ((w - 2) / 4 + 1) ∧ t'.mem = t.mem)
    (by unfold lenE; brun [h12, bv_sub_ofNat hw2 (by omega_arith), shr_ofNat (show w - 2 < 2 ^ 64 by omega_arith),
      BitVec.ofNat_add_ofNat]) (by decide) (by decide) (by decide +kernel)

/-- `L = 2 w_m` words of `q qInv`. -/
theorem ckLenQ_ok (w : Nat) (hw2 : 2 ≤ w) (hw : w < 2 ^ 24) :
    LenOk lenQ w ((w - 2) / 2) := fun t h12 =>
  WP.keep [.x13] (Q := fun t' => t'.gpr .x13 = BitVec.ofNat 64 ((w - 2) / 2) ∧ t'.mem = t.mem)
    (by unfold lenQ; brun [h12, bv_sub_ofNat hw2 (by omega_arith), shr_ofNat (show w - 2 < 2 ^ 64 by omega_arith)])
    (by decide) (by decide) (by decide +kernel)

/-- `aBase`: `[aA]`'s word `-1`, an array below `[aRem]`, for `W = 4 w_m + 2`. -/
theorem ckXb_ok (B : Addr) (w : Nat) (hw : w % 4 = 2) (hw' : w < 2 ^ 24) :
    XbOk aBase B (slot w aRem) (slot w aA) ((w - 2) / 4) := fun t h11 h12 => by
  obtain e : off B (slot w aA - 8) + BitVec.ofNat 64 (32 * ((w - 2) / 4) + 40) = off B (slot w aRem) := by
    rw [off_add]; congr 1; simp only [slot, aA, aRem]; omega_arith
  refine WP.keep [.x16] (Q := fun t' => t'.gpr .x16 = off B (slot w aA - 8) ∧ t'.mem = t.mem)
    ?_ (by decide) (by decide) (by decide +kernel)
  unfold aBase
  brun [h11, h12, shl5_ofNat (show (w - 2) / 4 < 2 ^ 58 by omega_arith)]
  rw [← e, BitVec.ofNat_add]
  exact BitVec.add_sub_cancel _ _

/-- The guard and its two paths: `[aRem] := [aA] mod [aM]`, when the words
of `[aA]` from `c` up are below `[aM]` and, if `wordGuard` passes, `[aA]`
fits in `L` words and `[aM]` in `w_m = k / 16` with its top bit set. -/
theorem ckWRem_ok {I : CkIn} {m₀ : Mem} {s : State} (h : CkS I m₀ s) (L : CkLens I)
    {top : List Instr} {c : Nat} (hT : TopOk top I.B I.Z s.mem c) (hc1 : 1 ≤ c) (hcw : c < wW I.cap)
    {lenL : List Instr} {Ln : Nat} (hL : LenOk lenL (wW I.cap) Ln) (hLW : Ln ≤ wW I.cap) (hmL : wk I.k / 2 ≤ Ln) :
    WP isa (.seq (.block (wordGuard sPlen sQlen)) (.ite (.zero .x .x9) (wdiv aA aM aRem CheckKey.aT wM lenL aBase)
      (seqs (CheckCrtKey.reduceTop top)))) s fun t =>
      CkS I m₀ t ∧ mword t.mem I.B = mword s.mem I.B ∧
      (I.av s.mem aA / 2 ^ (64 * c) < I.av s.mem aM →
        (I.Gd → I.av s.mem aA < 2 ^ (64 * Ln) ∧ 2 ^ (64 * (wk I.k / 2) - 1) ≤ I.av s.mem aM ∧
          I.av s.mem aM < 2 ^ (64 * (wk I.k / 2))) →
        I.av t.mem aRem = I.av s.mem aA % I.av s.mem aM) ∧
      ∀ i < 16, i ≠ aRem → i ≠ CheckCrtKey.aQ → i ≠ CheckKey.aT → I.av t.mem i = I.av s.mem i := by
  have hk1 := L.k1
  have hk2 := L.k2
  have hpl := L.pl2
  have hql := L.ql2
  have hn := h.ws.scr.nowrap
  have h256 := h.ws.h256
  obtain hn0 : 0 < I.nb.length := by rw [L.nl]; omega_arith
  refine WP.seq (WP.mono (wordGuard_ok (b := s.mem.read I.pN 1) h.ws.scr h.ws.x0 h256 (by decide) (by decide)
    h.args.k h.args.pl h.args.ql h.args.n rfl (by simpa using h.n.rd 0 hn0)) fun s₁ ⟨⟨h9, m₁⟩, k₁⟩ => ?_)
  obtain h₁ := h.step (rs := []) (by rw [m₁]; exact Frm.refl _ _ _) (by simp) (by simp) k₁ (by decide)
  obtain e₁ : ∀ i, I.av s₁.mem i = I.av s.mem i := fun i => by unfold CkIn.av; rw [m₁]
  refine WP.ite (s₁.gpr .x9 == 0) (VG.Proof.MlKem.AArch64.eval_zero _ _) (fun hb => ?_) (fun _ => ?_)
  · -- The guard passes: `wdiv`.
    obtain hg : guardVal I.k I.pl I.ql (s.mem.read I.pN 1) = 0 := by
      rw [← h9]; simpa using hb
    obtain ⟨g16, g2, gpq, gb⟩ := guard_zero (by omega_arith) (by omega_arith) (by omega_arith) hg
    obtain hb0 : 128 ≤ (I.nb[0]'hn0).toNat := by
      rw [read_one, show I.pN = I.pN + BitVec.ofNat 64 0 by simp, h.n.val 0 hn0] at gb; exact gb
    obtain hGd : I.Gd := ⟨g16, g2, gpq, hn0, hb0⟩
    obtain eW : wW I.cap = 2 * wk I.k + 2 := by rw [L.capk]
    obtain hw8 : 8 ≤ wk I.k := by unfold wk; omega_arith
    obtain hwk : wk I.k % 2 = 0 := by unfold wk; omega_arith
    obtain hwm : (wW I.cap - 2) / 4 = wk I.k / 2 := by rw [eW]; omega_arith
    obtain hW := ckWm_ok (wW I.cap) (by omega_arith) (by rw [eW]; unfold wk; omega_arith)
    obtain hxb := ckXb_ok I.B (wW I.cap) (by rw [eW]; omega_arith) (by rw [eW]; unfold wk; omega_arith)
    rw [hwm] at hW hxb
    refine WP.mono (wdiv_ok h₁.ws (iX := aA) (iM := aM) (iR := aRem) (iT := CheckKey.aT) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hW hL hxb (by omega_arith)
      (by omega_arith) (by omega_arith) hmL) fun t ⟨_, ft, kt, hval⟩ => ?_
    obtain ht := h₁.step ft (fun r hr => by
      simp only [ar, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Mut.ofSlot _ _ _) (fun r hr => by
      simp only [ar, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> dsimp only <;> exact h.ws.sl (by decide)) kt (by decide)
    refine ⟨ht, ?_, fun _ hG => ?_, fun i hi h1 _ h3 => ?_⟩
    · show word t.mem I.B (8 * Public.sMask) = word s.mem I.B (8 * Public.sMask)
      rw [ft.word_eq (fun r hr => by
        simp only [ar, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> dsimp only <;>
          exact .inl (hdr_lt_slot _ _ (show Public.sMask < 32 by decide))) (by unfold Public.sMask sFn; omega_arith),
        m₁]
    · obtain ⟨hAL, hMlo, hMhi⟩ := hG hGd
      obtain hM0 : wv s₁.mem I.B (slot (wW I.cap) aM) (wk I.k / 2) = I.av s.mem aM := by
        have := e₁ aM
        unfold CkIn.av at this ⊢
        rw [wv_low_of_lt (v := wk I.k / 2) (w := wW I.cap) (by omega_arith) (by rw [this]; exact hMhi), this]
      obtain hA0 : wv s₁.mem I.B (slot (wW I.cap) aA) Ln = I.av s.mem aA := by
        have := e₁ aA
        unfold CkIn.av at this ⊢
        rw [wv_low_of_lt (v := Ln) (w := wW I.cap) hLW (by rw [this]; exact hAL), this]
      obtain htop : 2 ^ 63 ≤ (word s₁.mem I.B (slot (wW I.cap) aM + 8 * (wk I.k / 2 - 1))).toNat := by
        rw [word_of_wv _ _ _ (wk I.k / 2) (by omega_arith), hM0]
        exact top_word_of (by omega_arith) hMlo hMhi
      obtain hv := hval htop
      rw [hM0, hA0] at hv
      obtain hM : 0 < I.av s.mem aM := Nat.lt_of_lt_of_le (Nat.two_pow_pos _) hMlo
      obtain hlt : wv t.mem I.B (slot (wW I.cap) aRem) (wW I.cap + 2) < 2 ^ (64 * wW I.cap) := by
        rw [hv]; exact Nat.lt_of_lt_of_le (Nat.mod_lt _ hM) (Nat.le_of_lt (wv_lt _ _ _ _))
      unfold CkIn.av
      rw [wv_low_of_lt (by omega_arith) hlt, hv]
    · rw [← e₁ i]
      unfold CkIn.av
      exact ft.wv_eq (fun r hr => by
        simp only [ar, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> dsimp only
        · have := slot_sep (w := wW I.cap) h1; omega_arith
        · have := slot_sep (w := wW I.cap) h3; omega_arith) (by have := h.ws.sl hi; omega_arith)
  · -- `reduceTop`.
    refine WP.mono (ckReduceTop_ok h₁ (by rw [m₁]; exact hT) hc1 hcw) fun t ⟨ht, mt, vt, ot⟩ =>
      ⟨ht, by rw [mt, m₁], fun hlt _ => by rw [vt (by rw [e₁, e₁]; exact hlt), e₁, e₁],
        fun i hi a b d => by rw [ot i hi a b d, e₁]⟩

/-- `wmodOne`: the mask of `[aA] mod [aM] = 1`, under `ckWRem_ok`'s
conditions. -/
theorem ckWModOne_ok {I : CkIn} {m₀ : Mem} {s : State} (h : CkS I m₀ s) (L : CkLens I)
    {g : Bool} (hm : mword s.mem I.B = mask g) (hO : I.av s.mem aOne = 1)
    {top : List Instr} {c : Nat} (hT : TopOk top I.B I.Z s.mem c) (hc1 : 1 ≤ c) (hcw : c < wW I.cap)
    {lenL : List Instr} {Ln : Nat} (hL : LenOk lenL (wW I.cap) Ln) (hLW : Ln ≤ wW I.cap) (hmL : wk I.k / 2 ≤ Ln) :
    WP isa (seqs (wmodOne top lenL)) s fun t => CkS I m₀ t ∧ (∃ r : Nat,
      (I.av s.mem aA / 2 ^ (64 * c) < I.av s.mem aM →
        (I.Gd → I.av s.mem aA < 2 ^ (64 * Ln) ∧ 2 ^ (64 * (wk I.k / 2) - 1) ≤ I.av s.mem aM ∧
          I.av s.mem aM < 2 ^ (64 * (wk I.k / 2))) → r = I.av s.mem aA % I.av s.mem aM) ∧
      mword t.mem I.B = mask (decide (r = 1) && g)) ∧
      ∀ i < 16, i ≠ aRem → i ≠ CheckCrtKey.aQ → i ≠ CheckKey.aT → I.av t.mem i = I.av s.mem i := by
  unfold wmodOne
  rw [List.append_assoc]
  refine wp_seqs_append (by simp) (by simp [eqA]) (WP.mono (ckWRem_ok h L hT hc1 hcw hL hLW hmL)
    fun s₁ ⟨h₁, m₁, v₁, o₁⟩ => ?_)
  refine WP.mono (ckEq_ok h₁ (a := aRem) (b := aOne) (by decide) (by decide) (m₁.trans hm)) fun t ⟨ht, mt, ot⟩ => ?_
  refine ⟨ht, ⟨I.av s₁.mem aRem, v₁, ?_⟩, fun i hi h1 h2 h3 => by rw [ot i hi, o₁ i hi h1 h2 h3]⟩
  rw [mt, o₁ aOne (by decide) (by decide) (by decide) (by decide), hO]

theorem modChecks_eq (sX sXlen sDX sYlen : Nat) : modChecks sX sXlen sDX sYlen =
    loadA aM sX sXlen ++ (([.block (decA aM)] : List (Prog isa)) ++ (loadA aX sDX sXlen ++ (ltA aX aM ++ (loadA aX sD sDlen ++
      (mulE ++ (wmodOne (topD sYlen) lenD ++ (loadA aX sDX sXlen ++ (mulE ++ wmodOne CheckCrtKey.topE lenE)))))))) := by
  simp only [modChecks, List.append_assoc]

/-- The checks modulo `X - 1`, for the prime `X` (the bytes `xb`) and its
exponent `dX` (the bytes `dxb`). -/
theorem phMod_ok {I : CkIn} {m₀ : Mem} {s : State} {c : Bool} (h : KS I m₀ c s) (L : CkLens I) (hE64 : I.E < 2 ^ 64)
    {sX sXlen sDX xl : Nat} {pX pDX : Addr} {xb dxb : List Byte} (hsX : sX < 32) (hsL : sXlen < 32)
    (hsD : sDX < 32) (hxl1 : 1 ≤ xl) (hxl2 : xl < I.k) (hxc : xl ≤ I.cap) (hxb : xb.length = xl) (hdxb : dxb.length = xl)
    (hA : ∀ t, CkS I m₀ t → word t.mem I.B (8 * sX) = pX ∧ word t.mem I.B (8 * sXlen) = BitVec.ofNat 64 xl ∧
      Src t I.B I.Z pX xb ∧ word t.mem I.B (8 * sDX) = pDX ∧ Src t I.B I.Z pDX dxb)
    {sYlen yl Y : Nat} (hsY : sYlen < 32) (hyc : yl ≤ I.cap)
    (hY : ∀ t, CkS I m₀ t → word t.mem I.B (8 * sYlen) = BitVec.ofNat 64 yl)
    (hy : Y < 2 ^ (64 * ((yl + 7) / 8))) (he33 : I.E < 2 ^ 33)
    (hXg : I.Gd → Spec.Rsa.os2ip xb * Y = I.N →
      2 ^ (64 * (wk I.k / 2) - 1) ≤ Spec.Rsa.os2ip xb - 1 ∧ Spec.Rsa.os2ip xb < 2 ^ (64 * (wk I.k / 2))) :
    WP isa (seqs (modChecks sX sXlen sDX sYlen)) s fun t => ∃ g : Bool, KS I m₀ (g && c) t ∧
      (Spec.Rsa.os2ip xb % 2 = 1 → 1 < Spec.Rsa.os2ip xb → I.D < I.N → Spec.Rsa.os2ip xb * Y = I.N →
        g = (decide (Spec.Rsa.os2ip dxb < Spec.Rsa.os2ip xb - 1) &&
          decide (I.D * I.E % (Spec.Rsa.os2ip xb - 1) = 1) &&
          decide (I.E * Spec.Rsa.os2ip dxb % (Spec.Rsa.os2ip xb - 1) = 1))) := by
  obtain ⟨hs, hm, hN, hE, hO⟩ := h
  have k1 := L.k1
  have k2 := L.k2
  obtain eW : wW I.cap = 2 * wk I.k + 2 := by rw [L.capk]
  obtain hwk : wk I.k < 2 ^ 20 := by unfold wk; omega_arith
  rw [modChecks_eq]
  -- `[aM] := X - 1`.
  obtain ⟨a1, a2, a3, -, -⟩ := hA s hs
  refine wp_seqs_append (by simp [loadA]) (by simp) (WP.mono (ckLoad_ok hs (j := aM) (by decide) hsX hsL a1 a2 a3
    hxb hxl1 (Nat.le_of_lt hxl2)) fun s₁ ⟨h₁, m₁, v₁, o₁⟩ => ?_)
  refine wp_seqs_append (a := [.block (decA aM)]) (by simp) (by simp [loadA]) (WP.mono (ckDec_ok h₁)
    fun s₂ ⟨h₂, m₂, v₂, o₂⟩ => ?_)
  rw [v₁] at v₂
  -- `dX < X - 1`.
  obtain ⟨-, b2, -, b4, b5⟩ := hA s₂ h₂
  refine wp_seqs_append (by simp [loadA]) (by simp [ltA]) (WP.mono (ckLoad_ok h₂ (j := aX) (by decide) hsD hsL b4
    b2 b5 hdxb hxl1 (Nat.le_of_lt hxl2)) fun s₃ ⟨h₃, m₃, v₃, o₃⟩ => ?_)
  obtain M₃ : I.av s₃.mem aM = I.av s₂.mem aM := o₃ aM (by decide) (by decide)
  refine wp_seqs_append (by simp [ltA]) (by simp [loadA]) (WP.mono (ckLt_ok h₃ (a := aX) (b := aM) (by decide)
    (by decide) (m₃.trans (m₂.trans (m₁.trans hm)))) fun s₄ ⟨h₄, m₄, o₄⟩ => ?_)
  rw [v₃, M₃] at m₄
  -- `d e mod (X - 1) = 1`.
  refine wp_seqs_append (by simp [loadA]) (by simp [mulE]) (WP.mono (ckLoad_ok h₄ (j := aX) (by decide) (by decide)
    (by decide) h₄.args.d h₄.args.dl h₄.d L.dbl L.dl1 L.dl2) fun s₅ ⟨h₅, m₅, v₅, o₅⟩ => ?_)
  obtain E₅ : I.av s₅.mem aE = I.E := by
    rw [o₅ aE (by decide) (by decide), o₄ aE (by decide), o₃ aE (by decide) (by decide), o₂ aE (by decide) (by decide),
      o₁ aE (by decide) (by decide), hE]
  refine wp_seqs_append (by simp [mulE]) (by simp [wmodOne]) (WP.mono (ckMulE_ok h₅ L
    (by rw [v₅]; exact lt_w (by rw [L.dbl]; exact L.dcap))) fun s₆ ⟨h₆, m₆, v₆, o₆⟩ => ?_)
  rw [v₅, e_word E₅ hE64] at v₆
  obtain O₆ : I.av s₆.mem aOne = 1 := by
    rw [o₆ aOne (by decide) (by decide), o₅ aOne (by decide) (by decide), o₄ aOne (by decide),
      o₃ aOne (by decide) (by decide), o₂ aOne (by decide) (by decide), o₁ aOne (by decide) (by decide), hO]
  refine wp_seqs_append (by simp [wmodOne]) (by simp [loadA]) (WP.mono (ckWModOne_ok h₆ L
    (m₆.trans (m₅.trans m₄)) O₆ (topD_ok hsY (hY _ h₆) (by have := L.cap2; have := L.k2; omega_arith)
      h₆.ws.h256) (by omega_arith)
    (by have := L.cap1; unfold wW wk; omega_arith) (ckLenD_ok (wW I.cap) (by rw [eW]; omega_arith))
    (by omega_arith) (by rw [eW]; omega_arith)) fun s₇ ⟨h₇, ⟨r₁, hr₁, m₇⟩, o₇⟩ => ?_)
  obtain M₆ : I.av s₆.mem aM = I.av s₂.mem aM := by
    rw [o₆ aM (by decide) (by decide), o₅ aM (by decide) (by decide), o₄ aM (by decide), M₃]
  rw [v₆, M₆] at hr₁
  -- `e dX mod (X - 1) = 1`.
  obtain ⟨-, -, -, c4, c5⟩ := hA s₇ h₇
  refine wp_seqs_append (by simp [loadA]) (by simp [mulE]) (WP.mono (ckLoad_ok h₇ (j := aX) (by decide) hsD hsL c4
    ((hA s₇ h₇).2.1) c5 hdxb hxl1 (Nat.le_of_lt hxl2)) fun s₈ ⟨h₈, m₈, v₈, o₈⟩ => ?_)
  obtain E₈ : I.av s₈.mem aE = I.E := by
    rw [o₈ aE (by decide) (by decide), o₇ aE (by decide) (by decide) (by decide) (by decide), o₆ aE (by decide)
      (by decide), E₅]
  refine wp_seqs_append (by simp [mulE]) (by simp [wmodOne]) (WP.mono (ckMulE_ok h₈ L
    (by rw [v₈]; exact lt_w (by rw [hdxb]; exact hxc))) fun s₉ ⟨h₉, m₉, v₉, o₉⟩ => ?_)
  rw [v₈, e_word E₈ hE64] at v₉
  obtain O₉ : I.av s₉.mem aOne = 1 := by
    rw [o₉ aOne (by decide) (by decide), o₈ aOne (by decide) (by decide),
      o₇ aOne (by decide) (by decide) (by decide) (by decide), O₆]
  refine WP.mono (ckWModOne_ok h₉ L (m₉.trans (m₈.trans m₇)) O₉ (topE_ok _ _ _)
    (by omega_arith) (by unfold wW; omega_arith) (ckLenE_ok (wW I.cap) (by omega_arith) (by rw [eW]; omega_arith))
    (by rw [eW]; omega_arith) (by rw [eW]; omega_arith)) fun t ⟨ht, ⟨r₂, hr₂, mt⟩, ot⟩ => ?_
  obtain M₉ : I.av s₉.mem aM = I.av s₂.mem aM := by
    rw [o₉ aM (by decide) (by decide), o₈ aM (by decide) (by decide), o₇ aM (by decide) (by decide) (by decide)
      (by decide), M₆]
  rw [v₉, M₉] at hr₂
  -- What the other arrays keep.
  obtain keep : ∀ i, i = 0 ∨ i = aE ∨ i = aOne → I.av t.mem i = I.av s.mem i := by
    intro i hi
    obtain h16 : i < 16 := by rcases hi with rfl | rfl | rfl <;> decide
    obtain d1 : i ≠ aM := by rcases hi with rfl | rfl | rfl <;> decide
    obtain d2 : i ≠ aX := by rcases hi with rfl | rfl | rfl <;> decide
    obtain d3 : i ≠ aA := by rcases hi with rfl | rfl | rfl <;> decide
    obtain d4 : i ≠ aRem := by rcases hi with rfl | rfl | rfl <;> decide
    obtain d5 : i ≠ aT := by rcases hi with rfl | rfl | rfl <;> decide
    obtain d6 : i ≠ CheckCrtKey.aQ := by rcases hi with rfl | rfl | rfl <;> decide
    rw [ot i h16 d4 d6 d5, o₉ i h16 d3, o₈ i h16 d2, o₇ i h16 d4 d6 d5, o₆ i h16 d3, o₅ i h16 d2, o₄ i h16,
      o₃ i h16 d2, o₂ i h16 d1, o₁ i h16 d1]
  refine ⟨decide (Spec.Rsa.os2ip dxb < I.av s₂.mem aM) && decide (r₁ = 1) && decide (r₂ = 1), ⟨ht, ?_,
    by rw [keep 0 (.inl rfl), hN], by rw [keep aE (.inr (.inl rfl)), hE], by rw [keep aOne (.inr (.inr rfl)), hO]⟩,
    fun ho h1 hd hpq => ?_⟩
  · rw [mt]
    cases decide (r₂ = 1) <;> cases decide (r₁ = 1) <;> cases decide (Spec.Rsa.os2ip dxb < I.av s₂.mem aM) <;>
      cases c <;> rfl
  · have hM : I.av s₂.mem aM = Spec.Rsa.os2ip xb - 1 := v₂ ho
    obtain hM0 : 0 < I.av s₂.mem aM := by rw [hM]; omega_arith
    obtain hdBound : I.D * I.E / 2 ^ (64 * ((yl + 7) / 8 + 1)) < I.av s₂.mem aM := by
      rw [hM, Nat.mul_comm I.D I.E]
      exact (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
        (by rw [Nat.mul_comm (Spec.Rsa.os2ip xb - 1)]; exact Proof.Rsa.fullExp_bound (x := Spec.Rsa.os2ip xb) (L := yl) he33 (by omega_arith) (by rw [hpq]; exact hd) hy)
    obtain hN : I.N < 2 ^ (64 * wk I.k) := lt_w (by rw [L.nl])
    obtain gM : I.Gd → 2 ^ (64 * (wk I.k / 2) - 1) ≤ I.av s₂.mem aM ∧ I.av s₂.mem aM < 2 ^ (64 * (wk I.k / 2)) :=
      fun hG => by
        obtain ⟨g1, g2⟩ := hXg hG hpq
        rw [hM]; exact ⟨g1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) g2⟩
    rw [hr₁ hdBound (fun hG => ⟨?_, gM hG⟩), hM]
    · by_cases hlt : Spec.Rsa.os2ip dxb < Spec.Rsa.os2ip xb - 1
      · rw [hr₂ (by rw [hM]; exact Nat.lt_of_le_of_lt (mul_div_top_le (k := 1) (by simpa using hE64)) hlt)
          (fun hG => ⟨?_, gM hG⟩), hM, Nat.mul_comm (Spec.Rsa.os2ip dxb) I.E]
        -- `e dX < 2^64 · 2^(64 w_m)`.
        obtain hX := (gM hG).2
        rw [hM] at hX
        rw [eW, show (2 * wk I.k + 2 - 2) / 4 + 1 = wk I.k / 2 + 1 by omega_arith, Nat.mul_add, Nat.pow_add]
        exact Nat.mul_lt_mul_of_lt_of_le (Nat.lt_trans hlt (by omega_arith)) (Nat.le_of_lt (by simpa using hE64))
          (Nat.two_pow_pos _)
      · simp only [hlt, decide_false, Bool.false_and]
    · -- `d e < 2^(64 (w + 1))`.
      rw [eW, show (2 * wk I.k + 2) / 2 = wk I.k + 1 by omega_arith, Nat.mul_add, Nat.pow_add]
      exact Nat.mul_lt_mul_of_lt_of_le (Nat.lt_trans hd hN) (Nat.le_of_lt (by simpa using hE64)) (Nat.two_pow_pos _)


/-- `qInv < p` and `q qInv ≡ 1 (mod p)`, by `wmodOne`. -/
theorem phQIC_ok {I : CkIn} {m₀ : Mem} {s : State} {c : Bool} (h : KS I m₀ c s) (L : CkLens I)
    (hPg : I.Gd → I.P * I.Q = I.N →
      2 ^ (64 * (wk I.k / 2) - 1) ≤ I.P - 1 ∧ I.P < 2 ^ (64 * (wk I.k / 2))) :
    WP isa (seqs (loadA aM sP sPlen ++ (loadA aX sQI sPlen ++ (ltA aX aM ++ (loadA aR sQ sQlen ++
      (mulPQ ++ wmodOne CheckCrtKey.topQ lenQ)))))) s fun t => ∃ g : Bool, KS I m₀ (g && c) t ∧
      (0 < I.P → I.P * I.Q = I.N → g = (decide (I.QI < I.P) && decide (I.Q * I.QI % I.P = 1))) := by
  obtain ⟨hs, hm, hN, hE, hO⟩ := h
  obtain eW : wW I.cap = 2 * wk I.k + 2 := by rw [L.capk]
  have k2 := L.k2
  obtain hwk : wk I.k < 2 ^ 20 := by unfold wk; omega_arith
  refine wp_seqs_append (by simp [loadA]) (by simp [loadA]) (WP.mono (ckLoad_ok hs (j := aM) (by decide) (by decide)
    (by decide) hs.args.p hs.args.pl hs.p L.pbl L.pl1 (Nat.le_of_lt L.pl2)) fun s₁ ⟨h₁, m₁, v₁, o₁⟩ => ?_)
  refine wp_seqs_append (by simp [loadA]) (by simp [ltA]) (WP.mono (ckLoad_ok h₁ (j := aX) (by decide) (by decide)
    (by decide) h₁.args.qi h₁.args.pl h₁.qi L.qibl L.pl1 (Nat.le_of_lt L.pl2)) fun s₂ ⟨h₂, m₂, v₂, o₂⟩ => ?_)
  obtain M₂ : I.av s₂.mem aM = I.P := by rw [o₂ aM (by decide) (by decide), v₁]
  refine wp_seqs_append (by simp [ltA]) (by simp [loadA]) (WP.mono (ckLt_ok h₂ (a := aX) (b := aM) (by decide)
    (by decide) (m₂.trans (m₁.trans hm))) fun s₃ ⟨h₃, m₃, o₃⟩ => ?_)
  rw [v₂, M₂] at m₃
  refine wp_seqs_append (by simp [loadA]) (by simp [mulPQ]) (WP.mono (ckLoad_ok h₃ (j := aR) (by decide) (by decide)
    (by decide) h₃.args.q h₃.args.ql h₃.q L.qbl L.ql1 (Nat.le_of_lt L.ql2)) fun s₄ ⟨h₄, m₄, v₄, o₄⟩ => ?_)
  obtain X₄ : I.av s₄.mem aX = I.QI := by rw [o₄ aX (by decide) (by decide), o₃ aX (by decide), v₂]
  refine wp_seqs_append (by simp [mulPQ]) (by simp [wmodOne]) (WP.mono (ckMulPQ_ok h₄ L
    (by rw [X₄]; have := os2ip_lt I.qib; rw [L.qibl] at this; exact this)
    (by rw [v₄]; have := os2ip_lt I.qb; rw [L.qbl] at this; exact this)) fun s₅ ⟨h₅, m₅, v₅, o₅⟩ => ?_)
  rw [X₄, v₄] at v₅
  obtain O₅ : I.av s₅.mem aOne = 1 := by
    rw [o₅ aOne (by decide) (by decide), o₄ aOne (by decide) (by decide), o₃ aOne (by decide),
      o₂ aOne (by decide) (by decide), o₁ aOne (by decide) (by decide), hO]
  -- `c = ⌈q_len / 8⌉` words: `q < 2^(64 c)`.
  obtain hk1 : 1 ≤ (I.ql + 7) / 8 := by have := L.ql1; omega_using [this]
  obtain hk : (I.ql + 7) / 8 < wW I.cap := by have := L.qcap; simp only [wW, wk]; omega_using [this]
  refine WP.mono (ckWModOne_ok h₅ L (m₅.trans (m₄.trans m₃)) O₅ (topQ_ok h₅.args.ql
    (by have := L.ql2; have := L.k2; omega_arith) (by have := h₅.ws.h256; omega_using [this])) hk1 hk (ckLenQ_ok (wW I.cap) (by omega_arith) (by rw [eW]; omega_arith))
    (by rw [eW]; omega_arith) (by rw [eW]; omega_arith))
    fun t ⟨ht, ⟨r, hr, mt⟩, ot⟩ => ?_
  obtain M₅ : I.av s₅.mem aM = I.P := by
    rw [o₅ aM (by decide) (by decide), o₄ aM (by decide) (by decide), o₃ aM (by decide), M₂]
  rw [v₅, M₅] at hr
  obtain keep : ∀ i, i = 0 ∨ i = aE ∨ i = aOne → I.av t.mem i = I.av s.mem i := by
    intro i hi
    obtain h16 : i < 16 := by rcases hi with rfl | rfl | rfl <;> decide
    obtain d1 : i ≠ aM := by rcases hi with rfl | rfl | rfl <;> decide
    obtain d2 : i ≠ aX := by rcases hi with rfl | rfl | rfl <;> decide
    obtain d3 : i ≠ aA := by rcases hi with rfl | rfl | rfl <;> decide
    obtain d4 : i ≠ aRem := by rcases hi with rfl | rfl | rfl <;> decide
    obtain d5 : i ≠ aT := by rcases hi with rfl | rfl | rfl <;> decide
    obtain d6 : i ≠ aR := by rcases hi with rfl | rfl | rfl <;> decide
    obtain d7 : i ≠ CheckCrtKey.aQ := by rcases hi with rfl | rfl | rfl <;> decide
    rw [ot i h16 d4 d7 d5, o₅ i h16 d3, o₄ i h16 d6, o₃ i h16, o₂ i h16 d2, o₁ i h16 d1]
  refine ⟨decide (I.QI < I.P) && decide (r = 1), ⟨ht, ?_, by rw [keep 0 (.inl rfl), hN],
    by rw [keep aE (.inr (.inl rfl)), hE], by rw [keep aOne (.inr (.inr rfl)), hO]⟩, fun hP hpq => ?_⟩
  · rw [mt]
    cases decide (r = 1) <;> cases decide (I.QI < I.P) <;> cases c <;> rfl
  · by_cases hlt : I.QI < I.P
    · have hq : I.Q < 2 ^ (64 * ((I.ql + 7) / 8)) := Nat.lt_of_lt_of_le (os2ip_lt I.qb)
        (by rw [L.qbl, show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
            exact Nat.pow_le_pow_right (by decide) (by omega_using []))
      rw [hr (Nat.lt_of_le_of_lt (mul_div_top_le hq) hlt) (fun hG => ⟨?_, ?_, ?_⟩), Nat.mul_comm I.QI I.Q]
      · -- `q qInv < q p = n < 2^(64 w)`.
        obtain hN : I.N < 2 ^ (64 * wk I.k) := lt_w (by rw [L.nl])
        rw [eW, show (2 * wk I.k + 2 - 2) / 2 = wk I.k by omega_arith, Nat.mul_comm I.QI I.Q]
        exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.le_of_lt hlt)) (by rw [Nat.mul_comm, hpq]; exact hN)
      · exact Nat.le_trans (hPg hG hpq).1 (Nat.sub_le _ _)
      · exact (hPg hG hpq).2
    · simp only [hlt, decide_false, Bool.false_and]

end VG.Proof.Rsa.AArch64
