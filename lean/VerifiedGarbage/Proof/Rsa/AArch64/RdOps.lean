module

public import VerifiedGarbage.Proof.Rsa.AArch64.KeyWs
public import VerifiedGarbage.Impl.Rsa.AArch64.RecoverDet
import VerifiedGarbage.Proof.Bignum.AArch64.Setup
import VerifiedGarbage.Proof.Bignum.AArch64.PubSetup
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
import VerifiedGarbage.Proof.Bignum.AArch64.MontMul
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Rsa.AArch64.RdPieces
public import VerifiedGarbage.Proof.Rsa.AArch64.Inv
public import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtSel
public import VerifiedGarbage.Proof.Rsa.AArch64.Div
public import VerifiedGarbage.Proof.Rsa.AArch64.RdArgs

/-!
# `vg_rsa_recover_primes_det` on AArch64: the widths

`setW_ok`: the header rewritten for the width in `x12` gives the working
space (`Ws`) at that width; `setNar_ok` and `setWid_ok` for the narrow
width `vk k = ⌈k / 8⌉ + 1` and the wide one `Wk k = 2 vk k + 2`, whose array
`j` is the narrow arrays `2 j` and `2 j + 1` (`slot_wide`).
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64.Rd

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Rsa.AArch64.RecoverDet
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- The narrow width. -/
abbrev vk (k : Nat) : Nat := (k + 15) / 8

/-- The wide width. -/
abbrev Wk (k : Nat) : Nat := 2 * vk k + 2

theorem slot_wide (v j : Nat) : slot (2 * v + 2) j = slot v (2 * j) := by
  unfold slot; rw [show 8 * (2 * v + 2 + 2) = 2 * (8 * (v + 2)) by omega, ← Nat.mul_assoc, Nat.mul_comm j 2]

/-- The header ranges `setW` writes. -/
def hdrW : List (Nat × Nat) := [(8 * sW, 8), (8 * sArr 0, 64), (8 * sStride, 8)]

theorem setW_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (h12 : s.gpr .x12 = BitVec.ofNat 64 w) (hw1 : 2 ≤ w) (hw2 : w < 2 ^ 24) (hZ : slot w 16 ≤ Z) :
    WP isa (.block setW) s fun t => Ws t B Z w ∧ Frm B hdrW s.mem t.mem ∧ t.gpr .x12 = s.gpr .x12 ∧
      Keep [.x3, .x4] s t := by
  have hn := hs.nowrap
  have h8 := hdr_lt_slot w 16 (show 31 < 32 by decide)
  have eW : sW = 6 := rfl
  have eA : sArr 0 = 8 := rfl
  have eS : sStride = 28 := rfl
  unfold setW
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = s.mem.writeW (off B (8 * sW)) (BitVec.ofNat 64 w)) (by
    brun [h0, h12, hdr_enc (show sW < 32 by decide), hs.st (d := 8 * sW) (by omega)]) (by decide) (by decide)
    (by decide +kernel)) fun t₁ ⟨hm₁, k₁⟩ => ?_
  have hs₁ := hs.congr k₁.wr
  have h0₁ : t₁.gpr .x0 = B := (k₁.gpr .x0 (by decide)).trans h0
  have h12₁ : t₁.gpr .x12 = BitVec.ofNat 64 w := (k₁.gpr .x12 (by decide)).trans h12
  rw [WP.block_append_iff]
  refine WP.mono (setBases_ok hs₁ h0₁ h12₁ (by unfold sArr; omega)) fun t₂ ⟨hb, ho₂, k₂⟩ => ?_
  have hs₂ := hs₁.congr k₂.wr
  have h0₂ : t₂.gpr .x0 = B := (k₂.gpr .x0 (by decide)).trans h0₁
  have h12₂ : t₂.gpr .x12 = BitVec.ofNat 64 w := (k₂.gpr .x12 (by decide)).trans h12₁
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.mem = t₂.mem.writeW (off B (8 * sStride))
      (BitVec.ofNat 64 (8 * (w + 2)))) (by
    brun [h0₂, h12₂, hdr_enc (show sStride < 32 by decide), hs₂.st (d := 8 * sStride) (by omega),
      ofNat_add_ofNat, shl_ofNat (show (w + 2) * 2 ^ 3 < 2 ^ 64 by omega)]
    rw [show (w + 2) * 2 ^ 3 = 8 * (w + 2) by omega]) (by decide) (by decide) (by decide +kernel))
    fun t ⟨hm, k₃⟩ => ?_
  have o3 := writeW_outside t₂.mem B (BitVec.ofNat 64 (8 * (w + 2))) (d := 8 * sStride) (by omega)
  have o1 := writeW_outside s.mem B (BitVec.ofNat 64 w) (d := 8 * sW) (by omega)
  rw [← hm] at o3
  rw [← hm₁] at o1
  refine ⟨⟨hs₂.congr k₃.wr, (k₃.gpr .x0 (by decide)).trans h0₂, ?_, ?_, fun j hj => ?_, hZ, hw1, hw2⟩, ?_,
    (k₃.gpr .x12 (by decide)).trans (h12₂.trans h12.symm), ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  · rw [o3.word (by omega) (by omega), ho₂.word (by omega) (by omega), hm₁, word_writeW_self]
  · rw [hm, word_writeW_self]
  · rw [o3.word (by unfold sArr; omega) (by unfold sArr; omega)]; exact hb j hj
  · intro x hx
    have a := hx (8 * sW, 8) (by simp [hdrW])
    have b := hx (8 * sArr 0, 64) (by simp [hdrW])
    have c := hx (8 * sStride, 8) (by simp [hdrW])
    dsimp only at a b c
    rw [o3 x c, ho₂ x b, o1 x a]

/-- `narW`: the narrow width into `x12`. -/
theorem narW_ok {s : State} {B : Addr} {Z k : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (hZ : 8 * 32 ≤ Z)
    (hK : word s.mem B (8 * Public.sK) = BitVec.ofNat 64 k) (hk : k < 2 ^ 32) :
    WP isa (.block narW) s fun t =>
      (t.gpr .x12 = BitVec.ofNat 64 (vk k) ∧ t.mem = s.mem) ∧ Keep [.x3, .x12] s t :=
  WP.keep [.x3, .x12] (by
    brun [narW, h0, hdr_enc (show Public.sK < 32 by decide), hs.ld (d := 8 * Public.sK) (by unfold Public.sK sFn; omega),
      hK]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow]
    simp only [vk]; omega) (by decide) (by decide) (by decide +kernel)

theorem setNar_ok {s : State} {B : Addr} {Z k : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (hK : word s.mem B (8 * Public.sK) = BitVec.ofNat 64 k) (hk1 : 64 ≤ k) (hk2 : k ≤ 1024)
    (hZ : 128 * k ≤ Z) :
    WP isa (.block setNar) s fun t => Ws t B Z (vk k) ∧ Frm B hdrW s.mem t.mem ∧ Keep [.x3, .x4, .x12] s t := by
  unfold setNar
  rw [WP.block_append_iff]
  refine WP.mono (narW_ok hs h0 (by omega) hK (by omega)) fun t₁ ⟨⟨h12, m₁⟩, k₁⟩ => ?_
  refine WP.mono (setW_ok (hs.congr k₁.wr) ((k₁.gpr .x0 (by decide)).trans h0) h12 (by simp only [vk]; omega)
    (by simp only [vk]; omega) (by simp only [slot, hdrBytes, vk]; omega)) fun t ⟨hw, f, _, k₂⟩ => ⟨hw, by rw [← m₁]; exact f, (k₁.trans k₂).mono (by decide)⟩

theorem setWid_ok {s : State} {B : Addr} {Z k : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (hK : word s.mem B (8 * Public.sK) = BitVec.ofNat 64 k) (hk1 : 64 ≤ k) (hk2 : k ≤ 1024)
    (hZ : 128 * k ≤ Z) :
    WP isa (.block setWid) s fun t => Ws t B Z (Wk k) ∧ Frm B hdrW s.mem t.mem ∧ Keep [.x3, .x4, .x12] s t := by
  unfold setWid
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (narW_ok hs h0 (by omega) hK (by omega)) fun t₁ ⟨⟨h12, m₁⟩, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x12] (Q := fun t => t.gpr .x12 = BitVec.ofNat 64 (Wk k) ∧ t.mem = t₁.mem)
    (by brun [h12, ofNat_add_ofNat]; congr 1; simp only [Wk, vk]; omega) (by decide) (by decide) (by decide +kernel))
    fun t₂ ⟨⟨h12₂, m₂⟩, k₂⟩ => ?_
  refine WP.mono (setW_ok ((hs.congr k₁.wr).congr k₂.wr) ((k₂.gpr .x0 (by decide)).trans ((k₁.gpr .x0 (by decide)).trans h0))
    h12₂ (by simp only [Wk, vk]; omega) (by simp only [Wk, vk]; omega) (by simp only [slot, hdrBytes, Wk, vk]; omega)) fun t ⟨hw, f, _, k₃⟩ =>
      ⟨hw, by rw [← m₁, ← m₂]; exact f, ((k₁.trans k₂).trans k₃).mono (by decide)⟩


/-! ## Operations on arrays -/

section Ops
variable {s : State} {B : Addr} {Z w : Nat}

/-- `subA o a b`: `[o] := [a] - [b]`, and `x15` the mask of `[b] ≤ [a]`. -/
theorem subA_ok (h : Ws s B Z w) {o a b : Nat} (ho : o < 16) (ha : a < 16) (hb : b < 16) (hoa : o ≠ a)
    (hob : o ≠ b) :
    WP isa (subA o a b) s fun t =>
      wv t.mem B (slot w o) w + wv s.mem B (slot w b) w =
        wv s.mem B (slot w a) w + 2 ^ (64 * w) * (!decide (wv s.mem B (slot w b) w ≤ wv s.mem B (slot w a) w)).toNat ∧
      t.gpr .x15 = mask (decide (wv s.mem B (slot w b) w ≤ wv s.mem B (slot w a) w)) ∧ t.gpr .x7 = 0 ∧
      Outside B (slot w o) (8 * w) s.mem t.mem ∧
      Keep [.x3, .x4, .x7, .x11, .x12, .x13, .x14, .x15, .x16, .x17] s t := by
  have hn := h.scr.nowrap
  have so := h.sl ho
  have sa := h.sl ha
  have sb := h.sl hb
  have pa := slot_sep (w := w) hoa
  have pb := slot_sep (w := w) hob
  have hw1 := h.w1
  have hw2 := h.w2
  unfold subA
  simp only [seqs]
  refine WP.seq (WP.mono (subSet_ok h a b o) fun t₁ ⟨⟨h16, h17, h13, h14, _, h7, hc, m₁⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (subLoop_ok (h.scr.congr k₁.wr) h16 h17 h13 h14 hc (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)) fun t₂ ⟨hv, o₂, k₂⟩ => ?_)
  refine WP.mono (carryMask_ok t₂ ((k₂.gpr .x7 (by decide)).trans h7)) fun t ⟨⟨h15, mt, _⟩, k₃⟩ => ?_
  rw [m₁] at hv o₂
  rw [mt]
  have lt := wv_lt t₂.mem B (slot w o) w
  have hcv : t₂.c = decide (wv s.mem B (slot w b) w ≤ wv s.mem B (slot w a) w) := by
    cases hc' : t₂.c
    · rw [hc'] at hv; simp only [Bool.not_false, Bool.toNat_true, Nat.mul_one] at hv
      exact (decide_eq_false (by omega)).symm
    · rw [hc'] at hv; simp only [Bool.not_true, Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at hv
      exact (decide_eq_true (by omega)).symm
  refine ⟨by rw [← hcv]; exact hv, by rw [h15, hcv], (k₃.gpr .x7 (by decide)).trans ((k₂.gpr .x7 (by decide)).trans h7),
    o₂, ((k₁.trans k₂).trans k₃).mono (by decide)⟩

/-- The bases of `addA o a b`, from the carry clear. -/
theorem addSet_ok (h : Ws s B Z w) (a b o : Nat) :
    WP isa (.block (ws ++ [movi .x7 0, mov .x14 .x12, .adds .x .x3 .x7 .x7] ++ base a .x10 ++ base b .x8 ++
      base o .x5)) s fun t =>
      (t.gpr .x10 = off B (slot w a) ∧ t.gpr .x8 = off B (slot w b) ∧ t.gpr .x5 = off B (slot w o) ∧
        t.gpr .x14 = BitVec.ofNat 64 w ∧ t.gpr .x7 = 0 ∧ t.c = false ∧ t.mem = s.mem) ∧
      Keep [.x3, .x5, .x7, .x8, .x10, .x11, .x12, .x14] s t := by
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono h.ws_ok fun t₁ ⟨⟨h12, h11, m₁, _⟩, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x7, .x14] (Q := fun t => t.gpr .x14 = BitVec.ofNat 64 w ∧ t.gpr .x7 = 0 ∧
      t.c = false ∧ t.mem = t₁.mem) (by brun [h12]) (by decide) (by decide) (by decide +kernel))
    fun t₂ ⟨⟨h14, h7, hc, m₂⟩, k₂⟩ => ?_
  have h0₂ : t₂.gpr .x0 = B := ((k₁.trans k₂).gpr .x0 (by decide)).trans h.x0
  rw [← List.append_assoc]
  refine WP.mono (base3_ok a b o .x10 .x8 .x5 h0₂ ((k₂.gpr .x11 (by decide)).trans h11))
    fun t ⟨⟨h10, h8, h5, m₃, c₃⟩, k₃⟩ => ⟨⟨h10, h8, h5, (k₃.gpr .x14 (by decide)).trans h14,
      (k₃.gpr .x7 (by decide)).trans h7, c₃.trans hc, by rw [m₃, m₂, m₁]⟩, ((k₁.trans k₂).trans k₃).mono (by decide)⟩

/-- `addA o a b`: `[o] := ([a] & x15) + [b]`, modulo `2^(64 w)`. -/
theorem addA_ok (h : Ws s B Z w) {o a b : Nat} (ho : o < 16) (ha : a < 16) (hb : b < 16) (hoa : o ≠ a)
    (hob : o ≠ b) {c : Bool} (h15 : s.gpr .x15 = mask c) :
    WP isa (addA o a b) s fun t =>
      wv t.mem B (slot w o) w = ((if c then wv s.mem B (slot w a) w else 0) + wv s.mem B (slot w b) w) % 2 ^ (64 * w) ∧
      t.gpr .x7 = 0 ∧ Outside B (slot w o) (8 * w) s.mem t.mem ∧
      Keep [.x3, .x4, .x5, .x7, .x8, .x10, .x11, .x12, .x14] s t := by
  have hn := h.scr.nowrap
  have so := h.sl ho
  have sa := h.sl ha
  have sb := h.sl hb
  have pa := slot_sep (w := w) hoa
  have pb := slot_sep (w := w) hob
  have hw1 := h.w1
  have hw2 := h.w2
  unfold addA
  refine WP.seq (WP.mono (addSet_ok h a b o) fun t₁ ⟨⟨h10, h8, h5, h14, h7, hc, m₁⟩, k₁⟩ => ?_)
  refine WP.mono (addM_ok (h.scr.congr k₁.wr) h10 h8 h5 h14 ((k₁.gpr .x15 (by decide)).trans h15) hc (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)) fun t ⟨hv, _, o₂, k₂⟩ => ?_
  rw [m₁] at hv o₂
  refine ⟨?_, (k₂.gpr .x7 (by decide)).trans h7, o₂, (k₁.trans k₂).mono (by decide)⟩
  have lt := wv_lt t.mem B (slot w o) w
  rw [← hv, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt lt]

/-- The bases `[a]` in `x16` and `[o]` in `x17`, and `w` in `x14`. -/
theorem pairSet_ok (h : Ws s B Z w) (a o : Nat) :
    WP isa (.block (ws ++ [mov .x14 .x12] ++ base a .x16 ++ base o .x17)) s fun t =>
      (t.gpr .x16 = off B (slot w a) ∧ t.gpr .x17 = off B (slot w o) ∧ t.gpr .x14 = BitVec.ofNat 64 w ∧
        t.mem = s.mem) ∧ Keep [.x11, .x12, .x14, .x16, .x17] s t := by
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono h.ws_ok fun t₁ ⟨⟨h12, h11, m₁, _⟩, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x14] (Q := fun t => t.gpr .x14 = BitVec.ofNat 64 w ∧ t.mem = t₁.mem) (by brun [h12])
    (by decide) (by decide) (by decide +kernel)) fun t₂ ⟨⟨h14, m₂⟩, k₂⟩ => ?_
  have h0₂ : t₂.gpr .x0 = B := ((k₁.trans k₂).gpr .x0 (by decide)).trans h.x0
  refine WP.mono (base2_ok a o .x16 .x17 h0₂ ((k₂.gpr .x11 (by decide)).trans h11))
    fun t ⟨⟨h16, h17, m₃, _⟩, k₃⟩ => ⟨⟨h16, h17, (k₃.gpr .x14 (by decide)).trans h14, by rw [m₃, m₂, m₁]⟩,
      ((k₁.trans k₂).trans k₃).mono (by decide)⟩

/-- `halfA o a`: `[o] := [a] / 2` for `[a]`'s word `w` zero; `o` may be `a`. -/
theorem halfA_ok (h : Ws s B Z w) {o a : Nat} (ho : o < 16) (ha : a < 16)
    (hz : word s.mem B (slot w a + 8 * w) = 0) :
    WP isa (halfA o a) s fun t =>
      wv t.mem B (slot w o) w = wv s.mem B (slot w a) w / 2 ∧ Outside B (slot w o) (8 * w) s.mem t.mem ∧
      Keep [.x3, .x4, .x11, .x12, .x14, .x16, .x17] s t := by
  have hn := h.scr.nowrap
  have so := h.sl ho
  have sa := h.sl ha
  have hw1 := h.w1
  have hw2 := h.w2
  have sp : slot w o = slot w a ∨ slot w a + 8 * (w + 1) ≤ slot w o ∨ slot w o + 8 * w ≤ slot w a := by
    by_cases e : o = a
    · left; rw [e]
    · right; have := slot_sep (w := w) e; omega
  unfold halfA
  refine WP.seq (WP.mono (pairSet_ok h a o) fun t₁ ⟨⟨h16, h17, h14, m₁⟩, k₁⟩ => ?_)
  refine WP.mono (shr_ok (h.scr.congr k₁.wr) h16 h17 h14 (by omega) (by omega) (by omega) (by omega) sp)
    fun t ⟨hv, _, o₂, k₂⟩ => ⟨?_, by rw [m₁] at o₂; exact o₂, (k₁.trans k₂).mono (by decide)⟩
  rw [m₁, hz] at hv
  have := wv_low (m := s.mem) (B := B) (e := slot w a) (w := w) (by omega)
  have z : (0 : BitVec 64).toNat = 0 := rfl
  rw [z] at hv
  omega

/-- `selA o a`: `[o] := [a]` if `x15` is all ones. -/
theorem selA_ok (h : Ws s B Z w) {o a : Nat} (ho : o < 16) (ha : a < 16) (hoa : o ≠ a) {c : Bool}
    (h15 : s.gpr .x15 = mask c) :
    WP isa (selA o a) s fun t =>
      wv t.mem B (slot w o) w = (if c then wv s.mem B (slot w a) w else wv s.mem B (slot w o) w) ∧
      Outside B (slot w o) (8 * w) s.mem t.mem ∧ Keep [.x3, .x4, .x11, .x12, .x14, .x16, .x17] s t := by
  have hn := h.scr.nowrap
  have so := h.sl ho
  have sa := h.sl ha
  have pa := slot_sep (w := w) hoa
  have hw1 := h.w1
  have hw2 := h.w2
  unfold selA
  refine WP.seq (WP.mono (pairSet_ok h a o) fun t₁ ⟨⟨h16, h17, h14, m₁⟩, k₁⟩ => ?_)
  refine WP.mono (selLoop_ok (h.scr.congr k₁.wr) h16 h17 h14 ((k₁.gpr .x15 (by decide)).trans h15) (by omega)
    (by omega) (by omega) (by omega) (by omega)) fun t ⟨hv, o₂, k₂⟩ => ⟨by rw [hv, m₁], by rw [m₁] at o₂; exact o₂,
      (k₁.trans k₂).mono (by decide)⟩

/-- A block setting the carry flag to `b`, from `x7 = 0`, writing only `x3`
and `x4`. -/
def CIn (cin : List Instr) (b : Bool) (s : State) : Prop :=
  WP isa (.block cin) s fun t => (t.c = b ∧ t.mem = s.mem) ∧ Keep [.x3, .x4] s t

theorem c0_ok (s : State) (h7 : s.gpr .x7 = 0) : CIn c0 false s :=
  WP.keep [.x3, .x4] (by brun [c0, h7]) (by decide) (by decide) (by decide +kernel)

theorem c1_ok (s : State) (h7 : s.gpr .x7 = 0) : CIn c1 true s :=
  WP.keep [.x3, .x4] (by brun [c1, h7]) (by decide) (by decide) (by decide +kernel)

theorem cOf_ok (s : State) {r : Reg} (hr : r = .x1 ∨ r = .x2) {b : Bool}
    (hv : s.gpr r = BitVec.ofNat 64 b.toNat) : CIn (cOf r) b s := by
  rcases hr with rfl | rfl <;>
  · refine WP.keep [.x3, .x4] ?_ (by decide) (by decide) (by decide +kernel)
    unfold cOf
    brun [hv]
    cases b <;> decide

theorem cMask_ok (s : State) {c : Bool} (h15 : s.gpr .x15 = mask c) :
    CIn [.adds .x .x3 .x15 .x15] c s := by
  refine WP.keep [.x3, .x4] ?_ (by decide) (by decide) (by decide +kernel)
  brun [h15]
  cases c <;> decide

/-- `dblA a cin cout`: `[a] := 2 [a] + b` for the carry `b` that `cin`
sets, `C` the carry out; then `cout`. -/
theorem dblA_ok (h : Ws s B Z w) {a : Nat} (ha : a < 16) {cin : List Instr} {b : Bool}
    (hc : ∀ t, t.gpr .x7 = 0 → (∀ r, r ∉ [Reg.x11, .x12, .x7, .x14, .x16] → t.gpr r = s.gpr r) → CIn cin b t) {cout : List Instr} {Q : State → Prop}
    (hq : ∀ t₁ : State, wv t₁.mem B (slot w a) w + 2 ^ (64 * w) * t₁.c.toNat = 2 * wv s.mem B (slot w a) w + b.toNat →
      t₁.gpr .x7 = 0 → Outside B (slot w a) (8 * w) s.mem t₁.mem →
      Keep [.x3, .x4, .x7, .x11, .x12, .x14, .x16] s t₁ → WP isa (.block cout) t₁ Q) :
    WP isa (dblA a cin cout) s Q := by
  have hn := h.scr.nowrap
  have sa := h.sl ha
  have hw1 := h.w1
  have hw2 := h.w2
  unfold dblA
  simp only [seqs]
  rw [List.append_assoc, List.append_assoc, WP.seq_iff, WP.block_append_iff]
  refine WP.mono h.ws_ok fun t₁ ⟨⟨h12, h11, m₁, _⟩, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x7, .x14] (Q := fun t => t.gpr .x14 = BitVec.ofNat 64 w ∧ t.gpr .x7 = 0 ∧
      t.mem = t₁.mem) (by brun [h12]) (by decide) (by decide) (by decide +kernel))
    fun t₂ ⟨⟨h14, h7, m₂⟩, k₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base_ok a .x16 (((k₁.trans k₂).gpr .x0 (by decide)).trans h.x0) ((k₂.gpr .x11 (by decide)).trans h11))
    fun t₃ ⟨⟨h16, m₃, _⟩, k₃⟩ => ?_
  refine WP.mono (hc t₃ ((k₃.gpr .x7 (by decide)).trans h7) (fun r hr =>
    (((k₁.trans k₂).trans k₃).mono (by decide) : Keep [Reg.x11, .x12, .x7, .x14, .x16] s t₃).gpr r hr)) fun t₄ ⟨⟨c₄, m₄⟩, k₄⟩ => ?_
  have k14 := ((k₁.trans k₂).trans k₃).trans k₄
  refine WP.seq (WP.mono (shl_ok (h.scr.congr k14.wr) ((k₄.gpr .x16 (by decide)).trans h16)
    ((k₄.gpr .x14 (by decide)).trans ((k₃.gpr .x14 (by decide)).trans h14)) (by omega) (by omega) (by omega))
    fun t₅ ⟨hv, _, o₅, k₅⟩ => ?_)
  have mm : t₄.mem = s.mem := by rw [m₄, m₃, m₂, m₁]
  rw [mm, c₄] at hv
  rw [mm] at o₅
  exact hq t₅ hv ((k₅.gpr .x7 (by decide)).trans ((k₄.gpr .x7 (by decide)).trans ((k₃.gpr .x7 (by decide)).trans h7)))
    o₅ ((k14.trans k₅).mono (by decide))

/-- `dblA a cin []`. -/
theorem dbl_ok (h : Ws s B Z w) {a : Nat} (ha : a < 16) {cin : List Instr} {b : Bool}
    (hc : ∀ t, t.gpr .x7 = 0 → (∀ r, r ∉ [Reg.x11, .x12, .x7, .x14, .x16] → t.gpr r = s.gpr r) → CIn cin b t) :
    WP isa (dblA a cin []) s fun t =>
      wv t.mem B (slot w a) w = (2 * wv s.mem B (slot w a) w + b.toNat) % 2 ^ (64 * w) ∧ t.gpr .x7 = 0 ∧
      Outside B (slot w a) (8 * w) s.mem t.mem ∧ Keep [.x3, .x4, .x7, .x11, .x12, .x14, .x16] s t :=
  dblA_ok h ha hc fun t₁ hv h7 o k => WP.block_nil_iff.mpr ⟨by
    have := wv_lt t₁.mem B (slot w a) w
    rw [← hv, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt this], h7, o, k⟩

/-- `dblA a cin (cTo r)`: the carry out into `r`. -/
theorem dblc_ok (h : Ws s B Z w) {a : Nat} (ha : a < 16) {cin : List Instr} {b : Bool}
    (hc : ∀ t, t.gpr .x7 = 0 → (∀ r, r ∉ [Reg.x11, .x12, .x7, .x14, .x16] → t.gpr r = s.gpr r) → CIn cin b t) {r : Reg} (hr : r = .x1 ∨ r = .x2) :
    WP isa (dblA a cin (cTo r)) s fun t =>
      wv t.mem B (slot w a) w = (2 * wv s.mem B (slot w a) w + b.toNat) % 2 ^ (64 * w) ∧
      t.gpr r = BitVec.ofNat 64 ((2 * wv s.mem B (slot w a) w + b.toNat) / 2 ^ (64 * w)) ∧ t.gpr .x7 = 0 ∧
      Outside B (slot w a) (8 * w) s.mem t.mem ∧ Keep [r, .x3, .x4, .x7, .x11, .x12, .x14, .x16] s t :=
  dblA_ok h ha hc fun t₁ hv' h7 o k => by
    have lt := wv_lt t₁.mem B (slot w a) w
    have e1 : (2 * wv s.mem B (slot w a) w + b.toNat) % 2 ^ (64 * w) = wv t₁.mem B (slot w a) w := by
      rw [← hv', Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt lt]
    have e2 : (2 * wv s.mem B (slot w a) w + b.toNat) / 2 ^ (64 * w) = t₁.c.toNat := by
      rw [← hv', Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt lt, Nat.zero_add]
    have hk : WP isa (.block (cTo r)) t₁ fun t => (t.gpr r = BitVec.ofNat 64 t₁.c.toNat ∧ t.mem = t₁.mem) ∧
        Keep [r] t₁ t := by
      rcases hr with rfl | rfl <;>
      · refine WP.keep _ ?_ (by decide) (by decide) (by decide +kernel)
        unfold cTo; brun [h7]; cases t₁.c <;> rfl
    refine WP.mono hk fun t ⟨⟨hr', mt⟩, k'⟩ => ?_
    have h7' : t.gpr .x7 = 0 := by rw [k'.gpr .x7 (by rcases hr with rfl | rfl <;> decide)]; exact h7
    exact ⟨by rw [mt, e1], by rw [hr', e2], h7', by rw [mt]; exact o, (k.trans k').mono (by simp)⟩

end Ops

/-- The bases of a comparison of `[a]` with `[b]`, from the carry set. -/
theorem cmpSet_ok' {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) (a b : Nat) :
    WP isa (.block (ws ++ [movi .x7 0, mov .x14 .x12, .subs .x .x3 .x7 .x7] ++ base a .x16 ++ base b .x17)) s
      fun t => (t.gpr .x16 = off B (slot w a) ∧ t.gpr .x17 = off B (slot w b) ∧
        t.gpr .x14 = BitVec.ofNat 64 w ∧ t.gpr .x12 = BitVec.ofNat 64 w ∧
        t.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2)) ∧ t.gpr .x7 = 0 ∧ t.c = true ∧
        t.mem = s.mem) ∧ Keep [.x3, .x7, .x11, .x12, .x14, .x16, .x17] s t := by
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono h.ws_ok fun t₁ ⟨⟨h12, h11, m₁, _⟩, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x7, .x14] (Q := fun t => t.gpr .x14 = BitVec.ofNat 64 w ∧ t.gpr .x7 = 0 ∧
      t.c = true ∧ t.mem = t₁.mem) (by brun [h12]) (by decide) (by decide) (by decide +kernel))
    fun t₂ ⟨⟨h14, h7, hc, m₂⟩, k₂⟩ => ?_
  have h0₂ : t₂.gpr .x0 = B := ((k₁.trans k₂).gpr .x0 (by decide)).trans h.x0
  refine WP.mono (base2_ok a b .x16 .x17 h0₂ ((k₂.gpr .x11 (by decide)).trans h11))
    fun t ⟨⟨h16, h17, m₃, c₃⟩, k₃⟩ => ⟨⟨h16, h17, (k₃.gpr .x14 (by decide)).trans h14,
      (k₃.gpr .x12 (by decide)).trans ((k₂.gpr .x12 (by decide)).trans h12),
      (k₃.gpr .x11 (by decide)).trans ((k₂.gpr .x11 (by decide)).trans h11), (k₃.gpr .x7 (by decide)).trans h7,
      c₃.trans hc, by rw [m₃, m₂, m₁]⟩, ((k₁.trans k₂).trans k₃).mono (by decide)⟩

/-- `borrowMask`: `x15` the mask of the carry flag clear. -/
theorem borrowMask_ok (s : State) (h7 : s.gpr .x7 = 0) :
    WP isa (.block borrowMask) s fun t =>
      (t.gpr .x15 = mask (!s.c) ∧ t.mem = s.mem ∧ t.c = s.c) ∧ Keep [.x4, .x15] s t := by
  refine WP.keep [.x4, .x15] ?_ (by decide) (by decide) (by decide +kernel)
  brun [borrowMask, h7]
  cases s.c <;> rfl

/-- `ones`: `x15` all ones and `x7 = 0`. -/
theorem ones_ok (s : State) :
    WP isa (.block ones) s fun t => (t.gpr .x15 = mask true ∧ t.gpr .x7 = 0 ∧ t.mem = s.mem) ∧ Keep [.x7, .x15] s t :=
  WP.keep [.x7, .x15] (by brun [ones]) (by decide) (by decide) (by decide +kernel)

/-! ## What every piece keeps -/

open VG.Impl.Rsa.AArch64.Recover (sP sQ sD sDl)

/-- Between the pieces of `main`: the working space at the width `w`, the
arguments, the inputs, and the mask `c`. -/
structure G (I : RpIn) (m₀ : Mem) (w : Nat) (c : Bool) (s : State) : Prop where
  ws : Ws s I.B I.Z w
  args : RpArgs s.mem I.B I.k I.el I.dl I.pP I.pQ I.pN I.pE I.pD
  n : Src s I.B I.Z I.pN I.nb
  e : Src s I.B I.Z I.pE I.eb
  d : Src s I.B I.Z I.pD I.db
  inScr : InScr I.B I.Z m₀ s.mem
  wr : s.wr = I.W
  msk : word s.mem I.B (8 * Public.sMask) = mask c

theorem G.step {I : RpIn} {m₀ : Mem} {w : Nat} {c : Bool} {s t : State} (h : G I m₀ w c s) {rs : List (Nat × Nat)}
    (hf : Frm I.B rs s.mem t.mem) (hm : ∀ r ∈ rs, 8 * 32 ≤ r.1) (hz : ∀ r ∈ rs, r.1 + r.2 ≤ I.Z) {regs : List Reg}
    (k : Keep regs s t) (hr : .x0 ∉ regs) : G I m₀ w c t :=
  have hi : InScr I.B I.Z s.mem t.mem := InScr.of_frm hf hz
  have hmut : ∀ r ∈ rs, Mut r := fun r hr => Or.inl (hm r hr)
  ⟨h.ws.congr hf hmut k hr, h.args.congr fun i hi => hf.word_eq (fun r hr => Or.inl (by
      have := hm r hr; unfold rArg at hi; omega)) (by have := h.ws.scr.nowrap; have := h.ws.h256; unfold rArg at hi; omega),
    h.n.congrK hi k, h.e.congrK hi k, h.d.congrK hi k, h.inScr.trans hi, k.wr.trans h.wr,
    (hf.word_eq (fun r hr => Or.inl (by have := hm r hr; simp only [Public.sMask, sFn]; omega))
      (by have := h.ws.scr.nowrap; have := h.ws.h256; simp only [Public.sMask, sFn]; omega)).trans h.msk⟩

/-- After a piece that changes only array `j`'s first `n` bytes. -/
theorem G.out {I : RpIn} {m₀ : Mem} {w : Nat} {c : Bool} {s t : State} (h : G I m₀ w c s) {j n : Nat} (hj : j < 16)
    (hn : n ≤ 8 * (w + 2)) (o : Outside I.B (slot w j) n s.mem t.mem) {regs : List Reg} (k : Keep regs s t)
    (hr : .x0 ∉ regs) : G I m₀ w c t :=
  h.step (Frm.of_outside o (List.mem_singleton_self _)) (fun r hr => by
    rw [List.mem_singleton.mp hr]; unfold slot hdrBytes; dsimp only; omega) (fun r hr => by
    rw [List.mem_singleton.mp hr]; have := h.ws.sl hj; dsimp only; omega) k hr

/-- After a piece that changes no memory. -/
theorem G.same {I : RpIn} {m₀ : Mem} {w : Nat} {c : Bool} {s t : State} (h : G I m₀ w c s) (hm : t.mem = s.mem)
    {regs : List Reg} (k : Keep regs s t) (hr : .x0 ∉ regs) : G I m₀ w c t :=
  h.step (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) (by simp) k hr

/-- After the mask is stored. -/
theorem G.store {I : RpIn} {m₀ : Mem} {w : Nat} {c c' : Bool} {s t : State} (h : G I m₀ w c s)
    (hm : t.mem = s.mem.writeW (off I.B (8 * Public.sMask)) (mask c')) {regs : List Reg} (k : Keep regs s t)
    (hr : .x0 ∉ regs) : G I m₀ w c' t := by
  have hn := h.ws.scr.nowrap
  have h256 := h.ws.h256
  have o := writeW_outside s.mem I.B (mask c') (d := 8 * Public.sMask) (by simp only [Public.sMask, sFn]; omega)
  rw [← hm] at o
  have hf : Frm I.B [(8 * Public.sMask, 8)] s.mem t.mem := Frm.of_outside o (List.mem_singleton_self _)
  have hi : InScr I.B I.Z s.mem t.mem := InScr.of_frm hf (by
    simp only [List.mem_singleton]; rintro r rfl; simp only [Public.sMask, sFn]; omega)
  exact ⟨h.ws.congr hf (by simp only [List.mem_singleton]; rintro r rfl; exact Or.inr rfl) k hr,
    h.args.congr fun i hi => o.word (by unfold rArg at hi; simp only [Public.sMask, sFn]; omega)
      (by unfold rArg at hi; omega),
    h.n.congrK hi k, h.e.congrK hi k, h.d.congrK hi k, h.inScr.trans hi, k.wr.trans h.wr,
    by rw [hm, word_writeW_self]⟩

/-- After the header is rewritten for the width `w'`. -/
theorem G.hdr {I : RpIn} {m₀ : Mem} {w w' : Nat} {c : Bool} {s t : State} (h : G I m₀ w c s)
    (hw : Ws t I.B I.Z w') (hf : Frm I.B hdrW s.mem t.mem) {regs : List Reg} (k : Keep regs s t) :
    G I m₀ w' c t := by
  have hn := h.ws.scr.nowrap
  have h256 := h.ws.h256
  have hi : InScr I.B I.Z s.mem t.mem := InScr.of_frm hf (by
    simp only [hdrW, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> simp only [sW, sArr, sStride, sFn] <;> omega)
  have hw' : ∀ i, (16 ≤ i ∧ i < 28) → word t.mem I.B (8 * i) = word s.mem I.B (8 * i) := fun i hi =>
    hf.word_eq (fun r hr => by
      simp only [hdrW, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [sW, sArr, sStride, sFn] <;> omega) (by omega)
  exact ⟨hw, h.args.congr fun i hi => hw' i (by unfold rArg at hi; omega), h.n.congrK hi k, h.e.congrK hi k,
    h.d.congrK hi k, h.inScr.trans hi, k.wr.trans h.wr,
    (hw' Public.sMask (by simp only [Public.sMask, sFn]; omega)).trans h.msk⟩

theorem G.setNar_ok {I : RpIn} {m₀ : Mem} {w : Nat} {c : Bool} {s : State} (h : G I m₀ w c s) (L : RpLens I) :
    WP isa (.block setNar) s fun t => G I m₀ (vk I.k) c t ∧ Frm I.B hdrW s.mem t.mem ∧ Keep [.x3, .x4, .x12] s t :=
  WP.mono (Rd.setNar_ok h.ws.scr h.ws.x0 h.args.k L.k1 L.k2 L.z) fun _ ⟨hw, f, k⟩ => ⟨h.hdr hw f k, f, k⟩

theorem G.setWid_ok {I : RpIn} {m₀ : Mem} {w : Nat} {c : Bool} {s : State} (h : G I m₀ w c s) (L : RpLens I) :
    WP isa (.block setWid) s fun t => G I m₀ (Wk I.k) c t ∧ Frm I.B hdrW s.mem t.mem ∧ Keep [.x3, .x4, .x12] s t :=
  WP.mono (Rd.setWid_ok h.ws.scr h.ws.x0 h.args.k L.k1 L.k2 L.z) fun _ ⟨hw, f, k⟩ => ⟨h.hdr hw f k, f, k⟩

/-- `andMask`: the mask in `x15` and'ed into `sMask`. -/
theorem andMask_ok {I : RpIn} {m₀ : Mem} {w : Nat} {c c' : Bool} {s : State} (h : G I m₀ w c s)
    (h15 : s.gpr .x15 = mask c') :
    WP isa (.block andMask) s fun t => G I m₀ w (c && c') t ∧ Outside I.B (8 * Public.sMask) 8 s.mem t.mem ∧
      Keep [.x3] s t := by
  have hn := h.ws.scr.nowrap
  have h256 := h.ws.h256
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.mem = s.mem.writeW (off I.B (8 * Public.sMask)) (mask (c && c')))
    ?_ (by decide) (by decide) (by decide +kernel)) fun t ⟨hm, k⟩ => ⟨h.store hm k (by decide), by
      rw [hm]; exact writeW_outside s.mem I.B _ (by simp only [Public.sMask, sFn]; omega), k⟩
  brun [andMask, h.ws.x0, hdr_enc (show Public.sMask < 32 by decide),
    h.ws.scr.ld (d := 8 * Public.sMask) (by simp only [Public.sMask, sFn]; omega),
    h.ws.scr.st (d := 8 * Public.sMask) (by simp only [Public.sMask, sFn]; omega), h.msk, h15, mask_and']

/-! ## Ranges -/

/-- Array `j`'s first `k` words are apart from array `i`'s first `n` bytes. -/
theorem rd_sep {w i j k n : Nat} (h : j ≠ i) (hk : k ≤ w + 2) (hn : n ≤ 8 * (w + 2)) :
    slot w j + 8 * k ≤ slot w i ∨ slot w i + n ≤ slot w j := by
  have := slot_sep (w := w) h; omega

/-- Array `j`'s words are apart from the header slot `i`. -/
theorem hd_sep {w j k i : Nat} (hi : i < 32) : slot w j + 8 * k ≤ 8 * i ∨ 8 * i + 8 ≤ slot w j :=
  .inr (hdr_lt_slot w j hi)

/-- Array `j`'s first `k` words are in the address space. -/
theorem G.bnd {I : RpIn} {m₀ : Mem} {w : Nat} {c : Bool} {s : State} (h : G I m₀ w c s) {j k : Nat} (hj : j < 16)
    (hk : k ≤ w + 2) : slot w j + 8 * k ≤ 2 ^ 64 := by
  have := h.ws.sl hj; have := h.ws.scr.nowrap; omega

end VG.Proof.Rsa.AArch64.Rd
