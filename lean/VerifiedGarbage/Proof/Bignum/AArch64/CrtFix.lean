import VerifiedGarbage.Proof.Rsa.Ranges
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
import VerifiedGarbage.Proof.Bignum.AArch64.CrtRows
import VerifiedGarbage.Proof.Bignum.AArch64.R2
import VerifiedGarbage.Proof.Bignum.AArch64.Setup

/-!
# `vg_rsa_private_crt` on AArch64: the fixes and the products

`primeFix`, in a prime's workspace, replaces the prime by 3 where the mask is
clear and computes its `-X⁻¹` and the number 1 (`primeFix_ok`);
`pqProduct` leaves `p q` in the modulus' accumulators (`pqProduct_ok`), and
the start of `finish` `m_q + h q` (`finishSum_ok`).
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

/-! ## The fixes of a prime -/

/-- The mask from the modulus' header into `sMaskX`. -/
def fixMask : List Instr := [ldh .x5 Crt.sLink, ldw .x5 .x5 sMask, sth .x5 Crt.sMaskX]

/-- The fix of the low word of the prime: or'ed with 3 where the mask is
clear. -/
def fixLow : List Instr :=
  [movi .x4 3, .logic .and .x .x5 .x15 .x4, .logic .eor .x .x5 .x5 .x4, ldh .x16 (sArr aN), ld .x3 .x16,
    .logic .orr .x .x3 .x3 .x5, st .x3 .x16]

/-- `-X⁻¹` into the header, and the operands of `setWord`. -/
def fixTail : List Instr := [sth .x15 sMinv, ldh .x12 sW, movi .x9 1, movi .x13 0]

theorem primeFix_eq : primeFix =
    ([.block fixMask] : List (Prog isa)) ++ maskArr aN ++
      ([.block (fixLow ++ minv ++ fixTail), setWord aOne] : List (Prog isa)) := rfl

/-- The low word of the fixed prime. -/
theorem fixWord (c : Bool) (x : BitVec 64) :
    x &&& mask c ||| (mask c &&& BitVec.setWidth 64 (3#16) ^^^ BitVec.setWidth 64 (3#16)) =
      if c then x else 3 := by
  cases c
  · rw [mask_false, show x &&& (0 : BitVec 64) = 0 from BitVec.and_zero]
    show _ = (3 : BitVec 64); decide
  · rw [mask_true, BitVec.and_allOnes, BitVec.allOnes_and, BitVec.xor_self, BitVec.or_zero]; rfl

/-- `primeFix`'s first step: the mask from the modulus' header. -/
theorem fixMask_ok {s : State} {B : Addr} {Z o w wx : Nat} {mi : BitVec 64} {c : Bool}
    (hc : SubCtx s B Z o w wx mi) (hM : word s.mem B (8 * sMask) = mask c) :
    WP isa (.block fixMask) s fun t =>
      t.mem = s.mem.writeW (off (off B o) (8 * Crt.sMaskX)) (mask c) ∧ Keep [.x5] s t := by
  refine WP.keep [.x5] (Q := fun t => t.mem = s.mem.writeW (off (off B o) (8 * Crt.sMaskX)) (mask c)) ?_
    (by decide) (by decide) (by decide +kernel)
  rw [off_off]
  brun [fixMask, ldw, hc.x0, hdr_enc (show Crt.sLink < 32 by decide), hdr_enc (show sMask < 32 by decide),
    hdr_enc (show Crt.sMaskX < 32 by decide), hc.ld' (show Crt.sLink < 32 by decide), hc.link',
    hc.ldn (show sMask < 32 by decide), hM, hc.st' (show Crt.sMaskX < 32 by decide)]

/-- The fix of the low word of the prime (the masked `x`). -/
theorem fixLow_ok {t : State} {G : Addr} {Zx wx : Nat} {mi : BitVec 64} {c : Bool} {x : BitVec 64}
    (hg : Good t G Zx wx mi) (hZ : slot wx 8 ≤ Zx) (h15 : t.gpr .x15 = mask c)
    (hx : word t.mem G (slot wx aN) = x &&& mask c) :
    WP isa (.block fixLow) t fun t' =>
      (t'.gpr .x3 = if c then x else 3) ∧ t'.mem = t.mem.writeW (off G (slot wx aN)) (if c then x else 3) ∧
      Keep [.x3, .x4, .x5, .x16] t t' := by
  have hN := Nat.le_trans (slot_le (w := wx) (show aN < 8 by decide)) hZ
  refine WP.mono (WP.keep [.x3, .x4, .x5, .x16] (Q := fun t' => (t'.gpr .x3 = if c then x else 3) ∧
    t'.mem = t.mem.writeW (off G (slot wx aN)) (if c then x else 3)) ?_ (by decide) (by decide) (by decide +kernel))
    fun t' ⟨⟨h1, h2⟩, k⟩ => ⟨h1, h2, k⟩
  brun [fixLow, hg.x0, h15, hdr_enc (sArr_lt (show aN < 8 by decide)), hg.ld hZ (sArr_lt (show aN < 8 by decide)),
    hg.hdr.harr aN (by decide), hg.scr.ld (show slot wx aN + 8 ≤ Zx by omega_arith),
    hg.scr.st (show slot wx aN + 8 ≤ Zx by omega_arith), hx, fixWord]

/-- The fix of the low word, `-X⁻¹` into the header and `setWord`'s operands. -/
theorem fixBlock_ok {t : State} {G : Addr} {Zx wx : Nat} {mi : BitVec 64} {c : Bool} {x : BitVec 64}
    (hg : Good t G Zx wx mi) (hZ : slot wx 8 ≤ Zx) (h15 : t.gpr .x15 = mask c)
    (hx : word t.mem G (slot wx aN) = x &&& mask c) (hodd : (if c then x else 3).toNat % 2 = 1) :
    WP isa (.block (fixLow ++ minv ++ fixTail)) t fun t' =>
      ((if c then x else 3).toNat * (t'.gpr .x15).toNat + 1) % 2 ^ 64 = 0 ∧
      t'.mem = (t.mem.writeW (off G (slot wx aN)) (if c then x else 3)).writeW (off G (8 * sMinv)) (t'.gpr .x15) ∧
      t'.gpr .x12 = BitVec.ofNat 64 wx ∧ (t'.gpr .x9).toNat = 1 ∧ t'.gpr .x13 = BitVec.ofNat 64 0 ∧
      Keep mmRegs t t' := by
  have hn := hg.scr.nowrap
  have hN := Nat.le_trans (slot_le (w := wx) (show aN < 8 by decide)) hZ
  have hW := hdr_lt_slot wx aN (show sW < 32 by decide)
  have hW' := hdr_lt_slot wx aN (show sMinv < 32 by decide)
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (fixLow_ok hg hZ h15 hx) fun t₁ ⟨h3, hm₁, k₁⟩ => ?_
  refine WP.mono (minv_ok t₁ (by rw [h3]; exact hodd)) fun t₂ ⟨hinv, k₂, hm₂⟩ => ?_
  rw [h3] at hinv
  have k12 := k₁.trans k₂
  have h0₂ : t₂.gpr .x0 = G := (k12.gpr .x0 (by decide)).trans hg.x0
  have hs₂ : Scr t₂ G Zx := hg.scr.congr k12.wr
  have hw₂ : word t₂.mem G (8 * sW) = BitVec.ofNat 64 wx := by
    rw [hm₂, hm₁, (writeW_outside t.mem G _ (by omega_arith)).word (by omega_arith) (by omega_arith)]
    exact hg.hdr.hw
  have hw₂' : word (t₂.mem.writeW (off G (8 * sMinv)) (t₂.gpr .x15)) G (8 * sW) = BitVec.ofNat 64 wx := by
    rw [(writeW_outside t₂.mem G _ (by omega_arith)).word (by unfold sW sMinv; omega_arith) (by omega_arith)]; exact hw₂
  refine WP.mono (WP.keep [.x9, .x12, .x13] (c := .block fixTail) (Q := fun t' =>
      t'.mem = t₂.mem.writeW (off G (8 * sMinv)) (t₂.gpr .x15) ∧ t'.gpr .x12 = BitVec.ofNat 64 wx ∧
      (t'.gpr .x9).toNat = 1 ∧ t'.gpr .x13 = BitVec.ofNat 64 0)
    (by brun [fixTail, h0₂, hdr_enc (show sMinv < 32 by decide), hdr_enc (show sW < 32 by decide),
      hs₂.st (show 8 * sMinv + 8 ≤ Zx by have := hdr_lt_slot wx 8 (show sMinv < 32 by decide); omega_arith),
      hs₂.ld (show 8 * sW + 8 ≤ Zx by have := hdr_lt_slot wx 8 (show sW < 32 by decide); omega_arith), hw₂'])
    (by decide) (by decide) (by decide +kernel)) fun t₃ ⟨⟨hm₃, h12, h9, h13⟩, k₃⟩ => ?_
  have h15₃ : t₃.gpr .x15 = t₂.gpr .x15 := k₃.gpr .x15 (by decide)
  refine ⟨by rw [h15₃]; exact hinv, by rw [hm₃, hm₂, hm₁, h15₃], h12, h9, h13, (k12.trans k₃).mono (by decide)⟩

/-- In a prime's workspace (`c` the validity mask in the modulus' `sMask`):
the mask into `sMaskX`, `X := c ? X : 3`, `-X⁻¹` and the number 1. -/
theorem primeFix_ok {s : State} {B : Addr} {Z o w wx : Nat} {mi : BitVec 64} {c : Bool} {X : Nat}
    (hc : SubCtx s B Z o w wx mi) (hw2 : 2 ≤ wx) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (hM : word s.mem B (8 * sMask) = mask c) (hX : wv s.mem (off B o) (slot wx aN) wx = X)
    (hodd : c = true → X % 2 = 1) :
    WP isa (seqs primeFix) s fun t => ∃ minv', SubCtx t B Z o w wx minv' ∧
      wv t.mem (off B o) (slot wx aN) wx = (if c then X else 3) ∧
      ((word t.mem (off B o) (slot wx aN)).toNat * minv'.toNat + 1) % 2 ^ 64 = 0 ∧
      wv t.mem (off B o) (slot wx aOne) wx = 1 ∧ word t.mem (off B o) (8 * Crt.sMaskX) = mask c ∧
      Frm (off B o) [(slot wx aN, 8 * (wx + 2)), (slot wx aOne, 8 * (wx + 2)), (8 * Crt.sMaskX, 8), (8 * sMinv, 8)]
        s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hc.scr.nowrap
  have hi := hc.hi
  have hlo := hc.lo
  have hGn : (off B o).toNat + slot wx 8 ≤ 2 ^ 64 := hc.good.scr.nowrap
  have sN := slot_le (w := wx) (show aN < 8 by decide)
  have sO := slot_le (w := wx) (show aOne < 8 by decide)
  have hN0 := hdr_lt_slot wx aN (show 31 < 32 by decide)
  have hO0 := hdr_lt_slot wx aOne (show 31 < 32 by decide)
  have sNO := Rsa.slot_lt (w := wx) (show aN < aOne by decide)
  have eMX : Crt.sMaskX = 24 := rfl
  have eMi : sMinv = 7 := rfl
  rw [primeFix_eq]
  refine wp_seqs_append (by simp) (by simp) ?_
  refine wp_seqs_append (by simp) (by simp [maskArr]) ?_
  simp only [seqs]
  -- The mask.
  refine WP.mono (fixMask_ok hc hM) fun s₁ ⟨hm₁, k₁⟩ => ?_
  have o₁ := writeW_outside s.mem (off B o) (d := 8 * Crt.sMaskX) (mask c) (by decide)
  rw [← hm₁] at o₁
  have f₁ : Frm (off B o) [(8 * Crt.sMaskX, 8)] s.mem s₁.mem := Frm.of_outside o₁ (by simp)
  have hc₁ := hc.of_frm f₁ (fun r hr => by rw [List.mem_singleton.mp hr, eMX]; omega_arith) k₁.wr (k₁.gpr .x0 (by decide))
  have hMX₁ : word s₁.mem (off B o) (8 * Crt.sMaskX) = mask c := by rw [hm₁]; exact word_writeW_self _ _ _ _
  have hX₁ : wv s₁.mem (off B o) (slot wx aN) wx = X := by
    rw [o₁.wv (Or.inr (by omega_arith)) (by omega_arith)]; exact hX
  -- `X &&&= mask`.
  refine WP.mono (maskArr_ok hc₁.good (Nat.le_refl _) (by omega_arith) (by omega_arith) (show aN < 8 by decide) hMX₁)
    fun s₃ ⟨hd₃, _, ho₃, h15₃, k₃⟩ => ?_
  have f₃ : Frm (off B o) [(slot wx aN, 8 * (wx + 2))] s₁.mem s₃.mem :=
    Frm.of_outside (ho₃.mono (o' := slot wx aN) (n' := 8 * (wx + 2)) (Nat.le_refl _) (by omega_arith)) (by simp)
  have hc₃ : SubCtx s₃ B Z o w wx mi := hc₁.of_frm f₃ (fun r hr => by
      rw [List.mem_singleton.mp hr]; omega_arith) k₃.wr (k₃.gpr .x0 (by decide))
  -- The low word, `-X⁻¹` and the operands of `setWord`.
  have hx₃ : word s₃.mem (off B o) (slot wx aN) = word s₁.mem (off B o) (slot wx aN) &&& mask c := by
    have := hd₃ 0 (by omega_arith); rw [Nat.mul_zero, Nat.add_zero] at this; exact this
  have hodd₃ : (if c then word s₁.mem (off B o) (slot wx aN) else 3).toNat % 2 = 1 := by
    cases c
    · show (3 : BitVec 64).toNat % 2 = 1; decide
    · show (word s₁.mem (off B o) (slot wx aN)).toNat % 2 = 1
      rw [← wv_mod64 _ _ _ (show 1 ≤ wx by omega_arith), hX₁, Nat.mod_mod_of_dvd _ (by decide)]; exact hodd rfl
  refine WP.seq (WP.mono (fixBlock_ok hc₃.good (Nat.le_refl _) h15₃ hx₃ hodd₃)
    fun s₄ ⟨hinv, hm₄, h12₄, h9₄, h13₄, k₄⟩ => ?_)
  -- What changed so far.
  have o₄a := writeW_outside s₃.mem (off B o) (d := slot wx aN) (if c then word s₁.mem (off B o) (slot wx aN) else 3)
    (by omega_arith)
  have o₄b := writeW_outside (s₃.mem.writeW (off (off B o) (slot wx aN))
    (if c then word s₁.mem (off B o) (slot wx aN) else 3)) (off B o) (d := 8 * sMinv) (s₄.gpr .x15) (by decide)
  rw [← hm₄] at o₄b
  have f₁₄ : Frm (off B o) ([(slot wx aN, 8 * (wx + 2))] ++ [(8 * sMinv, 8)]) s₁.mem s₄.mem :=
    (f₃.trans
      (Frm.of_outside (o₄a.mono (o' := slot wx aN) (n' := 8 * (wx + 2)) (Nat.le_refl _) (by omega_arith)) (by simp))).append
      (Frm.of_outside o₄b (by simp))
  have hh₄ : ∀ i < 32, i ≠ sMinv → word s₄.mem (off B o) (8 * i) = word s₁.mem (off B o) (8 * i) :=
    fun i hi' hne => f₁₄.word_eq (fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · omega_arith
      · rw [eMi] at hne ⊢; omega_arith) (by omega_arith)
  have hH₄ : Hdr s₄.mem (off B o) wx (s₄.gpr .x15) :=
    ⟨(hh₄ _ (by decide) (by decide)).trans hc₁.hdr.hw, by rw [hm₄]; exact word_writeW_self _ _ _ _,
      fun j hj => (hh₄ _ (by unfold sArr; omega_arith) (by unfold sArr; rw [eMi]; omega_arith)).trans (hc₁.hdr.harr j hj)⟩
  have K₄ := k₃.trans k₄
  have h0₄ : s₄.gpr .x0 = off B o := (K₄.gpr .x0 (by decide)).trans hc₁.x0
  have hs₄ : Scr s₄ (off B o) (slot wx 8) := hc₁.good.scr.congr K₄.wr
  refine WP.mono (setWord_ok hs₄ h0₄ hH₄ (Nat.le_refl _) h12₄ (by omega_arith) (o := aOne) (by decide) (i := 0)
    (by omega_arith) h13₄) fun t ⟨hone, ho₇, k₇⟩ => ?_
  have f₇ : Frm (off B o) [(slot wx aOne, 8 * (wx + 2))] s₄.mem t.mem := Frm.of_outside ho₇ (by simp)
  have f₁t := f₁₄.append f₇
  have F := f₁.append f₁t
  have hF : ∀ r ∈ [(8 * Crt.sMaskX, 8)] ++ ([(slot wx aN, 8 * (wx + 2))] ++ [(8 * sMinv, 8)] ++
      [(slot wx aOne, 8 * (wx + 2))]), 8 * 6 + 8 ≤ r.1 ∧ r.1 + r.2 ≤ slot wx 8 := fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp only [eMX, eMi] <;> omega_arith
  have hFw : ∀ i < 32, i ≠ sMinv → i ≠ Crt.sMaskX → word t.mem (off B o) (8 * i) = word s.mem (off B o) (8 * i) :=
    fun i hi' h1 h2 => F.word_eq (fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [eMi] at h1; rw [eMX] at h2
      rcases hr with rfl | rfl | rfl | rfl <;> simp only [eMX, eMi] <;> omega_arith) (by omega_arith)
  have hFb : ∀ i < 32, word t.mem B (8 * i) = word s.mem B (8 * i) := fun i hi' =>
    F.word_below (L := slot wx 8) (fun r hr => (hF r hr).2) (by omega_arith) (by unfold slot hdrBytes at hi; omega_arith)
      (by have := hdr_lt_slot w 8 hi'; omega_arith)
  have K := (k₁.trans K₄).trans k₇
  have hN₄ : ∀ {d k : Nat}, slot wx aN ≤ d → d + 8 * k ≤ slot wx aN + 8 * (wx + 2) →
      wv t.mem (off B o) d k = wv s₄.mem (off B o) d k := fun h1 h2 =>
    f₇.wv_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; omega_arith) (by omega_arith)
  have hw₀ : word s₄.mem (off B o) (slot wx aN) = if c then word s₁.mem (off B o) (slot wx aN) else 3 := by
    rw [o₄b.word (Or.inr (by rw [eMi]; omega_arith)) (by omega_arith)]
    exact word_writeW_self _ _ _ _
  have hup : ∀ i < wx, i ≠ 0 → word s₄.mem (off B o) (slot wx aN + 8 * i) =
      word s₁.mem (off B o) (slot wx aN + 8 * i) &&& mask c := fun i hi' hne => by
    rw [o₄b.word (Or.inr (by rw [eMi]; omega_arith)) (by omega_arith),
      o₄a.word (Or.inr (by omega_arith)) (by omega_arith), hd₃ i hi']
  refine ⟨s₄.gpr .x15, ⟨hc.scr.congr K.wr, (K.gpr .x0 (by decide)).trans hc.x0,
    ⟨(hFw _ (by decide) (by decide) (by decide)).trans hc.hdr.hw,
      by rw [← hH₄.hminv]; exact f₇.word_eq (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; rw [eMi]; omega_arith) (by omega_arith),
      fun j hj => (hFw _ (by unfold sArr; omega_arith) (by unfold sArr; rw [eMi]; omega_arith)
        (by unfold sArr; rw [eMX]; omega_arith)).trans (hc.hdr.harr j hj)⟩,
    (hFw _ (by decide) (by decide) (by decide)).trans hc.link, (hFb _ (by decide)).trans hc.nw,
    fun j hj => (hFb _ (by unfold sArr; omega_arith)).trans (hc.narr j hj), hc.lo, hc.hi⟩, ?_, ?_, ?_, ?_, ?_,
    K.mono (by decide)⟩
  · rw [hN₄ (Nat.le_refl _) (by omega_arith)]
    cases c
    · rw [wv_single _ _ _ (i := 0) wx (by omega_arith) fun q hq hne => by
        rw [hup q hq hne, mask_false]; exact BitVec.and_zero, Nat.mul_zero, Nat.add_zero, hw₀]
      rfl
    · rw [← hX₁]
      refine wv_congr fun i hi' => ?_
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · rw [Nat.mul_zero, Nat.add_zero, hw₀]; rfl
      · rw [hup i hi' (by omega_arith), mask_true, BitVec.and_allOnes]
  · rw [f₇.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; omega_arith) (by omega_arith), hw₀]
    exact hinv
  · rw [hone, h9₄]
  · rw [f₁t.word_eq (fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [eMX, eMi] <;> omega_arith) (by omega_arith)]
    exact hMX₁
  · exact F.mono fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl <;> simp

/-! ## Products into the modulus' accumulators -/

theorem accs_le (w : Nat) : slot w aAcc + 8 * (2 * w + 2) ≤ slot w 8 := by
  have := slot_le (w := w) (show aTmp < 8 by decide)
  simp only [slot, aTmp, aAcc] at this ⊢; omega_arith

theorem zeroAccStep_ok {s : State} {B : Addr} {Z eA N : Nat} (h7 : s.gpr .x7 = 0) (hA : eA + 8 * N ≤ Z)
    {j : Nat} (hj : j < N) {t : State} (hI : ZeroInv s B Z eA j t) :
    WP isa (.block ([st .x7 .x16, next .x16] ++ ([.subImm .x .x14 .x14 1] : List Instr))) t
      fun t' => ZeroInv s B Z eA (j + 1) t' ∧ t'.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 := by
  have hn := hI.scr.nowrap
  have t7 : t.gpr .x7 = 0 := (hI.keep.gpr .x7 (by decide)).trans h7
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x16] (Q := fun t₁ => t₁.mem = t.mem.writeW (off B (eA + 8 * j)) (0 : BitVec 64) ∧
    t₁.gpr .x16 = off B (eA + 8 * j + 8))
    (by brun [hI.x16, t7, hI.scr.st (show eA + 8 * j + 8 ≤ Z by omega_arith)]) (by decide) (by decide)
      (by decide +kernel)) fun t₁ ⟨⟨hm, h16'⟩, k₁⟩ => ?_
  refine WP.mono (dec_ok t₁ .x14) fun t' ⟨⟨h14', hm', _⟩, k'⟩ => ⟨?_, by rw [h14', k₁.gpr .x14 (by decide)]⟩
  refine ⟨hI.scr.congr (k'.wr.trans k₁.wr), (hI.keep.trans (k₁.trans k')).mono (by decide),
    by rw [k'.gpr .x16 (by decide), h16', Nat.mul_succ, Nat.add_assoc], ?_, ?_⟩
  · rw [hm', hm]
    intro x hx
    rw [writeW_outside t.mem B _ (by omega_arith) x (by omega_arith)]
    exact hI.out x (by omega_arith)
  · rw [hm', hm, wv_writeW_top _ _ _ _ _ (by omega_arith), hI.val]
    rfl

/-- `zeroAccs`: the `2 w + 2` words from `aAcc` cleared. -/
theorem zeroAccs_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} (hg : Good s B Z w mi)
    (hZ : slot w 8 ≤ Z) (hw' : w < 2 ^ 30) :
    WP isa (seqs zeroAccs) s fun t => (∀ k < 2 * w + 2, word t.mem B (slot w aAcc + 8 * k) = 0) ∧
      Outside B (slot w aAcc) (8 * (2 * w + 2)) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hg.scr.nowrap
  have hA := accs_le w
  unfold zeroAccs
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.x7, .x12, .x14, .x16] (Q := fun t => t.gpr .x16 = off B (slot w aAcc) ∧
      t.gpr .x14 = BitVec.ofNat 64 (w + w + 2) ∧ t.gpr .x7 = 0 ∧ t.mem = s.mem)
    (by brun [hg.x0, hdr_enc (sArr_lt (show aAcc < 8 by decide)), hdr_enc (show sW < 32 by decide),
      hg.ld hZ (sArr_lt (show aAcc < 8 by decide)), hg.ld hZ (show sW < 32 by decide),
      hg.hdr.harr aAcc (by decide), hg.hdr.hw, ofNat_add_ofNat]) (by decide) (by decide) (by decide +kernel))
    fun s₁ ⟨⟨h16, h14, h7, hm₁⟩, k₁⟩ => ?_)
  rw [show w + w + 2 = 2 * w + 2 by omega_arith] at h14
  refine WP.mono (wp_countdown (N := 2 * w + 2) (by omega_arith) (by omega_arith) (ZeroInv s₁ B Z (slot w aAcc))
    (fun j hj t hI _ => zeroAccStep_ok h7 (by omega_arith) hj hI)
    ⟨hg.scr.congr k₁.wr, Keep.refl _ _, by rw [h16]; rfl, Outside.refl _ _ _ _, rfl⟩ h14) fun t hI => ?_
  have ho := hI.out
  rw [hm₁] at ho
  refine ⟨fun k hk => ?_, ho, (k₁.trans hI.keep).mono (by decide)⟩
  have hv := hI.val
  rw [wv_eq_zero_iff] at hv
  exact hv k hk

/-- The operands of `mulRows`: `[x11]` the array `ja` of `p`'s workspace
(`x13` its words), `[x9]` `q`'s `aN` (`x12` its words), `x8` the modulus'
accumulator, `x7 = 0`. -/
def rowsHdr (ja : Nat) : List Instr :=
  [ldh .x5 Crt.sWsP, ldw .x11 .x5 (sArr ja), ldw .x13 .x5 sW, ldh .x5 Crt.sWsQ, ldw .x9 .x5 (sArr aN),
    ldw .x12 .x5 sW, ldh .x8 (sArr aAcc), movi .x7 0]

theorem rowsHdr_ok {s : State} {B : Addr} {Z w op oq wp wq ja : Nat} {A Q : Addr} (hs : Scr s B Z)
    (h0 : s.gpr .x0 = B) (hacc : word s.mem B (8 * sArr aAcc) = off B (slot w aAcc))
    (hp : word s.mem B (8 * Crt.sWsP) = off B op) (hq : word s.mem B (8 * Crt.sWsQ) = off B oq)
    (hpw : word s.mem B (op + 8 * sW) = BitVec.ofNat 64 wp)
    (hqw : word s.mem B (oq + 8 * sW) = BitVec.ofNat 64 wq)
    (hpa : word s.mem B (op + 8 * sArr ja) = A) (hqa : word s.mem B (oq + 8 * sArr aN) = Q)
    (hja : ja < 8) (hlo : slot w 8 ≤ op) (hop : op + slot wp 8 + tabBytes wp ≤ oq) (hoq : oq + slot wq 8 + tabBytes wq ≤ Z) :
    WP isa (.block (rowsHdr ja)) s fun t =>
      t.gpr .x11 = A ∧ t.gpr .x13 = BitVec.ofNat 64 wp ∧ t.gpr .x9 = Q ∧ t.gpr .x12 = BitVec.ofNat 64 wq ∧
      t.gpr .x8 = off B (slot w aAcc) ∧ t.gpr .x7 = 0 ∧ t.mem = s.mem ∧ Keep mmRegs s t := by
  have hn := hs.nowrap
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have h8p := hdr_lt_slot wp 8 (show 31 < 32 by decide)
  have h8q := hdr_lt_slot wq 8 (show 31 < 32 by decide)
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega_arith)
  have hlp : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (op + 8 * i)) 8 := fun i hi => hs.ld (by omega_arith)
  have hlq : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (oq + 8 * i)) 8 := fun i hi => hs.ld (by omega_arith)
  refine WP.mono (WP.keep [.x5, .x7, .x8, .x9, .x11, .x12, .x13] (Q := fun t => t.gpr .x11 = A ∧
      t.gpr .x13 = BitVec.ofNat 64 wp ∧ t.gpr .x9 = Q ∧ t.gpr .x12 = BitVec.ofNat 64 wq ∧
      t.gpr .x8 = off B (slot w aAcc) ∧ t.gpr .x7 = 0 ∧ t.mem = s.mem)
    (by
      brun [rowsHdr, ldw, h0, hdr_enc (show Crt.sWsP < 32 by decide), hdr_enc (show Crt.sWsQ < 32 by decide),
        hdr_enc (sArr_lt hja), hdr_enc (sArr_lt (show aN < 8 by decide)), hdr_enc (sArr_lt (show aAcc < 8 by decide)),
        hdr_enc (show sW < 32 by decide), hl Crt.sWsP (by decide), hl Crt.sWsQ (by decide),
        hl (sArr aAcc) (by decide), hp, hq, hacc, hlp (sArr ja) (sArr_lt hja), hlp sW (by decide),
        hlq (sArr aN) (by decide), hlq sW (by decide), hpw, hqw, hpa, hqa])
    rfl rfl rfl)
    fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2, k.mono (by decide)⟩

theorem pqProduct_eq :
    pqProduct = zeroAccs ++ ([.block (rowsHdr aN), mulRows] : List (Prog isa)) := rfl

/-- `p q` into the modulus' accumulators (`2 w + 2` words). -/
theorem pqProduct_ok {s : State} {B : Addr} {Z w op oq wp wq : Nat} {mi : BitVec 64}
    (hg : Good s B Z w mi) (hw' : w < 2 ^ 29)
    (hp : word s.mem B (8 * Crt.sWsP) = off B op) (hq : word s.mem B (8 * Crt.sWsQ) = off B oq)
    (hpw : word s.mem B (op + 8 * sW) = BitVec.ofNat 64 wp)
    (hqw : word s.mem B (oq + 8 * sW) = BitVec.ofNat 64 wq)
    (hpa : word s.mem B (op + 8 * sArr aN) = off B (op + slot wp aN))
    (hqa : word s.mem B (oq + 8 * sArr aN) = off B (oq + slot wq aN))
    (hlo : slot w 8 ≤ op) (hop : op + slot wp 8 + tabBytes wp ≤ oq) (hoq : oq + slot wq 8 + tabBytes wq ≤ Z)
    (hwp : 1 ≤ wp) (hwp' : wp ≤ w) (hwq : 1 ≤ wq) (hwq' : wq ≤ w) :
    WP isa (seqs pqProduct) s fun t =>
      wv t.mem B (slot w aAcc) (2 * w + 2) = wv s.mem B (op + slot wp aN) wp * wv s.mem B (oq + slot wq aN) wq ∧
      Outside B (slot w aAcc) (8 * (2 * w + 2)) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hg.scr.nowrap
  have hA := accs_le w
  have h8 := hdr_lt_slot w 0 (show 31 < 32 by decide)
  have hpN := slot_le (w := wp) (show aN < 8 by decide)
  have hqN := slot_le (w := wq) (show aN < 8 by decide)
  have hpS := hdr_lt_slot wp 8 (show 31 < 32 by decide)
  have hqS := hdr_lt_slot wq 8 (show 31 < 32 by decide)
  have eW : sW = 6 := rfl
  have eN : sArr aN = 8 := rfl
  rw [pqProduct_eq]
  refine wp_seqs_append (by simp [zeroAccs]) (by simp)
    (WP.mono (zeroAccs_ok hg (by omega_arith) (by omega_arith)) fun s₁ ⟨hz₁, ho₁, k₁⟩ => ?_)
  have hs₁ := hg.scr.congr k₁.wr
  have hh : ∀ i < 32, word s₁.mem B (8 * i) = word s.mem B (8 * i) := fun i hi =>
    ho₁.word (Or.inl (by have := hdr_lt_slot w aAcc hi; omega_arith)) (by omega_arith)
  have hab : ∀ {d : Nat}, slot w 8 ≤ d → d + 8 ≤ 2 ^ 64 → word s₁.mem B d = word s.mem B d :=
    fun hd hd' => ho₁.word (Or.inr (by omega_arith)) hd'
  simp only [seqs]
  refine WP.seq (WP.mono (rowsHdr_ok hs₁ ((k₁.gpr .x0 (by decide)).trans hg.x0)
    ((hh _ (by decide)).trans (hg.hdr.harr aAcc (by decide))) ((hh _ (by decide)).trans hp)
    ((hh _ (by decide)).trans hq) ((hab (by omega_arith) (by omega_arith)).trans hpw)
    ((hab (by omega_arith) (by omega_arith)).trans hqw) ((hab (by omega_arith) (by omega_arith)).trans hpa)
    ((hab (by omega_arith) (by omega_arith)).trans hqa) (by decide) hlo hop hoq)
    fun s₂ ⟨h11, h13, h9, h12, h8, h7, hm₂, k₂⟩ => ?_)
  have hz₂ : wv s₂.mem B (slot w aAcc) (wp + wq + 2) = 0 := by
    rw [hm₂, wv_eq_zero_iff]; exact fun k hk => hz₁ k (by omega_arith)
  refine WP.mono (mulRows_ok (hs₁.congr k₂.wr) h11 h9 h13 h12 h8 h7 hwp hwq (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) (Or.inr (by omega_arith)) (Or.inr (by omega_arith)) (by rw [hz₂]; exact Nat.two_pow_pos _))
    fun t ⟨hv, ho, k₃⟩ => ⟨?_, ?_, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  · rw [show 2 * w + 2 = (wp + wq + 2) + (2 * w - wp - wq) by omega_arith, wv_add, hv, hz₂,
      ho.wv (Or.inr (Nat.le_refl _)) (by omega_arith), hm₂, (wv_eq_zero_iff _ _ _ (2 * w - wp - wq)).mpr fun k hk => by
        rw [Nat.add_assoc, ← Nat.mul_add]; exact hz₁ _ (by omega_arith), Nat.mul_zero, Nat.add_zero, Nat.zero_add,
      ho₁.wv (Or.inr (by omega_arith)) (by omega_arith), ho₁.wv (Or.inr (by omega_arith)) (by omega_arith)]
  · rw [hm₂] at ho
    exact ho₁.trans (ho.mono (Nat.le_refl _) (by omega_arith))

/-- `finish`'s copy of `m_q` (`q`'s `aY`) into the modulus' accumulator. -/
def finishCopy : List Instr := [ldh .x5 Crt.sWsQ, ldw .x16 .x5 (sArr aY), ldw .x12 .x5 sW, ldh .x17 (sArr aAcc)]

/-- The first steps of `finish`: `m_q + h q` into the modulus' accumulator. -/
def finishSum : List (Prog isa) :=
  zeroAccs ++ ([.block finishCopy, copyWords, .block (rowsHdr aY), mulRows] : List (Prog isa))

theorem finish_eq : finish = finishSum ++ finish.drop 6 := rfl

/-- `m_q + h q` (`m_q` in `q`'s `aY`, `h` in `p`'s) into the modulus'
accumulators (`2 w + 2` words). -/
theorem finishSum_ok {s : State} {B : Addr} {Z w op oq wp wq : Nat} {mi : BitVec 64}
    (hg : Good s B Z w mi) (hw' : w < 2 ^ 29)
    (hp : word s.mem B (8 * Crt.sWsP) = off B op) (hq : word s.mem B (8 * Crt.sWsQ) = off B oq)
    (hpw : word s.mem B (op + 8 * sW) = BitVec.ofNat 64 wp)
    (hqw : word s.mem B (oq + 8 * sW) = BitVec.ofNat 64 wq)
    (hpy : word s.mem B (op + 8 * sArr aY) = off B (op + slot wp aY))
    (hqy : word s.mem B (oq + 8 * sArr aY) = off B (oq + slot wq aY))
    (hqa : word s.mem B (oq + 8 * sArr aN) = off B (oq + slot wq aN))
    (hlo : slot w 8 ≤ op) (hop : op + slot wp 8 + tabBytes wp ≤ oq) (hoq : oq + slot wq 8 + tabBytes wq ≤ Z)
    (hwp : 1 ≤ wp) (hwp' : wp ≤ w) (hwq : 1 ≤ wq) (hwq' : wq ≤ w) :
    WP isa (seqs finishSum) s fun t =>
      wv t.mem B (slot w aAcc) (2 * w + 2) = wv s.mem B (oq + slot wq aY) wq +
        wv s.mem B (op + slot wp aY) wp * wv s.mem B (oq + slot wq aN) wq ∧
      Outside B (slot w aAcc) (8 * (2 * w + 2)) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hg.scr.nowrap
  have hA := accs_le w
  have h8 := hdr_lt_slot w 0 (show 31 < 32 by decide)
  have hpY := slot_le (w := wp) (show aY < 8 by decide)
  have hqY := slot_le (w := wq) (show aY < 8 by decide)
  have hqN := slot_le (w := wq) (show aN < 8 by decide)
  have hpS := hdr_lt_slot wp 8 (show 31 < 32 by decide)
  have hqS := hdr_lt_slot wq 8 (show 31 < 32 by decide)
  have eW : sW = 6 := rfl
  have eN : sArr aN = 8 := rfl
  have eY : sArr aY = 14 := rfl
  refine wp_seqs_append (by simp [zeroAccs]) (by simp)
    (WP.mono (zeroAccs_ok hg (by omega_arith) (by omega_arith)) fun s₁ ⟨hz₁, ho₁, k₁⟩ => ?_)
  have hs₁ := hg.scr.congr k₁.wr
  have hh : ∀ i < 32, word s₁.mem B (8 * i) = word s.mem B (8 * i) := fun i hi =>
    ho₁.word (Or.inl (by have := hdr_lt_slot w aAcc hi; omega_arith)) (by omega_arith)
  have hab₁ : ∀ {d : Nat}, slot w 8 ≤ d → d + 8 ≤ 2 ^ 64 → word s₁.mem B d = word s.mem B d :=
    fun hd hd' => ho₁.word (Or.inr (by omega_arith)) hd'
  have h0₁ : s₁.gpr .x0 = B := (k₁.gpr .x0 (by decide)).trans hg.x0
  have hl : ∀ i < 32, InRegions (s₁.rd ++ s₁.wr) (off B (8 * i)) 8 := fun i hi => hs₁.ld (by omega_arith)
  have hlq : ∀ i < 32, InRegions (s₁.rd ++ s₁.wr) (off B (oq + 8 * i)) 8 := fun i hi => hs₁.ld (by omega_arith)
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.x5, .x12, .x16, .x17] (Q := fun t =>
      t.gpr .x16 = off B (oq + slot wq aY) ∧ t.gpr .x12 = BitVec.ofNat 64 wq ∧
      t.gpr .x17 = off B (slot w aAcc) ∧ t.mem = s₁.mem)
    (by
      brun [finishCopy, ldw, h0₁, hdr_enc (show Crt.sWsQ < 32 by decide), hdr_enc (sArr_lt (show aAcc < 8 by decide)),
        hdr_enc (sArr_lt (show aY < 8 by decide)), hdr_enc (show sW < 32 by decide),
        hl Crt.sWsQ (by decide), hl (sArr aAcc) (by decide),
        (hh _ (by decide)).trans hq, (hh _ (by decide)).trans (hg.hdr.harr aAcc (by decide)),
        hlq (sArr aY) (by decide), hlq sW (by decide), (hab₁ (by omega_arith) (by omega_arith)).trans hqy,
        (hab₁ (by omega_arith) (by omega_arith)).trans hqw]) (by decide) (by decide) (by decide +kernel))
    fun s₂ ⟨⟨h16, h12, h17, hm₂⟩, k₂⟩ => ?_)
  have hs₂ := hs₁.congr k₂.wr
  refine WP.seq (WP.mono (copyWords_ok h16 h17 h12 hwq (by omega_arith) (by omega_arith)
    (fun j hj => hs₂.ld (by omega_arith)) (fun j hj => hs₂.st (by omega_arith))
    (fun j hj b hb => by rw [ofs_off B (by omega_arith)]; omega_arith)) fun s₃ ⟨hc₃, _, ho₃, _, _, k₃⟩ => ?_)
  have hs₃ := hs₂.congr k₃.wr
  rw [hm₂] at hc₃ ho₃
  have hh₃ : ∀ i < 32, word s₃.mem B (8 * i) = word s.mem B (8 * i) := fun i hi =>
    (ho₃.word (Or.inl (by have := hdr_lt_slot w aAcc hi; omega_arith)) (by omega_arith)).trans (hh i hi)
  have hab : ∀ {d : Nat}, slot w 8 ≤ d → d + 8 ≤ 2 ^ 64 → word s₃.mem B d = word s.mem B d :=
    fun hd hd' => (ho₃.word (Or.inr (by omega_arith)) hd').trans (hab₁ hd hd')
  refine WP.seq (WP.mono (rowsHdr_ok hs₃ ((k₃.gpr .x0 (by decide)).trans ((k₂.gpr .x0 (by decide)).trans h0₁))
    ((hh₃ _ (by decide)).trans (hg.hdr.harr aAcc (by decide))) ((hh₃ _ (by decide)).trans hp)
    ((hh₃ _ (by decide)).trans hq) ((hab (by omega_arith) (by omega_arith)).trans hpw)
    ((hab (by omega_arith) (by omega_arith)).trans hqw) ((hab (by omega_arith) (by omega_arith)).trans hpy)
    ((hab (by omega_arith) (by omega_arith)).trans hqa) (by decide) hlo hop hoq)
    fun s₄ ⟨h11, h13, h9, h12', h8', h7, hm₄, k₄⟩ => ?_)
  have hmid : ∀ k < 2 * w + 2 - wq, word s₃.mem B (slot w aAcc + 8 * wq + 8 * k) = 0 := fun k hk => by
    rw [ho₃.word (Or.inr (by omega_arith)) (by omega_arith), Nat.add_assoc, ← Nat.mul_add]; exact hz₁ _ (by omega_arith)
  have hwvab : ∀ {d k : Nat}, slot w 8 ≤ d → d + 8 * k ≤ Z → wv s₃.mem B d k = wv s.mem B d k :=
    fun hd hk => (ho₃.wv (Or.inr (by omega_arith)) (by omega_arith)).trans (ho₁.wv (Or.inr (by omega_arith)) (by omega_arith))
  have hz₄ : wv s₄.mem B (slot w aAcc) (wp + wq + 2) = wv s.mem B (oq + slot wq aY) wq := by
    rw [hm₄, show wp + wq + 2 = wq + (wp + 2) by omega_arith, wv_add,
      (wv_eq_zero_iff _ _ _ (wp + 2)).mpr fun k hk => hmid k (by omega_arith),
      Nat.mul_zero, Nat.add_zero, hc₃, ho₁.wv (Or.inr (by omega_arith)) (by omega_arith)]
  have h0 : wv s₄.mem B (slot w aAcc) (wp + wq + 2) < 2 ^ (64 * (wq + 1)) := by
    rw [hz₄]
    exact Nat.lt_of_lt_of_le (wv_lt _ _ _ _) (Nat.pow_le_pow_right (by decide) (by omega_arith))
  refine WP.mono (mulRows_ok (hs₃.congr k₄.wr) h11 h9 h13 h12' h8' h7 hwp hwq (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) (Or.inr (by omega_arith)) (Or.inr (by omega_arith)) h0)
    fun t ⟨hv, ho, k₅⟩ => ⟨?_, ?_, ((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).mono (by decide)⟩
  · rw [show 2 * w + 2 = (wp + wq + 2) + (2 * w - wp - wq) by omega_arith, wv_add, hv, hz₄,
      ho.wv (Or.inr (Nat.le_refl _)) (by omega_arith), hm₄, (wv_eq_zero_iff _ _ _ (2 * w - wp - wq)).mpr fun k hk => by
        rw [show slot w aAcc + 8 * (wp + wq + 2) + 8 * k = slot w aAcc + 8 * wq + 8 * (wp + 2 + k) by omega_arith]
        exact hmid _ (by omega_arith), Nat.mul_zero, Nat.add_zero,
      hwvab (by omega_arith) (by omega_arith), hwvab (by omega_arith) (by omega_arith)]
  · rw [hm₄] at ho
    exact (ho₁.trans (ho₃.mono (Nat.le_refl _) (by omega_arith))).trans (ho.mono (Nat.le_refl _) (by omega_arith))

end VG.Proof.Bignum.AArch64
