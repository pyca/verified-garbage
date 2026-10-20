module
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Impl.MillerRabin.AArch64.Core
public import VerifiedGarbage.Proof.Rsa.AArch64.KeyWs
public import VerifiedGarbage.Proof.Framework.Contract

import VerifiedGarbage.Proof.Bignum.AArch64.CrtTab
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
import VerifiedGarbage.Proof.Rsa.Ranges
import VerifiedGarbage.Proof.Bignum.AArch64.CrtSel
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
import VerifiedGarbage.Proof.Bignum.AArch64.CrtArith
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Spec.RsaKeyGen

/-!
# A candidate on AArch64: reading Miller–Rabin's table

`mrSel_ok`: `[aXm] := T_d` for the digit `d < 16` in `kG`, each of the 16
entries selected under the mask of `j = d` (`Crt.selLoop`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen
open VG.Proof.MlKem.AArch64 (Keep count_loop)
open VG.Proof.Rsa (slot_lt)
open VG.Impl.Bignum.Public (aN aAcc aTmp aXm aY sCnt)

theorem slot_succ (w j : Nat) : slot w j + 8 * (w + 2) = slot w (j + 1) := by
  unfold slot; rw [Nat.add_mul j 1, Nat.one_mul, Nat.add_assoc]

/-- The table's entries, and `aE`, end within the working space. -/
theorem tab_fits {w Z j : Nat} (hEZ : slot w aE + 8 * (w + 2) ≤ Z) (hj : j < 16) :
    slot w (aT0 + j) + 8 * (w + 2) ≤ Z := by
  have := slot_lt (w := w) (show aT0 + j < aE by unfold aT0 aE; omega); omega

/-- An entry is apart from `aXm`. -/
theorem tab_sep_xm (w : Nat) {j : Nat} : slot w aXm + 8 * w ≤ slot w (aT0 + j) := by
  have := slot_lt (w := w) (show aXm < aT0 + j by unfold aXm aT0; omega); omega

/-- After `j` entries of `mrSel`'s loop. -/
structure SelJ (s₀ : State) (B : Addr) (Z w d : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep mmRegs s₀ t
  x2 : t.gpr .x2 = off B (slot w (aT0 + j))
  x7 : t.gpr .x7 = BitVec.setWidth 64 0#16
  x8 : t.gpr .x8 = BitVec.setWidth 64 0#16 - 1#64
  x9 : t.gpr .x9 = BitVec.ofNat 64 d
  x10 : t.gpr .x10 = BitVec.ofNat 64 j
  x11 : t.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2))
  x12 : t.gpr .x12 = BitVec.ofNat 64 w
  x13 : t.gpr .x13 = off B (slot w aXm)
  out : Outside B (slot w aXm) (8 * w) s₀.mem t.mem
  val : d < j → wv t.mem B (slot w aXm) w = wv s₀.mem B (slot w (aT0 + d)) w

/-- The mask of `j = d` and the bases of entry `j`'s selection. -/
theorem selHeadW_ok {t : State} {B : Addr} {w d j : Nat} (hd : d < 16) (hj : j < 16)
    (h9 : t.gpr .x9 = BitVec.ofNat 64 d) (h10 : t.gpr .x10 = BitVec.ofNat 64 j)
    (h7 : t.gpr .x7 = BitVec.setWidth 64 0#16) (h8 : t.gpr .x8 = BitVec.setWidth 64 0#16 - 1#64)
    (h2 : t.gpr .x2 = off B (slot w (aT0 + j))) (h12 : t.gpr .x12 = BitVec.ofNat 64 w)
    (h13 : t.gpr .x13 = off B (slot w aXm)) :
    WP isa (.block [.logic .eor .x .x3 .x10 .x9, movi .x4 1, .subs .x .x3 .x3 .x4, .csel .x .x15 .x7 .x8,
      mov .x16 .x2, mov .x17 .x13, mov .x14 .x12]) t fun t' =>
      (t'.gpr .x15 = mask (decide (j = d)) ∧ t'.gpr .x14 = BitVec.ofNat 64 w ∧
      t'.gpr .x16 = off B (slot w (aT0 + j)) ∧ t'.gpr .x17 = off B (slot w aXm) ∧ t'.mem = t.mem) ∧
      Keep [.x3, .x4, .x14, .x15, .x16, .x17] t t' := by
  refine WP.keep _ ?_ (by decide) (by decide) (by decide +kernel)
  brun [h9, h10, h7, h8, h2, h12, h13, subs_one_c, csel_mask', Bool.not_not,
    ofNat64_xor_eq (show j < 2 ^ 64 by omega) (show d < 2 ^ 64 by omega)]

/-- The next entry: `x2` up a stride, `x10 := j + 1`, `x3 := j + 1 − 16`. -/
theorem selNextW_ok {t : State} {B : Addr} {w j : Nat} (hj : j < 16)
    (h10 : t.gpr .x10 = BitVec.ofNat 64 j) (h2 : t.gpr .x2 = off B (slot w (aT0 + j)))
    (h11 : t.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2))) :
    WP isa (.block [.add .x .x2 .x2 .x11, .addImm .x .x10 .x10 1, .subImm .x .x3 .x10 16]) t fun t' =>
      (t'.gpr .x2 = off B (slot w (aT0 + (j + 1))) ∧ t'.gpr .x10 = BitVec.ofNat 64 (j + 1) ∧
      ((t'.gpr .x3).toNat ≠ 0 ↔ j + 1 ≠ 16) ∧ t'.mem = t.mem) ∧ Keep [.x2, .x3, .x10] t t' := by
  refine WP.keep _ ?_ (by decide) (by decide) (by decide +kernel)
  brun [h10, h2, h11, off_add, slot_succ, ofNat_add_ofNat]
  refine ⟨by rw [Nat.add_assoc], ?_⟩
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show j + 1 < 2 ^ 64 by omega)]
  omega

/-- Entry `j` of the selection. -/
theorem selStepW_ok {s₀ t : State} {B : Addr} {Z w d j : Nat} (hEZ : slot w aE + 8 * (w + 2) ≤ Z)
    (hw : 2 ≤ w) (hw' : w < 2 ^ 24) (hd : d < 16) (hj : j < 16) (hI : SelJ s₀ B Z w d j t) :
    WP isa (seqs [.block [.logic .eor .x .x3 .x10 .x9, movi .x4 1, .subs .x .x3 .x3 .x4, .csel .x .x15 .x7 .x8,
        mov .x16 .x2, mov .x17 .x13, mov .x14 .x12], Crt.selLoop,
      .block [.add .x .x2 .x2 .x11, .addImm .x .x10 .x10 1, .subImm .x .x3 .x10 16]]) t fun t' =>
      SelJ s₀ B Z w d (j + 1) t' ∧ ((t'.gpr .x3).toNat ≠ 0 ↔ j + 1 ≠ 16) := by
  have hn := hI.scr.nowrap
  have hT := tab_fits hEZ hj
  have hX := tab_sep_xm w (j := j)
  have hXZ : slot w aXm + 8 * (w + 2) ≤ Z := by
    have := slot_lt (w := w) (show aXm < aT0 + j by unfold aXm aT0; omega); omega
  simp only [seqs]
  refine WP.seq (WP.mono (selHeadW_ok hd hj hI.x9 hI.x10 hI.x7 hI.x8 hI.x2 hI.x12 hI.x13)
    fun t₁ ⟨⟨h15, h14, h16, h17, hm₁⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (selLoop_ok (hI.scr.congr k₁.wr) h16 h17 h14 h15 (by omega) (by omega) (by omega)
    (by omega) (Or.inl hX)) fun t₂ ⟨hv₂, o₂, k₂⟩ => ?_)
  have k12 := k₁.trans k₂
  refine WP.mono (selNextW_ok hj ((k12.gpr .x10 (by decide)).trans hI.x10) ((k12.gpr .x2 (by decide)).trans hI.x2)
    ((k12.gpr .x11 (by decide)).trans hI.x11)) fun t' ⟨⟨h2', h10', h3', hm'⟩, k'⟩ => ⟨?_, h3'⟩
  rw [hm₁] at hv₂ o₂
  have hT₀ : wv t.mem B (slot w (aT0 + j)) w = wv s₀.mem B (slot w (aT0 + j)) w :=
    hI.out.wv (by omega) (by omega)
  refine ⟨hI.scr.congr ((k12.trans k').wr), (hI.keep.trans (k12.trans k')).mono (by decide), h2',
    (k12.trans k' |>.gpr .x7 (by decide)).trans hI.x7, (k12.trans k' |>.gpr .x8 (by decide)).trans hI.x8,
    (k12.trans k' |>.gpr .x9 (by decide)).trans hI.x9, h10',
    (k12.trans k' |>.gpr .x11 (by decide)).trans hI.x11, (k12.trans k' |>.gpr .x12 (by decide)).trans hI.x12,
    (k12.trans k' |>.gpr .x13 (by decide)).trans hI.x13, ?_, fun hdj => ?_⟩
  · rw [hm']
    intro x hx
    rw [o₂ x hx]
    exact hI.out x hx
  · rw [hm', hv₂]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hdj with hlt | rfl
    · rw [decide_eq_false (by omega)]; exact hI.val hlt
    · rw [decide_eq_true rfl]; exact hT₀

/-- The selection's head: the bases, the digit and the masks' constants. -/
theorem selInitW_ok {s : State} {B : Addr} {Z w d : Nat} (h : Ws s B Z w) (hG : word s.mem B (8 * kG) = BitVec.ofNat 64 d) :
    WP isa (.block (ws ++ base aT0 .x2 ++ base aXm .x13 ++ [ldh .x9 kG, movi .x10 0, movi .x7 0, .subImm .x .x8 .x7 1]))
      s (SelJ s B Z w d 0) := by
  have hs := h.scr
  have hn := hs.nowrap
  have h256 := h.h256
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono h.ws_ok fun s₁ ⟨⟨h12, h11, m₁, _⟩, k₁⟩ => ?_
  have h0₁ : s₁.gpr .x0 = B := (k₁.gpr .x0 (by decide)).trans h.x0
  rw [WP.block_append_iff]
  refine WP.mono (base_ok aT0 .x2 h0₁ h11) fun s₂ ⟨⟨h2, m₂, _⟩, k₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base_ok aXm .x13 ((k₂.gpr .x0 (by decide)).trans h0₁) ((k₂.gpr .x11 (by decide)).trans h11))
    fun s₃ ⟨⟨h13, m₃, _⟩, k₃⟩ => ?_
  have k13 := (k₁.trans k₂).trans k₃
  refine WP.mono (WP.keep [.x7, .x8, .x9, .x10] (Q := fun t => t.gpr .x9 = BitVec.ofNat 64 d ∧
      t.gpr .x10 = BitVec.ofNat 64 0 ∧ t.gpr .x7 = BitVec.setWidth 64 0#16 ∧
      t.gpr .x8 = BitVec.setWidth 64 0#16 - 1#64 ∧ t.mem = s₃.mem) (by
    brun [(k13.gpr .x0 (by decide)).trans h.x0, hdr_enc (show kG < 32 by decide),
      (hs.congr k13.wr).ld (d := 8 * kG) (by simp only [kG]; omega), (by rw [m₃, m₂, m₁]; exact hG :
        word s₃.mem B (8 * kG) = BitVec.ofNat 64 d)])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h9, h10, h7, h8, hm⟩, k⟩ => ?_
  have k' := k13.trans k
  refine ⟨hs.congr k'.wr, k'.mono (by decide), (k₃.trans k |>.gpr .x2 (by decide)).trans (by rw [h2]; rfl), h7, h8, h9,
    h10, (k₂.trans k₃ |>.trans k |>.gpr .x11 (by decide)).trans h11,
    (k₂.trans k₃ |>.trans k |>.gpr .x12 (by decide)).trans h12, (k.gpr .x13 (by decide)).trans h13, ?_,
    fun h0 => absurd h0 (by omega)⟩
  rw [hm, m₃, m₂, m₁]; exact Outside.refl _ _ _ _

/-- `mrSel`: `[aXm] := T_d` for the digit `d` in `kG`. -/
theorem mrSel_ok {s : State} {B : Addr} {Z w d : Nat} (h : Ws s B Z w) (hEZ : slot w aE + 8 * (w + 2) ≤ Z)
    (hd : d < 16) (hG : word s.mem B (8 * kG) = BitVec.ofNat 64 d) :
    WP isa (seqs mrSel) s fun t =>
      wv t.mem B (slot w aXm) w = wv s.mem B (slot w (aT0 + d)) w ∧
      Outside B (slot w aXm) (8 * w) s.mem t.mem ∧ Scr t B Z ∧ Keep mmRegs s t := by
  simp only [mrSel, seqs]
  refine WP.seq (WP.mono (selInitW_ok h hG) fun s₁ h₁ => ?_)
  refine WP.mono (count_loop (cr := .x3) (n := 16) (by decide) (SelJ s B Z w d)
    (fun j hj t hI => selStepW_ok hEZ h.w1 h.w2 hd hj hI) h₁) fun t hI => ⟨hI.val hd, hI.out, hI.scr, hI.keep⟩

end VG.Proof.RsaKeyGen.AArch64
