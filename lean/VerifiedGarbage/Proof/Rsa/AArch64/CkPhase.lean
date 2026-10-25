module
public import VerifiedGarbage.Impl.Rsa.AArch64.CheckKey
public import VerifiedGarbage.Proof.Rsa.AArch64.CkPhaseCore
public import VerifiedGarbage.Proof.Rsa.AArch64.CrtKeyTop

import VerifiedGarbage.Proof.Rsa.AArch64.CrtKeyPhase
import VerifiedGarbage.Proof.Rsa.KeyBounds
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

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
  have hl := hs.ld (d := 8 * sl) (by omega_arith)
  refine WP.mono (WP.keep [.x13] (Q := fun t' => t'.gpr .x13 = BitVec.ofNat 64 ((yl + 7) / 8 + 1) ∧
    t'.mem = t.mem ∧ t'.c = t.c) ?_ (by rfl) (by rfl) (by rfl)) fun _ ⟨h, k⟩ => ⟨h, k.mono (by simp)⟩
  unfold topD
  brun [hdr_enc hsl, h0, hl, hh sl hsl, hy, BitVec.ofNat_add_ofNat, shr_ofNat (show yl + 7 < 2 ^ 64 by omega_arith)]
  rfl

theorem modChecks_eq (sX sXlen sDX sYlen : Nat) : modChecks sX sXlen sDX sYlen =
    loadA aM sX sXlen ++ (([.block (decA aM)] : List (Prog isa)) ++ (loadA aX sDX sXlen ++ (ltA aX aM ++ (loadA aX sD sDlen ++
      (mulE ++ (CheckCrtKey.modOne (topD sYlen) ++ (loadA aX sDX sXlen ++ (mulE ++ CheckCrtKey.modOne CheckCrtKey.topE)))))))) := by
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
    (hy : Y < 2 ^ (64 * ((yl + 7) / 8))) (he33 : I.E < 2 ^ 33) :
    WP isa (seqs (modChecks sX sXlen sDX sYlen)) s fun t => ∃ g : Bool, KS I m₀ (g && c) t ∧
      (Spec.Rsa.os2ip xb % 2 = 1 → 1 < Spec.Rsa.os2ip xb → I.D < I.N → Spec.Rsa.os2ip xb * Y = I.N →
        g = (decide (Spec.Rsa.os2ip dxb < Spec.Rsa.os2ip xb - 1) &&
          decide (I.D * I.E % (Spec.Rsa.os2ip xb - 1) = 1) &&
          decide (I.E * Spec.Rsa.os2ip dxb % (Spec.Rsa.os2ip xb - 1) = 1))) := by
  obtain ⟨hs, hm, hN, hE, hO⟩ := h
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
  have M₃ : I.av s₃.mem aM = I.av s₂.mem aM := o₃ aM (by decide) (by decide)
  refine wp_seqs_append (by simp [ltA]) (by simp [loadA]) (WP.mono (ckLt_ok h₃ (a := aX) (b := aM) (by decide)
    (by decide) (m₃.trans (m₂.trans (m₁.trans hm)))) fun s₄ ⟨h₄, m₄, o₄⟩ => ?_)
  rw [v₃, M₃] at m₄
  -- `d e mod (X - 1) = 1`.
  refine wp_seqs_append (by simp [loadA]) (by simp [mulE]) (WP.mono (ckLoad_ok h₄ (j := aX) (by decide) (by decide)
    (by decide) h₄.args.d h₄.args.dl h₄.d L.dbl L.dl1 L.dl2) fun s₅ ⟨h₅, m₅, v₅, o₅⟩ => ?_)
  have E₅ : I.av s₅.mem aE = I.E := by
    rw [o₅ aE (by decide) (by decide), o₄ aE (by decide), o₃ aE (by decide) (by decide), o₂ aE (by decide) (by decide),
      o₁ aE (by decide) (by decide), hE]
  refine wp_seqs_append (by simp [mulE]) (by simp [CheckCrtKey.modOne, CheckCrtKey.reduceTop]) (WP.mono (ckMulE_ok h₅ L
    (by rw [v₅]; exact lt_w (by rw [L.dbl]; exact L.dcap))) fun s₆ ⟨h₆, m₆, v₆, o₆⟩ => ?_)
  rw [v₅, e_word E₅ hE64] at v₆
  have O₆ : I.av s₆.mem aOne = 1 := by
    rw [o₆ aOne (by decide) (by decide), o₅ aOne (by decide) (by decide), o₄ aOne (by decide),
      o₃ aOne (by decide) (by decide), o₂ aOne (by decide) (by decide), o₁ aOne (by decide) (by decide), hO]
  refine wp_seqs_append (by simp [CheckCrtKey.modOne, CheckCrtKey.reduceTop]) (by simp [loadA]) (WP.mono (ckModOneTop_ok h₆
    (m₆.trans (m₅.trans m₄)) O₆ (topD_ok hsY (hY _ h₆) (by have := L.cap2; have := L.k2; omega_arith)
      h₆.ws.h256) (by omega_arith)
    (by have := L.cap1; unfold wW wk; omega_arith)) fun s₇ ⟨h₇, ⟨r₁, hr₁, m₇⟩, o₇⟩ => ?_)
  have M₆ : I.av s₆.mem aM = I.av s₂.mem aM := by
    rw [o₆ aM (by decide) (by decide), o₅ aM (by decide) (by decide), o₄ aM (by decide), M₃]
  rw [v₆, M₆] at hr₁
  -- `e dX mod (X - 1) = 1`.
  obtain ⟨-, -, -, c4, c5⟩ := hA s₇ h₇
  refine wp_seqs_append (by simp [loadA]) (by simp [mulE]) (WP.mono (ckLoad_ok h₇ (j := aX) (by decide) hsD hsL c4
    ((hA s₇ h₇).2.1) c5 hdxb hxl1 (Nat.le_of_lt hxl2)) fun s₈ ⟨h₈, m₈, v₈, o₈⟩ => ?_)
  have E₈ : I.av s₈.mem aE = I.E := by
    rw [o₈ aE (by decide) (by decide), o₇ aE (by decide) (by decide) (by decide) (by decide), o₆ aE (by decide)
      (by decide), E₅]
  refine wp_seqs_append (by simp [mulE]) (by simp [CheckCrtKey.modOne, CheckCrtKey.reduceTop]) (WP.mono (ckMulE_ok h₈ L
    (by rw [v₈]; exact lt_w (by rw [hdxb]; exact hxc))) fun s₉ ⟨h₉, m₉, v₉, o₉⟩ => ?_)
  rw [v₈, e_word E₈ hE64] at v₉
  have O₉ : I.av s₉.mem aOne = 1 := by
    rw [o₉ aOne (by decide) (by decide), o₈ aOne (by decide) (by decide),
      o₇ aOne (by decide) (by decide) (by decide) (by decide), O₆]
  refine WP.mono (ckModOneTop_ok h₉ (m₉.trans (m₈.trans m₇)) O₉ (topE_ok _ _ _)
    (by omega_arith) (by unfold wW; omega_arith)) fun t ⟨ht, ⟨r₂, hr₂, mt⟩, ot⟩ => ?_
  have M₉ : I.av s₉.mem aM = I.av s₂.mem aM := by
    rw [o₉ aM (by decide) (by decide), o₈ aM (by decide) (by decide), o₇ aM (by decide) (by decide) (by decide)
      (by decide), M₆]
  rw [v₉, M₉] at hr₂
  -- What the other arrays keep.
  have keep : ∀ i, i = 0 ∨ i = aE ∨ i = aOne → I.av t.mem i = I.av s.mem i := by
    intro i hi
    have h16 : i < 16 := by rcases hi with rfl | rfl | rfl <;> decide
    have d1 : i ≠ aM := by rcases hi with rfl | rfl | rfl <;> decide
    have d2 : i ≠ aX := by rcases hi with rfl | rfl | rfl <;> decide
    have d3 : i ≠ aA := by rcases hi with rfl | rfl | rfl <;> decide
    have d4 : i ≠ aRem := by rcases hi with rfl | rfl | rfl <;> decide
    have d5 : i ≠ aT := by rcases hi with rfl | rfl | rfl <;> decide
    have d6 : i ≠ CheckCrtKey.aQ := by rcases hi with rfl | rfl | rfl <;> decide
    rw [ot i h16 d4 d6 d5, o₉ i h16 d3, o₈ i h16 d2, o₇ i h16 d4 d6 d5, o₆ i h16 d3, o₅ i h16 d2, o₄ i h16,
      o₃ i h16 d2, o₂ i h16 d1, o₁ i h16 d1]
  refine ⟨decide (Spec.Rsa.os2ip dxb < I.av s₂.mem aM) && decide (r₁ = 1) && decide (r₂ = 1), ⟨ht, ?_,
    by rw [keep 0 (.inl rfl), hN], by rw [keep aE (.inr (.inl rfl)), hE], by rw [keep aOne (.inr (.inr rfl)), hO]⟩,
    fun ho h1 hd hpq => ?_⟩
  · rw [mt]
    cases decide (r₂ = 1) <;> cases decide (r₁ = 1) <;> cases decide (Spec.Rsa.os2ip dxb < I.av s₂.mem aM) <;>
      cases c <;> rfl
  · have hM : I.av s₂.mem aM = Spec.Rsa.os2ip xb - 1 := v₂ ho
    have hM0 : 0 < I.av s₂.mem aM := by rw [hM]; omega_arith
    have hdBound : I.D * I.E / 2 ^ (64 * ((yl + 7) / 8 + 1)) < I.av s₂.mem aM := by
      rw [hM, Nat.mul_comm I.D I.E]
      exact (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
        (by rw [Nat.mul_comm (Spec.Rsa.os2ip xb - 1)]; exact Proof.Rsa.fullExp_bound (x := Spec.Rsa.os2ip xb) (L := yl) he33 (by omega_arith) (by rw [hpq]; exact hd) hy)
    rw [hr₁ hdBound, hM]
    by_cases hlt : Spec.Rsa.os2ip dxb < Spec.Rsa.os2ip xb - 1
    · rw [hr₂ (by rw [hM]; exact Nat.lt_of_le_of_lt (mul_div_top_le (k := 1) (by simpa using hE64)) hlt),
        hM, Nat.mul_comm (Spec.Rsa.os2ip dxb) I.E]
    · simp only [hlt, decide_false, Bool.false_and]


end VG.Proof.Rsa.AArch64
