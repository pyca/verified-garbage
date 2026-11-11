module
public import VerifiedGarbage.Impl.Bignum.AArch64.R2Div
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import VerifiedGarbage.Proof.Bignum.AArch64.R2
public import VerifiedGarbage.Proof.Bignum.AArch64.R2dFast

public import VerifiedGarbage.Proof.Bignum.AArch64.R2dStep
import VerifiedGarbage.Proof.Bignum.AArch64.Bytes
import VerifiedGarbage.Proof.Bignum.AArch64.R2dRecip
import VerifiedGarbage.Proof.Bignum.AArch64.R2dQuot
import VerifiedGarbage.Proof.Bignum.AArch64.R2dSub
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import VerifiedGarbage.Proof.Bignum.WordStep
import VerifiedGarbage.Proof.Bignum.WordStepNorm
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# `R² mod m` by long division on AArch64, for any top word of a public `m`

`fastN` (`r2dFastN_ok`) is `fastPub` for an odd `m` whose top word is not
zero but whose top bit may be clear: `q̂` is estimated from the top words of
`x P` and `m P` for `P = 2^z` whose `d' = ⌊m P / 2^(64 (w - 1))⌋ ≥ 2^63`
(`normN_ok`), by the reciprocal of `d'` (`recipN_ok`) and `quotN`
(`r2dQuotN_ok`), which is `q ≤ q̂ ≤ q + 2` for `q = ⌊x 2^64 / m⌋`
(`WordStep.qhat_norm`), and a step is `x 2^64 mod m` for any such `q̂`
(`WordStep.wordStepQ_val`, `r2dStepN_ok`). `x` starts at `2^(64 (w - 1))`
(`topInit_ok`) and takes `w + 1` steps (`r2dStepsN_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.Public VG.Impl.Bignum.AArch64 VG.Impl.Bignum.AArch64.R2Div
open VG.Proof.Bignum VG.Proof.Bignum.WordStep
open VG.Proof.MlKem.AArch64 (Keep count_loop eval_zero eval_nonzero eq_zero_iff)

/-! ## `P` and `d'` -/

theorem pl_tst (x : BitVec 64) : (!(x &&& x).msb) = decide (x.toNat < 2 ^ 63) := by
  rw [BitVec.and_self, BitVec.msb_eq_decide]
  by_cases h : x.toNat < 2 ^ 63
  · rw [decide_eq_false (by omega_using [h]), decide_eq_true h]; rfl
  · rw [decide_eq_true (by omega_using [h]), decide_eq_false h]; rfl

theorem shl3_sub16 {w : Nat} (hw : 2 ≤ w) (hw' : w < 2 ^ 61) :
    BitVec.ofNat 64 w <<< 3 - BitVec.ofNat 64 16 = BitVec.ofNat 64 (8 * (w - 2)) := by
  rw [r2d_ofNat_shl3 hw']
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega_arith

/-- `normN`, `m` (`w ≥ 2` words, at least `2^(64 (w - 1))`) at `x9` and the
temporary at `x6`: `P = 2^z` and `d' = ⌊m P / 2^(64 (w - 1))⌋ ≥ 2^63` in the
temporary's words 1 and 2. -/
theorem normN_ok {s : State} {B : Addr} {Z w eM eT : Nat} (hs : Scr s B Z)
    (h9 : s.gpr .x9 = off B eM) (h12 : s.gpr .x12 = BitVec.ofNat 64 w) (h6 : s.gpr .x6 = off B eT)
    (hw : 2 ≤ w) (hw' : w < 2 ^ 31) (hM : eM + 8 * w ≤ Z) (hT : eT + 24 ≤ Z) (htop : 2 ^ (64 * (w - 1)) ≤ wv s.mem B eM w) :
    WP isa normN s fun t => (∃ z ≤ 63, (word t.mem B (eT + 8)).toNat = 2 ^ z ∧
      (word t.mem B (eT + 16)).toNat = wv s.mem B eM w * 2 ^ z / 2 ^ (64 * (w - 1)) ∧
      2 ^ 63 ≤ wv s.mem B eM w * 2 ^ z / 2 ^ (64 * (w - 1))) ∧
      Outside B (eT + 8) 16 s.mem t.mem ∧ Keep [.x3, .x10, .x13, .x15, .x16, .x17] s t := by
  have hn := hs.nowrap
  generalize hTw : word s.mem B (eM + 8 * (w - 1)) = T
  generalize hLw : word s.mem B (eM + 8 * (w - 2)) = L
  have hN : wv s.mem B eM w = T.toNat * 2 ^ (64 * (w - 2) + 64) + L.toNat * 2 ^ (64 * (w - 2)) + wv s.mem B eM (w - 2) := by
    have e1 : wv s.mem B eM (w - 1 + 1) = wv s.mem B eM (w - 1) + 2 ^ (64 * (w - 1)) *
        (word s.mem B (eM + 8 * (w - 1))).toNat := rfl
    have e2 : wv s.mem B eM (w - 2 + 1) = wv s.mem B eM (w - 2) + 2 ^ (64 * (w - 2)) *
        (word s.mem B (eM + 8 * (w - 2))).toNat := rfl
    rw [show w - 1 + 1 = w by omega, hTw] at e1
    rw [show w - 2 + 1 = w - 1 by omega, hLw] at e2
    rw [e1, e2, show 64 * (w - 1) = 64 * (w - 2) + 64 by omega, Nat.mul_comm (2 ^ (64 * (w - 2) + 64)),
      Nat.mul_comm (2 ^ (64 * (w - 2)))]
    generalize T.toNat * 2 ^ (64 * (w - 2) + 64) = a
    generalize L.toNat * 2 ^ (64 * (w - 2)) = b
    omega_using []
  have hT0 : 0 < T.toNat := by
    rcases Nat.eq_zero_or_pos T.toNat with h | h
    · have hl := wv_lt s.mem B eM (w - 2)
      have hL := Nat.mul_le_mul_right (2 ^ (64 * (w - 2))) (show L.toNat + 1 ≤ 2 ^ 64 from L.isLt)
      rw [Nat.add_mul, Nat.one_mul, ← Nat.pow_add, show 64 + 64 * (w - 2) = 64 * (w - 2) + 64 by omega] at hL
      rw [hN, h, Nat.zero_mul, Nat.zero_add, show 64 * (w - 1) = 64 * (w - 2) + 64 by omega] at htop
      generalize L.toNat * 2 ^ (64 * (w - 2)) = a at htop hL
      generalize 2 ^ (64 * (w - 2) + 64) = b at htop hL
      generalize 2 ^ (64 * (w - 2)) = c at hl hL
      omega_using [htop, hL, hl]
    · exact h
  unfold normN
  refine WP.seq (WP.mono (WP.keep [.x3, .x10, .x13, .x15] (Q := fun t =>
      t.gpr .x15 = T ∧ t.gpr .x3 = L ∧ (t.gpr .x10).toNat = 1 ∧ t.gpr .x13 = BitVec.ofNat 64 63 ∧ t.mem = s.mem)
    (by
      brun [h9, h12, shl3_sub16 hw (show w < 2 ^ 61 by omega), off_add,
        hs.ld (show eM + 8 * (w - 2) + 8 + 8 ≤ Z by omega), hs.ld (show eM + 8 * (w - 2) + 8 ≤ Z by omega)]
      exact ⟨by rw [← hTw, show eM + 8 * (w - 2) + 8 = eM + 8 * (w - 1) by omega], hLw⟩)
    (by decide) (by decide) (by decide +kernel)) fun s₁ ⟨⟨a15, a3, a10, a13, m1⟩, k1⟩ => ?_)
  -- 63 steps.
  let Inv : Nat → State → Prop := fun i t =>
    (∃ j ≤ i, (t.gpr .x10).toNat = 2 ^ j ∧ (t.gpr .x15).toNat = T.toNat * 2 ^ j ∧
      (j = i ∨ 2 ^ 63 ≤ T.toNat * 2 ^ j)) ∧ t.gpr .x3 = L ∧ t.mem = s.mem ∧
      Keep [.x3, .x10, .x13, .x15, .x16, .x17] s t
  refine WP.seq (WP.mono (wp_countdown (body := .block (normStep ++ ([.subImm .x .x13 .x13 1] : List Instr)))
    (cnt := .x13) (N := 63) (by decide) (by decide) Inv (fun i hi t ⟨⟨j, hj, jp, jx, jc⟩, j3, jm, jk⟩ hc => ?_)
    ⟨⟨0, Nat.le_refl _, a10, by rw [a15, Nat.pow_zero, Nat.mul_one], Or.inl rfl⟩, a3, m1, k1.mono (by decide)⟩ a13)
    fun t ⟨⟨j, hj, jp, jx, jc⟩, j3, jm, jk⟩ => ?_)
  · have hst : WP isa (.block (normStep ++ ([.subImm .x .x13 .x13 1] : List Instr))) t fun t' =>
        (t'.gpr .x10 = (if (t.gpr .x15).toNat < 2 ^ 63 then t.gpr .x10 + t.gpr .x10 else t.gpr .x10) ∧
          t'.gpr .x15 = (if (t.gpr .x15).toNat < 2 ^ 63 then t.gpr .x15 + t.gpr .x15 else t.gpr .x15) ∧
          t'.mem = t.mem ∧ t'.gpr .x13 = t.gpr .x13 - BitVec.ofNat 64 1) ∧
          Keep [.x10, .x13, .x15, .x16, .x17] t t' := by
      refine WP.keep _ ?_ (by decide) rfl (by decide +kernel)
      brun [normStep, r2d_exec_tst, r2d_exec_cselc, CondCode.holds, pl_tst, decide_eq_true_eq, RegUpd.nf_write]
    refine WP.mono hst fun t' ⟨⟨u10, u15, um, u13⟩, uk⟩ => ⟨⟨?_, by rw [uk.gpr .x3 (by decide), j3], by rw [um, jm],
      (jk.trans uk).mono (by decide)⟩, u13⟩
    rw [u10, u15]
    exact norm_inv_step hj (by omega) jp jx jc
  -- `P` and `d'` into the temporary.
  have hTP : 2 ^ 63 ≤ T.toNat * 2 ^ j := by
    rcases jc with rfl | h
    · exact Nat.le_mul_of_pos_left _ hT0
    · exact h
  have hj63 : j ≤ 63 := hj
  have hs₂ := hs.congr jk.wr
  have t6 : t.gpr .x6 = off B eT := (jk.gpr .x6 (by decide)).trans h6
  have hLP : L.toNat * 2 ^ j / 2 ^ 64 < 2 ^ j := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 64), Nat.mul_comm (2 ^ j)]
    exact Nat.mul_lt_mul_of_pos_right L.isLt (Nat.two_pow_pos j)
  have hpj : 2 ^ j ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) hj63
  generalize hd' : t.gpr .x15 + BitVec.ofNat 64 (L.toNat * (t.gpr .x10).toNat / 2 ^ 64) = D
  refine WP.mono (WP.keep [.x3, .x15] (Q := fun u => u.mem = (t.mem.writeW (off B (eT + 8)) (t.gpr .x10)).writeW
      (off B (eT + 16)) D) (by
    brun [j3, t6, hd', hs₂.st (show eT + 8 + 8 ≤ Z by omega), hs₂.st (show eT + 16 + 8 ≤ Z by omega)])
    (by decide) (by decide) (by decide +kernel)) fun u ⟨um, uk⟩ => ⟨⟨j, hj63, ?_, ?_⟩, ?_, (jk.trans uk).mono (by decide)⟩
  · rw [um, (writeW_outside _ B _ (show eT + 16 + 8 ≤ 2 ^ 64 by omega)).word (by omega) (by omega), word_writeW_self, jp]
  · have hNv : wv s.mem B eM w * 2 ^ j / 2 ^ (64 * (w - 1)) = T.toNat * 2 ^ j + L.toNat * 2 ^ j / 2 ^ 64 := by
      rw [hN, show 64 * (w - 1) = 64 * (w - 2) + 64 by omega]
      exact top_shift (by omega) (wv_lt _ _ _ _)
    have hD : D.toNat = T.toNat * 2 ^ j + L.toNat * 2 ^ j / 2 ^ 64 := by
      have hlt := shl_add_lt (by omega) (show T.toNat * 2 ^ j < 2 ^ 64 by rw [← jx]; exact (t.gpr .x15).isLt) hLP
      rw [← hd', BitVec.toNat_add, BitVec.toNat_ofNat, jx, jp, Nat.mod_eq_of_lt (by omega_using [hLP, hpj] :
        L.toNat * 2 ^ j / 2 ^ 64 < 2 ^ 64), Nat.mod_eq_of_lt hlt]
    rw [hNv]
    refine ⟨?_, by omega_using [hTP]⟩
    rw [um, word_writeW_self, hD]
  · rw [um, ← jm]
    exact ((writeW_outside _ B _ (show eT + 8 + 8 ≤ 2 ^ 64 by omega)).mono (by omega) (by omega)).trans
      ((writeW_outside _ B _ (show eT + 16 + 8 ≤ 2 ^ 64 by omega)).mono (by omega) (by omega))

/-! ## The reciprocal of `d'` -/

/-- `recipN`: `v = ⌊(2^128 - 1) / d'⌋ - 2^64` for `d' ≥ 2^63` (the word at
`x6 + 16`) into the word at `x6`. -/
theorem recipN_ok {s : State} {B : Addr} {Z eV : Nat} (hs : Scr s B Z) (h6 : s.gpr .x6 = off B eV)
    (h7 : s.gpr .x7 = 0) (hV : eV + 24 ≤ Z) (hd : 2 ^ 63 ≤ (word s.mem B (eV + 16)).toNat) :
    WP isa recipN s fun t =>
      (word t.mem B eV).toNat = (2 ^ 128 - 1) / (word s.mem B (eV + 16)).toNat - 2 ^ 64 ∧
      Outside B eV 8 s.mem t.mem ∧ Keep [.x2, .x3, .x4, .x5, .x10, .x13, .x15, .x16] s t := by
  have hn := hs.nowrap
  generalize hD : word s.mem B (eV + 16) = D at hd
  have hD' := D.isLt
  have hsub : (0 : BitVec 64) - D - BitVec.ofNat 64 1 = BitVec.ofNat 64 (2 ^ 64 - 1 - D.toNat) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, show (0 : BitVec 64).toNat = 0 from rfl]
    omega
  unfold recipN
  refine WP.seq (WP.mono (WP.keep [.x2, .x4, .x5, .x10, .x13] (Q := fun t =>
    t.gpr .x5 = BitVec.ofNat 64 D.toNat ∧ t.gpr .x2 = BitVec.ofNat 64 (2 ^ 64 - 1 - D.toNat) ∧
    t.gpr .x10 = BitVec.ofNat 64 0 ∧ t.gpr .x4 = (BitVec.ofNat 16 1).setWidth 64 ∧
    t.gpr .x13 = BitVec.ofNat 64 64 ∧ t.mem = s.mem)
    (by brun [h6, h7, off_add, hs.ld (show eV + 16 + 8 ≤ Z by omega), hD, hsub]
        <;> first | rfl | rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])
    (by decide) (by decide) (by decide +kernel))
    fun s₁ ⟨⟨h5, h2, h10, h4, h13, hm₁⟩, k₁⟩ => ?_)
  have hr0 : 2 ^ 64 - 1 - D.toNat < D.toNat := by omega
  have h0 : R2dRecInv s₁ D.toNat (2 ^ 64 - 1 - D.toNat) 0 s₁ :=
    ⟨Keep.refl _ _, rfl, 0, 2 ^ 64 - 1 - D.toNat, h2, h10, by simp, hr0⟩
  refine WP.seq (WP.mono (wp_countdown (N := 64) (by decide) (by decide) (R2dRecInv s₁ D.toNat (2 ^ 64 - 1 - D.toNat))
    (fun k hk t hI _ => divStep_ok hD' hr0 h4 ((k₁.gpr .x7 (by decide)).trans h7) h5 hk hI) h0 h13)
    fun t hI => ?_)
  obtain ⟨q, r, _, h10t, hP, hr⟩ := hI.val
  have t6 : t.gpr .x6 = off B eV := (hI.keep.gpr .x6 (by decide)).trans ((k₁.gpr .x6 (by decide)).trans h6)
  have hst : InRegions t.wr (off B eV) 8 := by
    rw [hI.keep.wr, k₁.wr]; exact hs.st (by omega)
  refine WP.mono (WP.keep [] (Q := fun t' => t'.mem = t.mem.writeW (off B eV) (t.gpr .x10))
    (by brun [t6, hst]) (by decide) (by decide) (by decide +kernel)) fun t' ⟨hm', k'⟩ => ?_
  have hq : q = (2 ^ 128 - 1) / D.toNat - 2 ^ 64 := by
    rw [← WordStep.recip_eq hD' (by omega), hP, Nat.mul_comm q, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hr,
      Nat.add_zero]
  have hqB : q < 2 ^ 64 := by
    rw [hq]
    have : (2 ^ 128 - 1) / D.toNat < 2 ^ 65 := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      have := Nat.mul_le_mul_left (2 ^ 65) hd
      omega
    omega
  refine ⟨by rw [hm', word_writeW_self, h10t, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hqB, hq], ?_,
    ((k₁.trans hI.keep).trans k').mono (by decide)⟩
  rw [hm', hI.mem, hm₁]
  exact writeW_outside _ _ _ (by omega)

/-! ## The estimate of the quotient -/

theorem shl3_sub24 {w : Nat} (hw : 3 ≤ w) (hw' : w < 2 ^ 61) :
    BitVec.ofNat 64 w <<< 3 - BitVec.ofNat 64 24 = BitVec.ofNat 64 (8 * (w - 3)) := by
  rw [r2d_ofNat_shl3 hw']
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega_arith

/-- `quotN`: `q̂ = min(⌊u / d'⌋, 2^64 - 1)` into `x1`, for `x` at `x11` of
`w ≥ 3` words, `u = ⌊x P / 2^(64 (w - 2))⌋` its top two words times `P`, and
`P = 2^z`, `d' ≥ 2^63` and `v` for `d'` in the temporary (at `x6`), with
`⌊x P / 2^(64 (w - 1))⌋ ≤ d'`. -/
theorem r2dQuotN_ok {t : State} {B : Addr} {Z w eX eT z : Nat} (hs : Scr t B Z)
    (h11 : t.gpr .x11 = off B eX) (h12 : t.gpr .x12 = BitVec.ofNat 64 w) (h6 : t.gpr .x6 = off B eT)
    (h7 : t.gpr .x7 = 0) (hw : 3 ≤ w) (hw' : w < 2 ^ 31) (hX : eX + 8 * w ≤ Z) (hT : eT + 24 ≤ Z)
    (hP : (word t.mem B (eT + 8)).toNat = 2 ^ z) (hz : z ≤ 63) (hd : 2 ^ 63 ≤ (word t.mem B (eT + 16)).toNat)
    (hv : (word t.mem B eT).toNat = (2 ^ 128 - 1) / (word t.mem B (eT + 16)).toNat - 2 ^ 64)
    (hXd : wv t.mem B eX w * 2 ^ z / 2 ^ (64 * (w - 1)) ≤ (word t.mem B (eT + 16)).toNat) :
    WP isa (.block quotN) t fun t' =>
      t'.gpr .x1 = BitVec.ofNat 64 (min (wv t.mem B eX w * 2 ^ z / 2 ^ (64 * (w - 2)) /
        (word t.mem B (eT + 16)).toNat) (2 ^ 64 - 1)) ∧
      t'.mem = t.mem ∧ Keep [.x1, .x2, .x3, .x4, .x5, .x13, .x14, .x15, .x16, .x17] t t' := by
  have hn := hs.nowrap
  generalize hDw : word t.mem B (eT + 16) = D at hd hv hXd ⊢
  generalize hPw : word t.mem B (eT + 8) = P at hP
  generalize hVw : word t.mem B eT = Vw at hv
  generalize hx2 : word t.mem B (eX + 8 * (w - 1)) = x2
  generalize hx1 : word t.mem B (eX + 8 * (w - 2)) = x1
  generalize hx0 : word t.mem B (eX + 8 * (w - 3)) = x0
  have e2 : eX + 8 * (w - 3) + 16 = eX + 8 * (w - 1) := by omega
  have e1 : eX + 8 * (w - 3) + 8 = eX + 8 * (w - 2) := by omega
  refine WP.mono (WP.keep [.x1, .x2, .x3, .x4, .x5, .x13, .x14, .x15, .x16, .x17] (Q := fun t' =>
      t'.gpr .x1 = (if decide ((D - (x2 * P + BitVec.ofNat 64 (x1.toNat * P.toNat / 2 ^ 64)) &&&
          D - (x2 * P + BitVec.ofNat 64 (x1.toNat * P.toNat / 2 ^ 64))) = 0) then
          (BitVec.ofNat 16 0).setWidth 64 - BitVec.ofNat 64 1
        else mgq Vw (x2 * P + BitVec.ofNat 64 (x1.toNat * P.toNat / 2 ^ 64))
          (x1 * P + BitVec.ofNat 64 (x0.toNat * P.toNat / 2 ^ 64)) D) ∧ t'.mem = t.mem) (by
    brun [h11, h12, h6, h7, r2d_exec_tst, r2d_exec_cselc, CondCode.holds, shl3_sub24 hw (show w < 2 ^ 61 by omega),
      off_add, e2, e1, hs.ld (show eX + 8 * (w - 1) + 8 ≤ Z by omega), hs.ld (show eX + 8 * (w - 2) + 8 ≤ Z by omega),
      hs.ld (show eX + 8 * (w - 3) + 8 ≤ Z by omega), hs.ld (show eT + 8 + 8 ≤ Z by omega),
      hs.ld (show eT + 16 + 8 ≤ Z by omega), hs.ld (show eT + 8 ≤ Z by omega), hDw, hPw, hVw, hx2, hx1, hx0,
      quotN, quotHeadN, quotMG]
    rfl) (by decide) (by decide) (by decide +kernel)) fun t' ⟨⟨h1, hm⟩, k⟩ => ⟨?_, hm, k⟩
  rw [h1]
  generalize hK : 64 * (w - 3) = K
  have hk1 : 64 * (w - 1) = K + 64 + 64 := by omega
  have hk2 : 64 * (w - 2) = K + 64 := by omega
  rw [hk1] at hXd
  rw [hk2]
  have hlow := wv_lt t.mem B eX (w - 3)
  rw [hK] at hlow
  have hXe : wv t.mem B eX w = x2.toNat * 2 ^ (K + 64 + 64) + x1.toNat * 2 ^ (K + 64) + x0.toNat * 2 ^ K +
      wv t.mem B eX (w - 3) := by
    have f1 : wv t.mem B eX (w - 1 + 1) = wv t.mem B eX (w - 1) + 2 ^ (64 * (w - 1)) *
        (word t.mem B (eX + 8 * (w - 1))).toNat := rfl
    have f2 : wv t.mem B eX (w - 2 + 1) = wv t.mem B eX (w - 2) + 2 ^ (64 * (w - 2)) *
        (word t.mem B (eX + 8 * (w - 2))).toNat := rfl
    have f3 : wv t.mem B eX (w - 3 + 1) = wv t.mem B eX (w - 3) + 2 ^ (64 * (w - 3)) *
        (word t.mem B (eX + 8 * (w - 3))).toNat := rfl
    rw [show w - 1 + 1 = w by omega, hx2, hk1] at f1
    rw [show w - 2 + 1 = w - 1 by omega, hx1, hk2] at f2
    rw [show w - 3 + 1 = w - 2 by omega, hx0, hK] at f3
    rw [f1, f2, f3, Nat.mul_comm x2.toNat, Nat.mul_comm x1.toNat, Nat.mul_comm x0.toNat]
    generalize 2 ^ (K + 64 + 64) * x2.toNat = a
    generalize 2 ^ (K + 64) * x1.toNat = b
    generalize 2 ^ K * x0.toNat = c
    omega_using []
  generalize hX : wv t.mem B eX w = X at hXd hXe ⊢
  -- The top words of `x P`.
  have hu2 : X * 2 ^ z / 2 ^ (K + 64 + 64) = x2.toNat * 2 ^ z + x1.toNat * 2 ^ z / 2 ^ 64 := by
    rw [hXe, Nat.add_assoc _ (x0.toNat * 2 ^ K)]
    refine top_shift (by omega) ?_
    have := Nat.mul_le_mul_right (2 ^ K) (show x0.toNat + 1 ≤ 2 ^ 64 from x0.isLt)
    rw [Nat.add_mul, Nat.one_mul, ← Nat.pow_add, Nat.add_comm 64 K] at this
    omega_using [this, hlow]
  have hU : X * 2 ^ z / 2 ^ (K + 64) = x2.toNat * 2 ^ z * 2 ^ 64 + (x1.toNat * 2 ^ z + x0.toNat * 2 ^ z / 2 ^ 64) := by
    have : X = (x2.toNat * 2 ^ 64 + x1.toNat) * 2 ^ (K + 64) + x0.toNat * 2 ^ K + wv t.mem B eX (w - 3) := by
      rw [hXe, Nat.add_mul, Nat.mul_assoc, ← Nat.pow_add, Nat.add_comm 64 (K + 64)]
    rw [this, top_shift (by omega) hlow, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm (2 ^ 64), ← Nat.mul_assoc,
      Nat.add_assoc]
  generalize hUd : X * 2 ^ z / 2 ^ (K + 64) = U at hU ⊢
  have hUu : U / 2 ^ 64 = X * 2 ^ z / 2 ^ (K + 64 + 64) := by
    rw [← hUd, Nat.div_div_eq_div_mul, ← Nat.pow_add]
  have hf0 : x0.toNat * 2 ^ z / 2 ^ 64 < 2 ^ z := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 64), Nat.mul_comm (2 ^ z)]
    exact Nat.mul_lt_mul_of_pos_right x0.isLt (Nat.two_pow_pos z)
  have hpz : 2 ^ z ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) hz
  have hf1 : x1.toNat * 2 ^ z / 2 ^ 64 < 2 ^ 64 := by
    have : x1.toNat * 2 ^ z / 2 ^ 64 < 2 ^ z := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 64), Nat.mul_comm (2 ^ z)]
      exact Nat.mul_lt_mul_of_pos_right x1.isLt (Nat.two_pow_pos z)
    omega_using [this, hpz]
  have hD' := D.isLt
  have r2v : (x2 * P + BitVec.ofNat 64 (x1.toNat * P.toNat / 2 ^ 64)).toNat = U / 2 ^ 64 := by
    rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, hP, Nat.mod_eq_of_lt hf1, Nat.mod_add_mod, hUu, hu2]
    exact Nat.mod_eq_of_lt (by omega_using [hu2, hXd, hD'])
  have r1v : (x1 * P + BitVec.ofNat 64 (x0.toNat * P.toNat / 2 ^ 64)).toNat = U % 2 ^ 64 := by
    rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, hP,
      Nat.mod_eq_of_lt (by omega_using [hf0, hpz] : x0.toNat * 2 ^ z / 2 ^ 64 < 2 ^ 64), Nat.mod_add_mod, hU,
      Nat.add_comm (x2.toNat * 2 ^ z * 2 ^ 64), Nat.add_mul_mod_self_right]
  have hu : U / 2 ^ 64 ≤ D.toNat := by rw [hUu]; exact hXd
  have hUe : U = (x2 * P + BitVec.ofNat 64 (x1.toNat * P.toNat / 2 ^ 64)).toNat * 2 ^ 64 +
      (x1 * P + BitVec.ofNat 64 (x0.toNat * P.toNat / 2 ^ 64)).toNat := by
    rw [r2v, r1v, Nat.div_add_mod']
  rw [← r2v] at hu
  rw [hUe]
  generalize x2 * P + BitVec.ofNat 64 (x1.toNat * P.toNat / 2 ^ 64) = U2 at hu ⊢
  generalize x1 * P + BitVec.ofNat 64 (x0.toNat * P.toNat / 2 ^ 64) = U1
  have hd0 : 0 < D.toNat := by omega_arith
  by_cases he : U2 = D
  · subst he
    simp only [BitVec.sub_self, BitVec.and_self]
    rw [Nat.min_eq_right (by
        rw [Nat.le_div_iff_mul_le hd0]
        exact Nat.le_trans (Nat.mul_le_mul_right _ (Nat.sub_le _ _))
          (by rw [Nat.mul_comm]; exact Nat.le_add_right _ _))]
    rfl
  · have hlt : U2.toNat < D.toNat := by
      rcases Nat.lt_or_eq_of_le hu with h | h
      · exact h
      · exact absurd (BitVec.eq_of_toNat_eq h) he
    have hne : D - U2 ≠ 0 := fun h => by
      have e := congrArg BitVec.toNat h
      rw [BitVec.toNat_sub] at e
      have := U2.isLt
      rw [show (0 : BitVec 64).toNat = 0 from rfl] at e
      omega_arith
    simp only [BitVec.and_self, hne, decide_false, Bool.false_eq_true, ↓reduceIte]
    have hq := mgq_val (v := Vw.toNat) hD' hd hlt U1.isLt hv
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at hq
    have hlt' : (U2.toNat * 2 ^ 64 + U1.toNat) / D.toNat < 2 ^ 64 := by
      rw [Nat.div_lt_iff_lt_mul hd0]
      have := Nat.mul_le_mul_right (2 ^ 64) (show U2.toNat + 1 ≤ D.toNat by omega_arith)
      rw [Nat.add_mul, Nat.one_mul] at this
      have := U1.isLt
      rw [Nat.mul_comm (2 ^ 64)]; omega_arith
    rw [Nat.min_eq_left (by omega_arith), ← hq, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-! ## A step -/

/-- `bases` and `quotN`: the registers, and `q̂` in `x1`. -/
theorem r2dHeadN_ok {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good t B Z w minv)
    (hZ : slot w 8 ≤ Z) (hw : 3 ≤ w) (hw' : w < 2 ^ 31) {z : Nat}
    (hP : (word t.mem B (slot w aTmp + 8)).toNat = 2 ^ z) (hz : z ≤ 63)
    (hd : 2 ^ 63 ≤ (word t.mem B (slot w aTmp + 16)).toNat)
    (hv : (word t.mem B (slot w aTmp)).toNat = (2 ^ 128 - 1) / (word t.mem B (slot w aTmp + 16)).toNat - 2 ^ 64)
    (hXd : wv t.mem B (slot w aR2) w * 2 ^ z / 2 ^ (64 * (w - 1)) ≤ (word t.mem B (slot w aTmp + 16)).toNat) :
    WP isa (.block (R2Div.bases ++ quotN)) t fun t' => StepRegs t' B w ∧
      t'.gpr .x1 = BitVec.ofNat 64 (min (wv t.mem B (slot w aR2) w * 2 ^ z / 2 ^ (64 * (w - 2)) /
        (word t.mem B (slot w aTmp + 16)).toNat) (2 ^ 64 - 1)) ∧
      t'.mem = t.mem ∧ Keep mmRegs t t' := by
  have hs := hg.scr
  have hn := hs.nowrap
  have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off B (8 * i)) 8 := fun i hi =>
    hs.ld (by have := hdr_lt_slot w 8 hi; have := slot_le (w := w) (show 7 < 8 by decide); omega_arith)
  have sl : ∀ j < 8, slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_le hj) hZ
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x6, .x7, .x8, .x9, .x11, .x12] (Q := fun t' => StepRegs t' B w ∧ t'.mem = t.mem)
    (by
      refine WP.mono (Q := fun (t' : State) => (t'.gpr .x8 = off B (slot w aAcc) ∧ t'.gpr .x9 = off B (slot w aN) ∧
        t'.gpr .x11 = off B (slot w aR2) ∧ t'.gpr .x6 = off B (slot w aTmp) ∧ t'.gpr .x12 = BitVec.ofNat 64 w ∧
        t'.gpr .x7 = 0) ∧ t'.mem = t.mem) ?_ fun t' ⟨⟨a, b, c, d, e, f⟩, g⟩ => ⟨⟨a, b, c, d, e, f⟩, g⟩
      brun [R2Div.bases, hg.x0, hdr_enc (show sArr aAcc < 32 by decide), hdr_enc (show sArr aN < 32 by decide),
        hdr_enc (show sArr aR2 < 32 by decide), hdr_enc (show sArr aTmp < 32 by decide),
        hdr_enc (show sW < 32 by decide), hl (sArr aAcc) (by decide), hl (sArr aN) (by decide),
        hl (sArr aR2) (by decide), hl (sArr aTmp) (by decide), hl sW (by decide),
        hg.hdr.harr aAcc (by decide), hg.hdr.harr aN (by decide), hg.hdr.harr aR2 (by decide),
        hg.hdr.harr aTmp (by decide), hg.hdr.hw])
    (by decide) (by decide) (by decide +kernel)) fun t₁ ⟨⟨hr, hm₁⟩, k₁⟩ => ?_
  have hs₁ := hs.congr k₁.wr
  rw [← hm₁] at hP hd hv hXd
  refine WP.mono (r2dQuotN_ok hs₁ hr.x11 hr.x12 hr.x6 hr.x7 hw hw' (by have := sl aR2 (by decide); omega_arith)
    (by have := sl aTmp (by decide); omega_arith) hP hz hd hv hXd)
    fun t' ⟨h1, hm, k⟩ => ⟨hr.keep k, by rw [h1, hm₁], by rw [hm, hm₁], (k₁.trans k).mono (by decide)⟩

/-- The estimate `q̂` of a step's quotient from the top words of `x P`, `P = 2^z`,
by `d' = D`. -/
def r2dQN (m : Mem) (B : Addr) (w z D : Nat) : Nat :=
  min (wv m B (slot w aR2) w * 2 ^ z / 2 ^ (64 * (w - 2)) / D) (2 ^ 64 - 1)

/-- A step's first pieces, by `quotN`: `t = x 2^64 - q̂ m` in the accumulator's
`w + 1` words, with a borrow `b` out of them. -/
theorem r2dStepPreN_ok {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {M D z : Nat} (hg : Good t B Z w minv)
    (hZ : slot w 8 ≤ Z) (hw : 3 ≤ w) (hw' : w < 2 ^ 31) (hM : wv t.mem B (slot w aN) w = M)
    (hP : (word t.mem B (slot w aTmp + 8)).toNat = 2 ^ z) (hz : z ≤ 63)
    (hD : (word t.mem B (slot w aTmp + 16)).toNat = D) (hd : 2 ^ 63 ≤ D)
    (hv : (word t.mem B (slot w aTmp)).toNat = (2 ^ 128 - 1) / D - 2 ^ 64)
    (hXd : wv t.mem B (slot w aR2) w * 2 ^ z / 2 ^ (64 * (w - 1)) ≤ D) :
    WP isa (seqs [.block (R2Div.bases ++ quotN), zeroAcc, mulAddRow, subPass]) t fun t₄ =>
      Good t₄ B Z w minv ∧ StepRegs t₄ B w ∧ wv t₄.mem B (slot w aN) w = M ∧
      (∃ b : Bool, wv t₄.mem B (slot w aAcc) (w + 1) + r2dQN t.mem B w z D * M =
        2 ^ 64 * wv t.mem B (slot w aR2) w + 2 ^ (64 * (w + 1)) * b.toNat) ∧
      Arrays B w [aAcc, aR2] t.mem t₄.mem ∧ Keep mmRegs t t₄ := by
  have hs := hg.scr
  have hn := hs.nowrap
  have sl : ∀ j < 8, slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_le hj) hZ
  have lA := sl aAcc (by decide)
  have lM := sl aN (by decide)
  have lX := sl aR2 (by decide)
  have sAM := slot_sep (w := w) (show aAcc ≠ aN by decide)
  have sAX := slot_sep (w := w) (show aAcc ≠ aR2 by decide)
  simp only [seqs]
  refine WP.seq (WP.mono (r2dHeadN_ok hg hZ hw hw' hP hz (by rw [hD]; exact hd) (by rw [hv, hD]) (by rw [hD]; exact hXd))
    fun t₁ ⟨r₁, h1, hm₁, k₁⟩ => ?_)
  rw [hD] at h1
  have hq : r2dQN t.mem B w z D = min (wv t.mem B (slot w aR2) w * 2 ^ z / 2 ^ (64 * (w - 2)) / D) (2 ^ 64 - 1) := rfl
  rw [← hq] at h1
  generalize r2dQN t.mem B w z D = q at h1 hq ⊢
  have hqB : q < 2 ^ 64 := by rw [hq]; exact Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by decide)
  have hs₁ := hs.congr k₁.wr
  generalize hXv : wv t.mem B (slot w aR2) w = X
  have hMB : M < 2 ^ (64 * w) := hM ▸ wv_lt _ _ _ _
  -- `[acc] := 0`.
  refine WP.seq (WP.mono (zeroAcc_ok hs₁ r₁.x8 r₁.x12 r₁.x7 hw' lA) fun t₂ ⟨hz₂, o₂, k₂⟩ => ?_)
  have r₂ := r₁.keep k₂
  have hs₂ := hs₁.congr k₂.wr
  have M₂ : wv t₂.mem B (slot w aN) w = M := by
    rw [o₂.wv (by omega_arith) (by omega_arith), hm₁, hM]
  have X₂ : wv t₂.mem B (slot w aR2) w = X := by
    rw [o₂.wv (by omega_arith) (by omega_arith), hm₁, hXv]
  -- `[acc] := q̂ m`.
  have hqM : q * M < 2 ^ (64 * (w + 1)) := by
    rw [pow64_succ, Nat.mul_comm (2 ^ (64 * w))]
    exact Nat.mul_lt_mul_of_lt_of_le hqB (Nat.le_of_lt hMB) (by omega_arith)
  refine WP.seq (WP.mono (mulAddRow_ok hs₂ r₂.x8 r₂.x9 r₂.x12 r₂.x7 (by omega_arith) hw' lA (by omega_arith) (by omega_arith)
    (by rw [hz₂, M₂, (k₂.gpr .x1 (by decide)).trans h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hqB, Nat.zero_add]
        exact Nat.lt_of_lt_of_le hqM (Nat.pow_le_pow_right (by decide) (by omega_arith))))
    fun t₃ ⟨hv₃, o₃, k₃⟩ => ?_)
  rw [hz₂, M₂, (k₂.gpr .x1 (by decide)).trans h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hqB, Nat.zero_add]
    at hv₃
  have r₃ := r₂.keep k₃
  have hs₃ := hs₂.congr k₃.wr
  have P₃ : wv t₃.mem B (slot w aAcc) (w + 1) = q * M := by
    rw [wv_low_top t₃.mem B (slot w aAcc) (w + 1) (by rw [hv₃]; exact hqM), hv₃]
  have X₃ : wv t₃.mem B (slot w aR2) w = X := by rw [o₃.wv (by omega_arith) (by omega_arith), X₂]
  have M₃ : wv t₃.mem B (slot w aN) w = M := by rw [o₃.wv (by omega_arith) (by omega_arith), M₂]
  -- `t := x 2^64 - q̂ m`.
  refine WP.mono (subPass_ok hs₃ r₃.x8 r₃.x11 r₃.x12 r₃.x7 (by omega_arith) hw' (by omega_arith) (by omega_arith)
    (by omega_arith)) fun t₄ ⟨b, hv₄, o₄, k₄⟩ => ?_
  rw [P₃, X₃] at hv₄
  have r₄ := r₃.keep k₄
  have hs₄ := hs₃.congr k₄.wr
  have kk : Keep mmRegs t t₄ := (((k₁.trans k₂).trans k₃).trans k₄).mono (by decide)
  have ha : Arrays B w [aAcc, aR2] t.mem t₄.mem := by
    have mA : aAcc ∈ [aAcc, aR2] := by decide
    rw [← hm₁]
    exact ((Arrays.of_outside mA o₂ (Nat.le_refl _) (Nat.le_refl _)).trans
      (Arrays.of_outside mA o₃ (Nat.le_refl _) (Nat.le_refl _))).trans
      (Arrays.of_outside mA o₄ (Nat.le_refl _) (by omega_arith))
  exact ⟨⟨hs₄, (kk.gpr .x0 (by decide)).trans hg.x0, ha.hdr hg.hdr⟩, r₄,
    by rw [o₄.wv (by omega_arith) (by omega_arith), M₃], ⟨b, by omega_arith⟩, ha, kk⟩

/-- `stepN`: `x := x 2^64 mod m` for `x < m`, any odd `m` of `w ≥ 3` words,
`P = 2^z`, `d'` and `v` in the temporary. -/
theorem r2dStepN_ok {t : State} {B : Addr} {Z w : Nat}
    {minv : BitVec 64} {M z : Nat} (hg : Good t B Z w minv)
    (hZ : slot w 8 ≤ Z) (hw : 3 ≤ w) (hw' : w < 2 ^ 31) (hM : wv t.mem B (slot w aN) w = M)
    (hP : (word t.mem B (slot w aTmp + 8)).toNat = 2 ^ z) (hz : z ≤ 63)
    (hD : (word t.mem B (slot w aTmp + 16)).toNat = M * 2 ^ z / 2 ^ (64 * (w - 1)))
    (hd : 2 ^ 63 ≤ M * 2 ^ z / 2 ^ (64 * (w - 1)))
    (hv : (word t.mem B (slot w aTmp)).toNat = (2 ^ 128 - 1) / (M * 2 ^ z / 2 ^ (64 * (w - 1))) - 2 ^ 64)
    (hX : wv t.mem B (slot w aR2) w < M) :
    WP isa stepN t fun t' =>
      Good t' B Z w minv ∧
      wv t'.mem B (slot w aR2) w = wv t.mem B (slot w aR2) w * 2 ^ 64 % M ∧
      Arrays B w [aAcc, aR2] t.mem t'.mem ∧ Keep mmRegs t t' := by
  have hn := hg.scr.nowrap
  have sl : ∀ j < 8, slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_le hj) hZ
  have lA := sl aAcc (by decide)
  have lM := sl aN (by decide)
  have lX := sl aR2 (by decide)
  have sAM := slot_sep (w := w) (show aAcc ≠ aN by decide)
  have sAX := slot_sep (w := w) (show aAcc ≠ aR2 by decide)
  have hMB : M < 2 ^ (64 * w) := hM ▸ wv_lt _ _ _ _
  have hXd : wv t.mem B (slot w aR2) w * 2 ^ z / 2 ^ (64 * (w - 1)) ≤ M * 2 ^ z / 2 ^ (64 * (w - 1)) :=
    Nat.div_le_div_right (Nat.mul_le_mul_right _ (Nat.le_of_lt hX))
  show WP isa (seqs [.block (R2Div.bases ++ quotN), zeroAcc, mulAddRow, subPass, addBackPub, addBackPub, copyBack]) t _
  refine wp_seqs_append (a := [.block (R2Div.bases ++ quotN), zeroAcc, mulAddRow, subPass])
    (b := [addBackPub, addBackPub, copyBack]) (by simp) (by simp)
    (WP.mono (r2dStepPreN_ok hg hZ hw hw' hM hP hz hD hd hv hXd) fun t₄ ⟨g₄, r₄, M₄, ⟨b, hv₄⟩, a₄, k₄⟩ => ?_)
  have hs₄ := g₄.scr
  have hq : r2dQN t.mem B w z (M * 2 ^ z / 2 ^ (64 * (w - 1))) =
    min (wv t.mem B (slot w aR2) w * 2 ^ z / 2 ^ (64 * (w - 2)) / (M * 2 ^ z / 2 ^ (64 * (w - 1)))) (2 ^ 64 - 1) := rfl
  generalize r2dQN t.mem B w z (M * 2 ^ z / 2 ^ (64 * (w - 1))) = q at hv₄ hq
  generalize hXv : wv t.mem B (slot w aR2) w = X at hX hv₄ hq ⊢
  simp only [seqs]
  -- `m` added back while `t` is negative.
  refine WP.seq (WP.mono (addBackPub_spec hs₄ r₄.x8 r₄.x9 r₄.x12 r₄.x7 (by omega_arith) hw' (by omega_arith) (by omega_arith)
    (by omega_arith)) fun t₅ ⟨c1, hv₅, o₅, k₅⟩ => ?_)
  rw [M₄] at hv₅
  have r₅ := r₄.keep k₅
  have hs₅ := hs₄.congr k₅.wr
  have M₅ : wv t₅.mem B (slot w aN) w = M := by rw [o₅.wv (by omega_arith) (by omega_arith), M₄]
  refine WP.seq (WP.mono (addBackPub_spec hs₅ r₅.x8 r₅.x9 r₅.x12 r₅.x7 (by omega_arith) hw' (by omega_arith) (by omega_arith)
    (by omega_arith)) fun t₆ ⟨c2, hv₆, o₆, k₆⟩ => ?_)
  rw [M₅] at hv₆
  have r₆ := r₅.keep k₆
  have hs₆ := hs₅.congr k₆.wr
  -- The value.
  have hM0 : 0 < M := Nat.lt_of_le_of_lt (Nat.zero_le _) hX
  have hW : 4 * M < 2 ^ (64 * (w + 1)) / 2 := by
    rw [show 2 ^ (64 * (w + 1)) / 2 = 2 ^ (64 * w) * 2 ^ 63 by
      rw [Nat.mul_succ, Nat.pow_add, show (2 : Nat) ^ 64 = 2 ^ 63 * 2 from rfl, ← Nat.mul_assoc,
        Nat.mul_div_cancel _ (by decide)]]
    have := Nat.mul_le_mul_left (2 ^ (64 * w)) (show 8 ≤ 2 ^ 63 by decide)
    omega_arith
  obtain ⟨hge, hle⟩ := qhat_norm (X := X) (M := M) (P := 2 ^ z) (K := 64 * (w - 2)) (Nat.two_pow_pos z) hX
    (by rw [show 64 * (w - 2) + 64 = 64 * (w - 1) by omega_arith]; exact hd)
  rw [show 64 * (w - 2) + 64 = 64 * (w - 1) by omega_arith, ← hq] at hge hle
  have hT3 : wv t₆.mem B (slot w aAcc) (w + 1) = X * 2 ^ 64 % M :=
    wordStepQ_val hM0 hW hge hle (wv_lt _ _ _ _) (Bool.toNat_lt b) (by rw [Nat.mul_comm X]; exact hv₄)
      (wv_lt _ _ _ _) (Bool.toNat_lt c1) hv₅ (wv_lt _ _ _ _) (Bool.toNat_lt c2) hv₆
  -- `x := t`.
  unfold copyBack
  refine WP.seq (WP.mono (WP.keep [.x16, .x17] (Q := fun t₇ => t₇.gpr .x16 = off B (slot w aAcc) ∧
    t₇.gpr .x17 = off B (slot w aR2) ∧ t₇.mem = t₆.mem) (by brun [r₆.x8, r₆.x11]) (by decide) (by decide)
    (by decide +kernel)) fun t₇ ⟨⟨h16, h17, hm₇⟩, k₇⟩ => ?_)
  have r₇ := r₆.keep k₇
  have hs₇ := hs₆.congr k₇.wr
  refine WP.mono (copyWords_ok h16 h17 r₇.x12 (by omega_arith) hw' (by omega_arith)
    (fun j hj => hs₇.ld (by omega_arith)) (fun j hj => hs₇.st (by omega_arith))
    (fun j hj i hi => by rw [ofs_off B (by omega_arith)]; omega_arith)) fun t' ⟨hc, _, o', _, _, k'⟩ => ?_
  have hMod : X * 2 ^ 64 % M < 2 ^ (64 * w) := Nat.lt_trans (Nat.mod_lt _ (by omega_arith)) hMB
  have kk : Keep mmRegs t t' := ((((k₄.trans k₅).trans k₆).trans k₇).trans k').mono (by decide)
  have ha : Arrays B w [aAcc, aR2] t.mem t'.mem := by
    have mA : aAcc ∈ [aAcc, aR2] := by decide
    have mX : aR2 ∈ [aAcc, aR2] := by decide
    refine ((a₄.trans (Arrays.of_outside mA o₅ (Nat.le_refl _) (by omega_arith))).trans
      (Arrays.of_outside mA o₆ (Nat.le_refl _) (by omega_arith))).trans ?_
    rw [← hm₇]
    exact Arrays.of_outside mX o' (Nat.le_refl _) (by omega_arith)
  refine ⟨⟨hs₇.congr k'.wr, (kk.gpr .x0 (by decide)).trans hg.x0, ha.hdr hg.hdr⟩, ?_, ha, kk⟩
  rw [hc, hm₇, wv_low_top t₆.mem B (slot w aAcc) w (by rw [hT3]; exact hMod), hT3]

/-! ## The steps -/

/-- After `j` of `steps`' `c` steps from `s`, which started at `x = X₀`. -/
structure R2dStepsInvN (s : State) (B : Addr) (Z w : Nat) (minv : BitVec 64) (M z X0 c j : Nat) (t : State) :
    Prop where
  g : Good t B Z w minv
  cnt : word t.mem B (8 * sCnt) = BitVec.ofNat 64 (c - j)
  x : wv t.mem B (slot w aR2) w = X0 * 2 ^ (64 * j) % M
  n : wv t.mem B (slot w aN) w = M
  p : (word t.mem B (slot w aTmp + 8)).toNat = 2 ^ z
  d : (word t.mem B (slot w aTmp + 16)).toNat = M * 2 ^ z / 2 ^ (64 * (w - 1))
  v : (word t.mem B (slot w aTmp)).toNat = (2 ^ 128 - 1) / (M * 2 ^ z / 2 ^ (64 * (w - 1))) - 2 ^ 64
  frm : Frm B (r2Ranges w) s.mem t.mem
  keep : Keep mmRegs s t

theorem stepsIterN_ok {s t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {M z X0 c j : Nat}
    (hZ : slot w 8 ≤ Z) (hw : 3 ≤ w) (hw' : w < 2 ^ 31) (hz : z ≤ 63) (hd : 2 ^ 63 ≤ M * 2 ^ z / 2 ^ (64 * (w - 1)))
    (hM0 : 0 < M) (hc' : c < 2 ^ 31)
    (hj : j < c) (hI : R2dStepsInvN s B Z w minv M z X0 c j t) :
    WP isa (.seq stepN (.block (dblCount sCnt))) t fun t' =>
      R2dStepsInvN s B Z w minv M z X0 c (j + 1) t' ∧ ((t'.gpr .x13).toNat ≠ 0 ↔ j + 1 ≠ c) := by
  have hn := hI.g.scr.nowrap
  have sl8 : ∀ j < 8, slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_le hj) hZ
  have hhs : ∀ j, 8 * sCnt + 8 ≤ slot w j := fun j => hdr_lt_slot w j (by decide)
  have sNA := slot_sep (w := w) (show aN ≠ aAcc by decide)
  have sNX := slot_sep (w := w) (show aN ≠ aR2 by decide)
  have sTA := slot_sep (w := w) (show aTmp ≠ aAcc by decide)
  have sTX := slot_sep (w := w) (show aTmp ≠ aR2 by decide)
  have lN := sl8 aN (by decide)
  have lT := sl8 aTmp (by decide)
  refine WP.seq (WP.mono (r2dStepN_ok hI.g hZ hw hw' hI.n hI.p hz hI.d hd hI.v (by rw [hI.x]; exact Nat.mod_lt _ hM0))
    fun t₁ ⟨g₁, x₁, a₁, k₁⟩ => ?_)
  have hcnt₁ : word t₁.mem B (8 * sCnt) = BitVec.ofNat 64 (c - j) := by
    rw [a₁.word_eq (fun j' hj' => Or.inl (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj'
      rcases hj' with rfl | rfl <;> exact hhs _)) (by have := hhs 8; omega_arith), hI.cnt]
  have arrs : ∀ j' ∈ [aAcc, aR2], ∀ d k, (d + 8 * k ≤ slot w aAcc ∨ slot w aAcc + 8 * (w + 2) ≤ d) →
      (d + 8 * k ≤ slot w aR2 ∨ slot w aR2 + 8 * (w + 2) ≤ d) →
      (d + 8 * k ≤ slot w j' ∨ slot w j' + 8 * (w + 2) ≤ d) := by
    intro j' hj' d k h1 h2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj'
    rcases hj' with rfl | rfl
    · exact h1
    · exact h2
  refine WP.mono (sqCount_ok g₁ hZ (c := c - j) (by omega_arith) (by omega_arith) hcnt₁)
    fun t' ⟨g', c', h13', o', k'⟩ => ⟨?_, by rw [h13', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]; omega_arith⟩
  have hN₁ : wv t₁.mem B (slot w aN) w = M := by
    rw [a₁.wv_eq (fun j' hj' => arrs j' hj' _ _ (by omega_arith) (by omega_arith)) (by omega_arith), hI.n]
  have hP₁ : word t₁.mem B (slot w aTmp + 8) = word t.mem B (slot w aTmp + 8) :=
    a₁.word_eq (fun j' hj' => arrs j' hj' _ 1 (by omega_arith) (by omega_arith)) (by omega_arith)
  have hT₁ : word t₁.mem B (slot w aTmp + 16) = word t.mem B (slot w aTmp + 16) :=
    a₁.word_eq (fun j' hj' => arrs j' hj' _ 1 (by omega_arith) (by omega_arith)) (by omega_arith)
  have hV₁ : word t₁.mem B (slot w aTmp) = word t.mem B (slot w aTmp) :=
    a₁.word_eq (fun j' hj' => arrs j' hj' _ 1 (by omega_arith) (by omega_arith)) (by omega_arith)
  refine ⟨g', by rw [c', show c - j - 1 = c - (j + 1) by omega_arith], ?_, ?_, ?_, ?_, ?_, ?_,
    ((hI.keep.trans k₁).trans k').mono (by decide)⟩
  · rw [o'.wv (by have := hhs aR2; omega_arith) (by have := sl8 aR2 (by decide); omega_arith), x₁, hI.x, Nat.mod_mul_mod,
      Nat.mul_assoc, ← Nat.pow_add, show 64 * j + 64 = 64 * (j + 1) by omega_arith]
  · rw [o'.wv (by have := hhs aN; omega_arith) (by omega_arith), hN₁]
  · rw [o'.word (by have := hhs aTmp; omega_arith) (by omega_arith), hP₁, hI.p]
  · rw [o'.word (by have := hhs aTmp; omega_arith) (by omega_arith), hT₁, hI.d]
  · rw [o'.word (by have := hhs aTmp; omega_arith) (by omega_arith), hV₁, hI.v]
  · exact (hI.frm.trans (Frm.of_arrays a₁ (by simp [r2Ranges]))).trans (Frm.of_outside o' (by simp [r2Ranges]))

/-- `steps`' start: the count `c` (in `x13`) into slot `sCnt`. -/
theorem r2dStepsStartN_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {M z c : Nat} (hg : Good s B Z w minv)
    (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) (h13 : s.gpr .x13 = BitVec.ofNat 64 c) (hM : wv s.mem B (slot w aN) w = M)
    (hP : (word s.mem B (slot w aTmp + 8)).toNat = 2 ^ z)
    (hD : (word s.mem B (slot w aTmp + 16)).toNat = M * 2 ^ z / 2 ^ (64 * (w - 1)))
    (hv : (word s.mem B (slot w aTmp)).toNat = (2 ^ 128 - 1) / (M * 2 ^ z / 2 ^ (64 * (w - 1))) - 2 ^ 64)
    (hX : wv s.mem B (slot w aR2) w < M) :
    WP isa (.block [sth .x13 sCnt]) s (R2dStepsInvN s B Z w minv M z (wv s.mem B (slot w aR2) w) c 0) := by
  have hn := hg.scr.nowrap
  have sl8 : ∀ j < 8, slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_le hj) hZ
  have hhs : ∀ j, 8 * sCnt + 8 ≤ slot w j := fun j => hdr_lt_slot w j (by decide)
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = s.mem.writeW (off B (8 * sCnt)) (s.gpr .x13))
    (by brun [hg.x0, hdr_enc (show sCnt < 32 by decide), hg.scr.st (show 8 * sCnt + 8 ≤ Z by have := hhs 8; omega_arith)])
    rfl rfl rfl) fun s₁ ⟨hm₁, k₁⟩ => ?_
  have o₁ : Outside B (8 * sCnt) 8 s.mem s₁.mem := by rw [hm₁]; exact writeW_outside _ _ _ (by have := hhs 8; omega_arith)
  exact ⟨⟨hg.scr.congr k₁.wr, (k₁.gpr .x0 (by decide)).trans hg.x0,
      by rw [hm₁]; exact Hdr.store hg.hdr (by decide) (by decide) _⟩,
      by rw [hm₁, word_writeW_self, h13, Nat.sub_zero],
      by rw [o₁.wv (by have := hhs aR2; omega_arith) (by have := sl8 aR2 (by decide); omega_arith), Nat.mul_zero, Nat.pow_zero,
        Nat.mul_one, Nat.mod_eq_of_lt hX],
      by rw [o₁.wv (by have := hhs aN; omega_arith) (by have := sl8 aN (by decide); omega_arith), hM],
      by rw [o₁.word (by have := hhs aTmp; omega_arith) (by have := sl8 aTmp (by decide); omega_arith), hP],
      by rw [o₁.word (by have := hhs aTmp; omega_arith) (by have := sl8 aTmp (by decide); omega_arith), hD],
      by rw [o₁.word (by have := hhs aTmp; omega_arith) (by have := sl8 aTmp (by decide); omega_arith), hv],
      Frm.of_outside o₁ (by simp [r2Ranges]), k₁.mono (by decide)⟩

/-- `stepsN`: `c ≥ 1` steps (`c` in `x13`), `x := x 2^(64 c) mod m`. -/
theorem r2dStepsN_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {M z c : Nat} (hg : Good s B Z w minv)
    (hZ : slot w 8 ≤ Z) (hw : 3 ≤ w) (hw' : w < 2 ^ 31) (hz : z ≤ 63) (hd : 2 ^ 63 ≤ M * 2 ^ z / 2 ^ (64 * (w - 1)))
    (hc : 1 ≤ c) (hc' : c < 2 ^ 31) (h13 : s.gpr .x13 = BitVec.ofNat 64 c) (hM : wv s.mem B (slot w aN) w = M)
    (hP : (word s.mem B (slot w aTmp + 8)).toNat = 2 ^ z)
    (hD : (word s.mem B (slot w aTmp + 16)).toNat = M * 2 ^ z / 2 ^ (64 * (w - 1)))
    (hv : (word s.mem B (slot w aTmp)).toNat = (2 ^ 128 - 1) / (M * 2 ^ z / 2 ^ (64 * (w - 1))) - 2 ^ 64)
    (hX : wv s.mem B (slot w aR2) w < M) :
    WP isa stepsN s (R2dStepsInvN s B Z w minv M z (wv s.mem B (slot w aR2) w) c c) := by
  have hM0 : 0 < M := Nat.lt_of_le_of_lt (Nat.zero_le _) hX
  unfold stepsN
  exact WP.seq (WP.mono (r2dStepsStartN_ok hg hZ (by omega_arith) h13 hM hP hD hv hX) fun s₁ h₀ =>
    count_loop (n := c) (by omega_arith) _ (fun j hj t hI => stepsIterN_ok hZ hw hw' hz hd hM0 hc' hj hI) h₀)

/-! ## `R² mod m` -/

/-- `setTop`, `x`'s base in `x11`: `x := 2^(64 (w - 1))`. -/
theorem setTop_ok {s : State} {B : Addr} {Z w eX : Nat} (hs : Scr s B Z) (h11 : s.gpr .x11 = off B eX)
    (h12 : s.gpr .x12 = BitVec.ofNat 64 w) (h7 : s.gpr .x7 = 0) (hw : 1 ≤ w) (hw' : w < 2 ^ 31)
    (hX : eX + 8 * (w + 2) ≤ Z) :
    WP isa setTop s fun t =>
      wv t.mem B eX w = 2 ^ (64 * (w - 1)) ∧ Outside B eX (8 * (w + 2)) s.mem t.mem ∧
        Keep [.x8, .x9, .x13, .x14, .x16] s t := by
  have hn := hs.nowrap
  unfold setTop
  refine WP.seq (WP.mono (WP.keep [.x8, .x9, .x13] (Q := fun t => t.gpr .x8 = off B eX ∧ (t.gpr .x9).toNat = 1 ∧
      t.gpr .x13 = BitVec.ofNat 64 (w - 1) ∧ t.mem = s.mem)
    (by
      brun [h11, h12]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega_arith) (by decide) (by decide) (by decide +kernel))
    fun s₁ ⟨⟨h8, h9, h13, hm₁⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (zeroAcc_ok (hs.congr k₁.wr) h8 ((k₁.gpr .x12 (by decide)).trans h12)
    ((k₁.gpr .x7 (by decide)).trans h7) hw' hX) fun s₂ ⟨hz, ho₂, k₂⟩ => ?_)
  have k12 := k₁.trans k₂
  have s₂8 : s₂.gpr .x8 = off B eX := (k₂.gpr .x8 (by decide)).trans h8
  have s₂i : s₂.gpr .x13 = BitVec.ofNat 64 (w - 1) := (k₂.gpr .x13 (by decide)).trans h13
  have s₂9 : s₂.gpr .x9 = s₁.gpr .x9 := k₂.gpr .x9 (by decide)
  have hi8 : (BitVec.ofNat 64 (w - 1) <<< 3 : BitVec 64) = BitVec.ofNat 64 (8 * (w - 1)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega_arith
  refine WP.mono (WP.keep [.x16] (Q := fun t => t.mem = s₂.mem.writeW (off B (eX + 8 * (w - 1))) (s₁.gpr .x9))
    (by brun [s₂8, s₂i, hi8, off_add, (hs.congr k12.wr).st (show eX + 8 * (w - 1) + 8 ≤ Z by omega_arith), s₂9])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨hm, k⟩ => ⟨?_, ?_, (k12.trans k).mono (by decide)⟩
  · have hz' := (wv_eq_zero_iff _ _ _ _).mp hz
    rw [wv_single t.mem B eX w (show w - 1 < w by omega_arith) fun q hq hne => by
      rw [hm, (writeW_outside s₂.mem B _ (by omega_arith)).word (by omega_arith) (by omega_arith)]
      exact hz' q (by omega_arith), hm, word_writeW_self, h9, Nat.one_mul]
  · rw [hm]
    intro x hx
    rw [writeW_outside _ B _ (by omega_arith) x (by omega_arith)]
    exact ho₂ x hx |>.trans (by rw [hm₁])

/-- `fastN`'s pieces before its steps: `P`, `d'`, `v`, `x := 2^(64 (w - 1))`
and the count `w + 1`. -/
theorem r2dFastNHead_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {M : Nat} (hg : Good s B Z w minv)
    (hZ : slot w 8 ≤ Z) (hw : 3 ≤ w) (hw30 : w < 2 ^ 30) (hM : wv s.mem B (slot w aN) w = M) (hodd : M % 2 = 1)
    (htop : 2 ^ (64 * (w - 1)) ≤ M) :
    WP isa (seqs [.block [ldh .x11 (sArr aR2), ldh .x9 (sArr aN), ldh .x6 (sArr aTmp), ldh .x12 sW, movi .x7 0],
        normN, recipN, setTop, .block [.addImm .x .x13 .x12 1]]) s fun t => Good t B Z w minv ∧
      t.gpr .x13 = BitVec.ofNat 64 (w + 1) ∧ wv t.mem B (slot w aN) w = M ∧
      (∃ z ≤ 63, (word t.mem B (slot w aTmp + 8)).toNat = 2 ^ z ∧
        (word t.mem B (slot w aTmp + 16)).toNat = M * 2 ^ z / 2 ^ (64 * (w - 1)) ∧
        2 ^ 63 ≤ M * 2 ^ z / 2 ^ (64 * (w - 1)) ∧
        (word t.mem B (slot w aTmp)).toNat = (2 ^ 128 - 1) / (M * 2 ^ z / 2 ^ (64 * (w - 1))) - 2 ^ 64) ∧
      wv t.mem B (slot w aR2) w = 2 ^ (64 * (w - 1)) ∧ 2 ^ (64 * (w - 1)) < M ∧
      Arrays B w [aR2, aTmp] s.mem t.mem ∧ Keep mmRegs s t := by
  have hw' : w < 2 ^ 31 := by omega_arith
  have hs := hg.scr
  have hn := hs.nowrap
  have sl8 : ∀ j < 8, slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_le hj) hZ
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hs.ld (by have := hdr_lt_slot w 8 hi; have := slot_le (w := w) (show 7 < 8 by decide); omega_arith)
  have sTN := slot_sep (w := w) (show aTmp ≠ aN by decide)
  have sXN := slot_sep (w := w) (show aR2 ≠ aN by decide)
  have sTX := slot_sep (w := w) (show aTmp ≠ aR2 by decide)
  have lN := sl8 aN (by decide)
  have lX := sl8 aR2 (by decide)
  have lT := sl8 aTmp (by decide)
  have hhs : ∀ j, 8 * sCnt + 8 ≤ slot w j := fun j => hdr_lt_slot w j (by decide)
  have hlt : 2 ^ (64 * (w - 1)) < M := Nat.lt_of_le_of_ne htop fun h => by
    rw [← h, show 64 * (w - 1) = (64 * (w - 1) - 1) + 1 by omega_arith, Nat.pow_succ, Nat.mul_mod_left] at hodd
    exact absurd hodd (by decide)
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.x6, .x7, .x9, .x11, .x12] (Q := fun t =>
    t.gpr .x11 = off B (slot w aR2) ∧ t.gpr .x9 = off B (slot w aN) ∧ t.gpr .x6 = off B (slot w aTmp) ∧
    t.gpr .x12 = BitVec.ofNat 64 w ∧ t.gpr .x7 = 0 ∧ t.mem = s.mem)
    (by brun [hg.x0, hdr_enc (show sArr aN < 32 by decide), hdr_enc (show sArr aR2 < 32 by decide),
        hdr_enc (show sArr aTmp < 32 by decide), hdr_enc (show sW < 32 by decide), hl (sArr aN) (by decide),
        hl (sArr aR2) (by decide), hl (sArr aTmp) (by decide), hl sW (by decide), hg.hdr.harr aN (by decide),
        hg.hdr.harr aR2 (by decide), hg.hdr.harr aTmp (by decide), hg.hdr.hw])
    (by decide) (by decide) (by decide +kernel)) fun t₁ ⟨⟨h11, h9, h6, h12, h7, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.wr
  -- `P` and `d'`.
  refine WP.seq (WP.mono (normN_ok hs₁ h9 h12 h6 (by omega_arith) hw' (by omega_arith) (by omega_arith)
    (by rw [hm₁, hM]; exact htop)) fun t₂ ⟨⟨z, hz, hP, hD, hd⟩, o₂, k₂⟩ => ?_)
  rw [hm₁, hM] at hD hd
  have hs₂ := hs₁.congr k₂.wr
  -- `v`.
  refine WP.seq (WP.mono (recipN_ok hs₂ ((k₂.gpr .x6 (by decide)).trans h6) ((k₂.gpr .x7 (by decide)).trans h7)
    (by omega_arith) (by rw [hD]; exact hd)) fun t₃ ⟨hv₃, o₃, k₃⟩ => ?_)
  rw [hD] at hv₃
  have hs₃ := hs₂.congr k₃.wr
  have a₃ : Arrays B w [aR2, aTmp] s.mem t₃.mem := by
    rw [← hm₁]
    exact (Arrays.of_outside (j := aTmp) (by decide) o₂ (by omega_arith) (by omega_arith)).trans
      (Arrays.of_outside (j := aTmp) (by decide) o₃ (Nat.le_refl _) (by omega_arith))
  have k13 := (k₁.trans k₂).trans k₃
  have k23 := k₂.trans k₃
  have h12₃ : t₃.gpr .x12 = BitVec.ofNat 64 w := (k23.gpr .x12 (by decide)).trans h12
  have P₃ : (word t₃.mem B (slot w aTmp + 8)).toNat = 2 ^ z := by
    rw [o₃.word (by omega_arith) (by omega_arith)]; exact hP
  have D₃ : (word t₃.mem B (slot w aTmp + 16)).toNat = M * 2 ^ z / 2 ^ (64 * (w - 1)) := by
    rw [o₃.word (by omega_arith) (by omega_arith)]; exact hD
  -- `x := 2^(64 (w - 1))`.
  refine WP.seq (WP.mono (setTop_ok hs₃ ((k23.gpr .x11 (by decide)).trans h11) h12₃
    ((k23.gpr .x7 (by decide)).trans h7) (by omega_arith) hw' lX) fun t₅ ⟨x₅, o₅, k₅⟩ => ?_)
  have hs₅ := hs₃.congr k₅.wr
  have a₅ : Arrays B w [aR2, aTmp] s.mem t₅.mem :=
    a₃.trans (Arrays.of_outside (j := aR2) (by decide) o₅ (Nat.le_refl _) (Nat.le_refl _))
  have k15 := k13.trans k₅
  -- The count `w + 1`.
  refine WP.mono (WP.keep [.x13] (Q := fun t => t.gpr .x13 = BitVec.ofNat 64 (w + 1) ∧ t.mem = t₅.mem)
    (by
      brun [(k₅.gpr .x12 (by decide)).trans h12₃]
      exact (BitVec.ofNat_add _ _).symm) (by decide) (by decide) (by decide +kernel)) fun t₆ ⟨⟨h13₆, hm₆⟩, k₆⟩ => ?_
  have k16 := k15.trans k₆
  have g₆ : Good t₆ B Z w minv :=
    ⟨hs₅.congr k₆.wr, (k16.gpr .x0 (by decide)).trans hg.x0, by rw [hm₆]; exact a₅.hdr hg.hdr⟩
  have sep : ∀ j ∈ [aR2, aTmp], ∀ d k, (d + 8 * k ≤ slot w aR2 ∨ slot w aR2 + 8 * (w + 2) ≤ d) →
      (d + 8 * k ≤ slot w aTmp ∨ slot w aTmp + 8 * (w + 2) ≤ d) →
      (d + 8 * k ≤ slot w j ∨ slot w j + 8 * (w + 2) ≤ d) := by
    intro j hj d k h1 h2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · exact h1
    · exact h2
  have N₆ : wv t₆.mem B (slot w aN) w = M := by
    rw [hm₆, a₅.wv_eq (fun j hj => sep j hj _ _ (by omega_arith) (by omega_arith)) (by omega_arith), hM]
  have T₆ : ∀ d, slot w aTmp ≤ d → d + 8 ≤ slot w aTmp + 8 * (w + 2) → word t₆.mem B d = word t₃.mem B d :=
    fun d h1 h2 => by rw [hm₆, o₅.word (by omega_arith) (by omega_arith)]
  have X₆ : wv t₆.mem B (slot w aR2) w = 2 ^ (64 * (w - 1)) := by rw [hm₆, x₅]
  exact ⟨g₆, h13₆, N₆, ⟨z, hz, by rw [T₆ _ (by omega_arith) (by omega_arith)]; exact P₃,
    by rw [T₆ _ (by omega_arith) (by omega_arith)]; exact D₃, hd, by rw [T₆ _ (Nat.le_refl _) (by omega_arith)]; exact hv₃⟩,
    X₆, hlt, by rw [hm₆]; exact a₅, k16.mono (by decide)⟩

/-- `fastN`: `R² mod m` into array `aR2`, for an odd `m` of `w ≥ 3` words whose
top word is not zero. -/
theorem r2dFastN_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {M : Nat} (hg : Good s B Z w minv)
    (hZ : slot w 8 ≤ Z) (hw : 3 ≤ w) (hw30 : w < 2 ^ 30) (hM : wv s.mem B (slot w aN) w = M) (hodd : M % 2 = 1)
    (htop : 2 ^ (64 * (w - 1)) ≤ M) :
    WP isa fastN s fun t => Good t B Z w minv ∧
      wv t.mem B (slot w aR2) w < M ∧ wv t.mem B (slot w aR2) w % M = 2 ^ (64 * w) * 2 ^ (64 * w) % M ∧
      Frm B (r2Ranges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hw' : w < 2 ^ 31 := by omega_arith
  refine wp_seqs_append (b := [stepsN]) (by simp) (by simp)
    (WP.mono (r2dFastNHead_ok hg hZ hw hw30 hM hodd htop)
      fun t₆ ⟨g₆, h13₆, N₆, ⟨z, hz, P₆, D₆, hd, V₆⟩, X₆, hlt, a₅, k16⟩ => ?_)
  -- `w + 1` steps.
  refine WP.mono (r2dStepsN_ok (c := w + 1) g₆ hZ hw hw' hz hd (by omega_arith) (by omega_arith) h13₆ N₆
    P₆ D₆ V₆ (by rw [X₆]; exact hlt)) fun t hI => ?_
  rw [X₆] at hI
  refine ⟨hI.g, by rw [hI.x]; exact Nat.mod_lt _ (by omega_arith), ?_, ?_, (k16.trans hI.keep).mono (by decide)⟩
  · rw [hI.x, Nat.mod_mod, ← Nat.pow_add, ← Nat.pow_add, show 64 * (w - 1) + 64 * (w + 1) = 64 * w + 64 * w by
      omega_arith]
  · exact (Frm.of_arrays a₅ (by simp [r2Ranges])).trans hI.frm

/-- `choiceW old f`: `old` for `w = 2` and `f` for `w ≥ 3`; both start from
`s`'s memory. -/
theorem r2dChoiceW_ok {old f : Prog isa} {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {Q : State → Prop}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hold : ∀ t, Good t B Z w minv → t.mem = s.mem → Keep mmRegs s t → w = 2 → WP isa old t Q)
    (hf : ∀ t, Good t B Z w minv → t.mem = s.mem → Keep mmRegs s t → 3 ≤ w → WP isa f t Q) :
    WP isa (choiceW old f) s Q := by
  have hs := hg.scr
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hs.ld (by have := hdr_lt_slot w 8 hi; have := slot_le (w := w) (show 7 < 8 by decide); omega_arith)
  refine WP.seq (WP.mono (WP.keep [.x12, .x13] (Q := fun t =>
    t.gpr .x13 = BitVec.ofNat 64 (w - 2) ∧ t.mem = s.mem)
    (by
      brun [hg.x0, hdr_enc (show sW < 32 by decide), hl sW (by decide), hg.hdr.hw]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega_arith)
    (by decide) (by decide) (by decide +kernel)) fun t₁ ⟨⟨h13, hm₁⟩, k₁⟩ => ?_)
  have g₁ : Good t₁ B Z w minv := ⟨hs.congr k₁.wr, (k₁.gpr .x0 (by decide)).trans hg.x0, by rw [hm₁]; exact hg.hdr⟩
  have hz : isa.eval (.zero .x .x13) t₁ = some (decide (w = 2)) := by
    rw [eval_zero, h13]
    congr 1
    by_cases h : w = 2
    · subst h; rfl
    · rw [decide_eq_false h]
      exact decide_eq_false fun e => h (by
        have : (BitVec.ofNat 64 (w - 2)).toNat = 0 := by rw [e]; rfl
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)] at this
        exact Nat.le_antisymm (by omega_arith) hw)
  by_cases h : w = 2
  · refine WP.ite true (by rw [hz, decide_eq_true h]) (fun _ => ?_) (by simp)
    exact hold t₁ g₁ hm₁ (k₁.mono (by decide)) h
  · refine WP.ite false (by rw [hz, decide_eq_false h]) (by simp) fun _ => ?_
    exact hf t₁ g₁ hm₁ (k₁.mono (by decide)) (by omega_arith)

end VG.Proof.Bignum.AArch64
