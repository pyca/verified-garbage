module
public import VerifiedGarbage.Impl.Bignum.AArch64.R2Div
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import VerifiedGarbage.Proof.Bignum.WordStep
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.AArch64.R2dQuot
import VerifiedGarbage.Proof.Bignum.AArch64.R2dSub
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-!
# `R² mod m` by long division on AArch64: a step

`step` makes `x := x 2^64 mod m` for `x < m` (array `aR2`), `m` of `w ≥ 2`
words (array `aN`) with its top bit set, and its reciprocal `v` in the first
word of array `aTmp` (`r2dStep_ok`), by `WordStep.wordStep_val`.
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.Public VG.Impl.Bignum.AArch64 VG.Impl.Bignum.AArch64.R2Div
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

/-- A number of `w ≥ 2` words: its top two words and the rest. -/
theorem wv_split2 (m : Mem) (B : Addr) (e : Nat) {w : Nat} (hw : 2 ≤ w) :
    wv m B e w = (word m B (e + 8 * (w - 1))).toNat * 2 ^ (64 * (w - 1)) +
      (word m B (e + 8 * (w - 2))).toNat * 2 ^ (64 * (w - 2)) + wv m B e (w - 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 2 := ⟨w - 2, by omega⟩
  rw [show k + 2 - 1 = k + 1 by omega, show k + 2 - 2 = k by omega, wv, wv]
  rw [Nat.mul_comm (2 ^ (64 * (k + 1))), Nat.mul_comm (2 ^ (64 * k))]
  omega

/-- A number of `w ≥ 1` words: its top word and the rest. -/
theorem wv_split1 (m : Mem) (B : Addr) (e : Nat) {w : Nat} (hw : 1 ≤ w) :
    wv m B e w = (word m B (e + 8 * (w - 1))).toNat * 2 ^ (64 * (w - 1)) + wv m B e (w - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega⟩
  rw [show k + 1 - 1 = k by omega, wv, Nat.mul_comm]
  omega

/-- The low `n` words are the number, if it is below `2^(64 n)`. -/
theorem wv_low_top (m : Mem) (B : Addr) (e n : Nat) (h : wv m B e (n + 1) < 2 ^ (64 * n)) :
    wv m B e n = wv m B e (n + 1) := by
  have e1 : wv m B e (n + 1) = wv m B e n + 2 ^ (64 * n) * (word m B (e + 8 * n)).toNat := rfl
  rcases Nat.eq_zero_or_pos (word m B (e + 8 * n)).toNat with h0 | h0
  · rw [e1, h0, Nat.mul_zero, Nat.add_zero]
  · have := Nat.mul_le_mul_left (2 ^ (64 * n)) h0
    omega

/-- The top word of `x < m` is at most that of `m`. -/
theorem r2d_top_le {m : Mem} {B : Addr} {eX eM w : Nat} (hw : 1 ≤ w)
    (h : wv m B eX w < wv m B eM w) :
    (word m B (eX + 8 * (w - 1))).toNat ≤ (word m B (eM + 8 * (w - 1))).toNat := by
  have hx := wv_split1 m B eX hw
  have hm := wv_split1 m B eM hw
  have lx := wv_lt m B eX (w - 1)
  have lm := wv_lt m B eM (w - 1)
  have dx : wv m B eX w / 2 ^ (64 * (w - 1)) = (word m B (eX + 8 * (w - 1))).toNat := by
    rw [hx, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt lx, Nat.zero_add]
  have dm : wv m B eM w / 2 ^ (64 * (w - 1)) = (word m B (eM + 8 * (w - 1))).toNat := by
    rw [hm, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt lm, Nat.zero_add]
  rw [← dx, ← dm]
  exact Nat.div_le_div_right (Nat.le_of_lt h)

/-! ## The pieces of a step -/

/-- The registers of a step after `bases`. -/
structure StepRegs (t : State) (B : Addr) (w : Nat) : Prop where
  x8 : t.gpr .x8 = off B (slot w aAcc)
  x9 : t.gpr .x9 = off B (slot w aN)
  x11 : t.gpr .x11 = off B (slot w aR2)
  x6 : t.gpr .x6 = off B (slot w aTmp)
  x12 : t.gpr .x12 = BitVec.ofNat 64 w
  x7 : t.gpr .x7 = 0

theorem StepRegs.keep {t t' : State} {B : Addr} {w : Nat} (h : StepRegs t B w) {rs : List Reg} (k : Keep rs t t')
    (h8 : Reg.x8 ∉ rs := by decide) (h9 : Reg.x9 ∉ rs := by decide) (h11 : Reg.x11 ∉ rs := by decide)
    (h6 : Reg.x6 ∉ rs := by decide) (h12 : Reg.x12 ∉ rs := by decide) (h7 : Reg.x7 ∉ rs := by decide) :
    StepRegs t' B w :=
  ⟨(k.gpr .x8 h8).trans h.x8, (k.gpr .x9 h9).trans h.x9, (k.gpr .x11 h11).trans h.x11,
    (k.gpr .x6 h6).trans h.x6, (k.gpr .x12 h12).trans h.x12, (k.gpr .x7 h7).trans h.x7⟩

/-- `bases` and `quot`: the registers, and `q̂` in `x1`. -/
theorem r2dHead_ok {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good t B Z w minv)
    (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hu : (word t.mem B (slot w aR2 + 8 * (w - 1))).toNat ≤ (word t.mem B (slot w aN + 8 * (w - 1))).toNat)
    (hd : 2 ^ 63 ≤ (word t.mem B (slot w aN + 8 * (w - 1))).toNat)
    (hv : (word t.mem B (slot w aTmp)).toNat = (2 ^ 128 - 1) / (word t.mem B (slot w aN + 8 * (w - 1))).toNat - 2 ^ 64) :
    WP isa (.block (R2Div.bases ++ quot)) t fun t' => StepRegs t' B w ∧
      t'.gpr .x1 = BitVec.ofNat 64 (min (((word t.mem B (slot w aR2 + 8 * (w - 1))).toNat * 2 ^ 64 +
        (word t.mem B (slot w aR2 + 8 * (w - 2))).toNat) / (word t.mem B (slot w aN + 8 * (w - 1))).toNat)
          (2 ^ 64 - 1)) ∧
      t'.mem = t.mem ∧ Keep mmRegs t t' := by
  have hs := hg.scr
  have hn := hs.nowrap
  have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off B (8 * i)) 8 := fun i hi =>
    hs.ld (by have := hdr_lt_slot w 8 hi; have := slot_le (w := w) (show 7 < 8 by decide); omega)
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
  rw [← hm₁] at hu hd hv
  refine WP.mono (r2dQuot_ok hs₁ hr.x11 hr.x9 hr.x12 hr.x6 hr.x7 hw hw' (by have := sl aR2 (by decide); omega)
    (by have := sl aN (by decide); omega) (by have := sl aTmp (by decide); omega) hu hd hv)
    fun t' ⟨h1, hm, k⟩ => ⟨hr.keep k, by rw [h1, hm₁], by rw [hm, hm₁], (k₁.trans k).mono (by decide)⟩

/-! ## A step -/

/-- `x := x 2^64 mod m`: `x < m` (array `aR2`) for `m` (array `aN`) of `w ≥ 2`
words, its top word `D ≥ 2^63`, and `v` for `D` in the first word of `aTmp`. -/
theorem r2dStep_ok {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {M D : Nat} (hg : Good t B Z w minv)
    (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31) (hM : wv t.mem B (slot w aN) w = M)
    (hD : (word t.mem B (slot w aN + 8 * (w - 1))).toNat = D) (hd : 2 ^ 63 ≤ D)
    (hv : (word t.mem B (slot w aTmp)).toNat = (2 ^ 128 - 1) / D - 2 ^ 64)
    (hX : wv t.mem B (slot w aR2) w < M) :
    WP isa step t fun t' => Good t' B Z w minv ∧
      wv t'.mem B (slot w aR2) w = wv t.mem B (slot w aR2) w * 2 ^ 64 % M ∧
      Arrays B w [aAcc, aR2] t.mem t'.mem ∧ Keep mmRegs t t' := by
  have hs := hg.scr
  have hn := hs.nowrap
  have sl : ∀ j < 8, slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_le hj) hZ
  have lA := sl aAcc (by decide)
  have lM := sl aN (by decide)
  have lX := sl aR2 (by decide)
  have sAM := slot_sep (w := w) (show aAcc ≠ aN by decide)
  have sAX := slot_sep (w := w) (show aAcc ≠ aR2 by decide)
  have sXM := slot_sep (w := w) (show aR2 ≠ aN by decide)
  have hu := r2d_top_le (m := t.mem) (B := B) (by omega : 1 ≤ w) (hM ▸ hX)
  unfold step
  simp only [seqs]
  refine WP.seq (WP.mono (r2dHead_ok hg hZ hw hw' hu (by rw [hD]; exact hd) (by rw [hv, hD]))
    fun t₁ ⟨r₁, h1, hm₁, k₁⟩ => ?_)
  rw [hD] at h1
  generalize hq : min (((word t.mem B (slot w aR2 + 8 * (w - 1))).toNat * 2 ^ 64 +
    (word t.mem B (slot w aR2 + 8 * (w - 2))).toNat) / D) (2 ^ 64 - 1) = q at h1
  have hqB : q < 2 ^ 64 := by rw [← hq]; exact Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by decide)
  have hs₁ := hs.congr k₁.wr
  generalize hXv : wv t.mem B (slot w aR2) w = X at hX
  have hXw := wv_split2 t.mem B (slot w aR2) hw
  have hMw := wv_split1 t.mem B (slot w aN) (show 1 ≤ w by omega)
  have hXl := wv_lt t.mem B (slot w aR2) (w - 2)
  have hml := wv_lt t.mem B (slot w aN) (w - 1)
  rw [hXv] at hXw
  rw [hM, hD] at hMw
  have hMB : M < 2 ^ (64 * w) := hM ▸ wv_lt _ _ _ _
  -- `[acc] := 0`.
  refine WP.seq (WP.mono (zeroAcc_ok hs₁ r₁.x8 r₁.x12 r₁.x7 hw' lA) fun t₂ ⟨hz₂, o₂, k₂⟩ => ?_)
  have r₂ := r₁.keep k₂
  have hs₂ := hs₁.congr k₂.wr
  have M₂ : wv t₂.mem B (slot w aN) w = M := by
    rw [o₂.wv (by omega) (by omega), hm₁, hM]
  have X₂ : wv t₂.mem B (slot w aR2) w = X := by
    rw [o₂.wv (by omega) (by omega), hm₁, hXv]
  -- `[acc] := q̂ m`.
  have hqM : q * M < 2 ^ (64 * (w + 1)) := by
    rw [pow64_succ, Nat.mul_comm (2 ^ (64 * w))]
    exact Nat.mul_lt_mul_of_lt_of_le hqB (Nat.le_of_lt hMB) (by omega)
  refine WP.seq (WP.mono (mulAddRow_ok hs₂ r₂.x8 r₂.x9 r₂.x12 r₂.x7 (by omega) hw' lA (by omega) (by omega)
    (by rw [hz₂, M₂, (k₂.gpr .x1 (by decide)).trans h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hqB, Nat.zero_add]
        exact Nat.lt_of_lt_of_le hqM (Nat.pow_le_pow_right (by decide) (by omega))))
    fun t₃ ⟨hv₃, o₃, k₃⟩ => ?_)
  rw [hz₂, M₂, (k₂.gpr .x1 (by decide)).trans h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hqB, Nat.zero_add]
    at hv₃
  have r₃ := r₂.keep k₃
  have hs₃ := hs₂.congr k₃.wr
  have P₃ : wv t₃.mem B (slot w aAcc) (w + 1) = q * M := by
    rw [wv_low_top t₃.mem B (slot w aAcc) (w + 1) (by rw [hv₃]; exact hqM), hv₃]
  have X₃ : wv t₃.mem B (slot w aR2) w = X := by rw [o₃.wv (by omega) (by omega), X₂]
  have M₃ : wv t₃.mem B (slot w aN) w = M := by rw [o₃.wv (by omega) (by omega), M₂]
  -- `t := x 2^64 - q̂ m`.
  refine WP.seq (WP.mono (subPass_ok hs₃ r₃.x8 r₃.x11 r₃.x12 r₃.x7 (by omega) hw' (by omega) (by omega)
    (by omega)) fun t₄ ⟨b, hv₄, o₄, k₄⟩ => ?_)
  rw [P₃, X₃] at hv₄
  have r₄ := r₃.keep k₄
  have hs₄ := hs₃.congr k₄.wr
  have M₄ : wv t₄.mem B (slot w aN) w = M := by rw [o₄.wv (by omega) (by omega), M₃]
  -- `m` added back while `t` is negative.
  refine WP.seq (WP.mono (r2dAddBack_ok hs₄ r₄.x8 r₄.x9 r₄.x12 r₄.x7 (by omega) hw' (by omega) (by omega)
    (by omega)) fun t₅ ⟨c1, hv₅, o₅, k₅⟩ => ?_)
  rw [M₄] at hv₅
  have r₅ := r₄.keep k₅
  have hs₅ := hs₄.congr k₅.wr
  have M₅ : wv t₅.mem B (slot w aN) w = M := by rw [o₅.wv (by omega) (by omega), M₄]
  refine WP.seq (WP.mono (r2dAddBack_ok hs₅ r₅.x8 r₅.x9 r₅.x12 r₅.x7 (by omega) hw' (by omega) (by omega)
    (by omega)) fun t₆ ⟨c2, hv₆, o₆, k₆⟩ => ?_)
  rw [M₅] at hv₆
  have r₆ := r₅.keep k₆
  have hs₆ := hs₅.congr k₆.wr
  -- The value.
  have hT3 : wv t₆.mem B (slot w aAcc) (w + 1) = X * 2 ^ 64 % M := by
    refine WordStep.wordStep_val hw hXw hXl hMw hml hd (hD ▸ BitVec.isLt _) hX (wv_lt _ _ _ _) (Bool.toNat_lt b)
      ?_ (wv_lt _ _ _ _) (Bool.toNat_lt c1) hv₅ (wv_lt _ _ _ _) (Bool.toNat_lt c2) hv₆
    rw [hq]; omega
  -- `x := t`.
  unfold copyBack
  refine WP.seq (WP.mono (WP.keep [.x16, .x17] (Q := fun t₇ => t₇.gpr .x16 = off B (slot w aAcc) ∧
    t₇.gpr .x17 = off B (slot w aR2) ∧ t₇.mem = t₆.mem) (by brun [r₆.x8, r₆.x11]) (by decide) (by decide)
    (by decide +kernel)) fun t₇ ⟨⟨h16, h17, hm₇⟩, k₇⟩ => ?_)
  have r₇ := r₆.keep k₇
  have hs₇ := hs₆.congr k₇.wr
  refine WP.mono (copyWords_ok h16 h17 r₇.x12 (by omega) hw' (by omega)
    (fun j hj => hs₇.ld (by omega)) (fun j hj => hs₇.st (by omega))
    (fun j hj i hi => by rw [ofs_off B (by omega)]; omega)) fun t' ⟨hc, _, o', _, _, k'⟩ => ?_
  have hMod : X * 2 ^ 64 % M < 2 ^ (64 * w) := Nat.lt_trans (Nat.mod_lt _ (by omega)) hMB
  have kk : Keep mmRegs t t' :=
    ((((((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k₆).trans k₇).trans k').mono (by decide))
  have ha : Arrays B w [aAcc, aR2] t.mem t'.mem := by
    have mA : aAcc ∈ [aAcc, aR2] := by decide
    have mX : aR2 ∈ [aAcc, aR2] := by decide
    rw [← hm₁]
    refine (((((Arrays.of_outside mA o₂ (Nat.le_refl _) (Nat.le_refl _)).trans
      (Arrays.of_outside mA o₃ (Nat.le_refl _) (Nat.le_refl _))).trans
      (Arrays.of_outside mA o₄ (Nat.le_refl _) (by omega))).trans
      (Arrays.of_outside mA o₅ (Nat.le_refl _) (by omega))).trans
      (Arrays.of_outside mA o₆ (Nat.le_refl _) (by omega))).trans ?_
    rw [← hm₇]
    exact Arrays.of_outside mX o' (Nat.le_refl _) (by omega)
  refine ⟨⟨hs₇.congr k'.wr, (kk.gpr .x0 (by decide)).trans hg.x0, ha.hdr hg.hdr⟩, ?_, ha, kk⟩
  rw [hc, hm₇, wv_low_top t₆.mem B (slot w aAcc) w (by rw [hT3]; exact hMod), hT3]

end VG.Proof.Bignum.AArch64
