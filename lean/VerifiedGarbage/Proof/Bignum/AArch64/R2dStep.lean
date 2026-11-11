module
public import VerifiedGarbage.Impl.Bignum.AArch64.R2Div
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

import VerifiedGarbage.Proof.Bignum.WordStep
import VerifiedGarbage.Proof.Bignum.WordStepNorm
import VerifiedGarbage.Proof.Bignum.AArch64.R2dQuot
import VerifiedGarbage.Proof.Bignum.AArch64.R2dRecip
import VerifiedGarbage.Proof.Bignum.AArch64.R2dSub
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# `R² mod m` by long division on AArch64: a step

`step` makes `x := x 2^64 mod m` for `x < m` (array `aR2`), `m` of `w ≥ 2`
words (array `aN`) with its top bit set, and its reciprocal `v` in the first
word of array `aTmp` (`r2dStep_ok`): `quot` estimates the quotient from the
top two words of `x` and the top word of `m`, `quot3` corrects it with the
next words (`r2dQuot3_ok`) to `q̂ = r2dQ X M w`, within one of the quotient
(`r2dQ_bounds`, `WordStep.qhat3_norm`), `mulSub` computes `x 2^64 - q̂ m`
in place of `x`, and `m` is added back once if that is negative
(`WordStep.wordStepQ1_val`, `r2dFin_ok`). So does `stepPub`, whose
`addBackPub` branches on the sign that `addBack` masks by
(`r2dStepPub_ok`): both are `r2dStepWith_ok` for a program that does what
`addBack` does (`AddBackSpec`).
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.Public VG.Impl.Bignum.AArch64 VG.Impl.Bignum.AArch64.R2Div
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

/-- A number of `w ≥ 2` words: its top two words and the rest. -/
theorem wv_split2 (m : Mem) (B : Addr) (e : Nat) {w : Nat} (hw : 2 ≤ w) :
    wv m B e w = (word m B (e + 8 * (w - 1))).toNat * 2 ^ (64 * (w - 1)) +
      (word m B (e + 8 * (w - 2))).toNat * 2 ^ (64 * (w - 2)) + wv m B e (w - 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 2 := ⟨w - 2, by omega_arith⟩
  rw [show k + 2 - 1 = k + 1 by omega_arith, show k + 2 - 2 = k by omega_arith, wv, wv]
  rw [Nat.mul_comm (2 ^ (64 * (k + 1))), Nat.mul_comm (2 ^ (64 * k))]
  omega_arith

/-- A number of `w ≥ 1` words: its top word and the rest. -/
theorem wv_split1 (m : Mem) (B : Addr) (e : Nat) {w : Nat} (hw : 1 ≤ w) :
    wv m B e w = (word m B (e + 8 * (w - 1))).toNat * 2 ^ (64 * (w - 1)) + wv m B e (w - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega_arith⟩
  rw [show k + 1 - 1 = k by omega_arith, wv, Nat.mul_comm]
  omega_arith

/-- The low `n` words are the number, if it is below `2^(64 n)`. -/
theorem wv_low_top (m : Mem) (B : Addr) (e n : Nat) (h : wv m B e (n + 1) < 2 ^ (64 * n)) :
    wv m B e n = wv m B e (n + 1) := by
  have e1 : wv m B e (n + 1) = wv m B e n + 2 ^ (64 * n) * (word m B (e + 8 * n)).toNat := rfl
  rcases Nat.eq_zero_or_pos (word m B (e + 8 * n)).toNat with h0 | h0
  · rw [e1, h0, Nat.mul_zero, Nat.add_zero]
  · have := Nat.mul_le_mul_left (2 ^ (64 * n)) h0
    omega_arith

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

/-- The top two of three words. -/
theorem div64_3 {a b c : Nat} (hc : c < 2 ^ 64) : (a * 2 ^ 128 + b * 2 ^ 64 + c) / 2 ^ 64 = a * 2 ^ 64 + b := by
  have e : a * 2 ^ 128 + b * 2 ^ 64 + c = c + 2 ^ 64 * (a * 2 ^ 64 + b) := by
    rw [show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 from rfl]
    generalize (2 : Nat) ^ 64 = W
    rw [Nat.mul_add]; ac_rfl
  rw [e, Nat.add_mul_div_left _ _ (Nat.two_pow_pos 64), Nat.div_eq_of_lt hc, Nat.zero_add]

/-- The top of two words. -/
theorem div64_2 {a c : Nat} (hc : c < 2 ^ 64) : (a * 2 ^ 64 + c) / 2 ^ 64 = a := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos 64), Nat.div_eq_of_lt hc, Nat.zero_add]

/-- The top word of `m` of `w ≥ 1` words. -/
theorem wv_top1 (m : Mem) (B : Addr) (e : Nat) {w : Nat} (hw : 1 ≤ w) :
    wv m B e w / 2 ^ (64 * (w - 1)) = (word m B (e + 8 * (w - 1))).toNat := by
  rw [wv_split1 m B e hw, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
    Nat.div_eq_of_lt (wv_lt m B e (w - 1)), Nat.zero_add]

/-- The top three words of `x 2^64`, for `x` of `w ≥ 2` words: its top
words and, for `w ≥ 3`, its word `w - 3`. -/
theorem wv_top3 (m : Mem) (B : Addr) (e : Nat) {w : Nat} (hw : 2 ≤ w) :
    wv m B e w * 2 ^ 64 / 2 ^ (64 * (w - 2)) = (word m B (e + 8 * (w - 1))).toNat * 2 ^ 128 +
      (word m B (e + 8 * (w - 2))).toNat * 2 ^ 64 + (if w = 2 then 0 else (word m B (e + 8 * w - 24)).toNat) := by
  have h1 := wv_split2 m B e hw
  by_cases h2 : w = 2
  · subst h2
    rw [h1]
    simp only [↓reduceIte]
    generalize (word m B (e + 8 * (2 - 1))).toNat = b
    generalize (word m B (e + 8 * (2 - 2))).toNat = a
    rw [show wv m B e (2 - 2) = 0 from rfl, show 64 * (2 - 2) = 0 from rfl, show 64 * (2 - 1) = 64 from rfl,
      Nat.pow_zero, Nat.mul_one, Nat.add_zero, Nat.add_zero, Nat.div_one, show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 from rfl]
    generalize (2 : Nat) ^ 64 = W
    rw [Nat.add_mul, Nat.mul_assoc]
  · simp only [h2, ↓reduceIte]
    have h0 := wv_split1 m B e (show 1 ≤ w - 2 by omega_arith)
    have hl := wv_lt m B e (w - 2 - 1)
    rw [show e + 8 * (w - 2 - 1) = e + 8 * w - 24 by omega_arith] at h0
    have p1 : 2 ^ (64 * (w - 1)) = 2 ^ (64 * (w - 2 - 1)) * 2 ^ 128 := by
      rw [← Nat.pow_add]; congr 1; omega_arith
    have p2 : 2 ^ (64 * (w - 2)) = 2 ^ (64 * (w - 2 - 1)) * 2 ^ 64 := by
      rw [← Nat.pow_add]; congr 1; omega_arith
    rw [p2, Nat.mul_div_mul_right _ _ (Nat.two_pow_pos 64), h1, h0, p1, p2]
    generalize 2 ^ (64 * (w - 2 - 1)) = P at hl ⊢
    generalize (word m B (e + 8 * (w - 1))).toNat = a
    generalize (word m B (e + 8 * (w - 2))).toNat = b
    generalize (word m B (e + 8 * w - 24)).toNat = c
    generalize wv m B e (w - 2 - 1) = l at hl ⊢
    have hP : 0 < P := Nat.lt_of_le_of_lt (Nat.zero_le _) hl
    rw [show a * (P * 2 ^ 128) + b * (P * 2 ^ 64) + (c * P + l) = l + P * (a * 2 ^ 128 + b * 2 ^ 64 + c) by
      rw [Nat.mul_add, Nat.mul_add]; ac_rfl,
      Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt hl, Nat.zero_add]

/-- The top two words of `m` of `w ≥ 2` words. -/
theorem wv_top2 (m : Mem) (B : Addr) (e : Nat) {w : Nat} (hw : 2 ≤ w) :
    wv m B e w * 2 ^ 64 / 2 ^ (64 * (w - 1)) =
      (word m B (e + 8 * (w - 1))).toNat * 2 ^ 64 + (word m B (e + 8 * (w - 2))).toNat := by
  have h := wv_split2 m B e hw
  have hl := wv_lt m B e (w - 2)
  have e1 : 2 ^ (64 * (w - 1)) = 2 ^ (64 * (w - 2)) * 2 ^ 64 := by
    rw [← Nat.pow_add]; congr 1; omega_arith
  rw [e1, Nat.mul_div_mul_right _ _ (Nat.two_pow_pos 64), h, e1]
  generalize 2 ^ (64 * (w - 2)) = P at hl ⊢
  generalize (word m B (e + 8 * (w - 1))).toNat = a
  generalize (word m B (e + 8 * (w - 2))).toNat = b
  generalize wv m B e (w - 2) = l at hl ⊢
  have hP : 0 < P := Nat.lt_of_le_of_lt (Nat.zero_le _) hl
  rw [show a * (P * 2 ^ 64) + b * P + l = l + P * (a * 2 ^ 64 + b) by rw [Nat.mul_add]; ac_rfl,
    Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt hl, Nat.zero_add]

/-- The estimate of a step's quotient: `min(⌊U / D⌋, 2^64 - 1)` for the top
three words `U` of `X 2^64` and the top two `D` of `M`, of `w` words. -/
def r2dQ (X M w : Nat) : Nat := min (X * 2 ^ 64 / 2 ^ (64 * (w - 2)) / (M * 2 ^ 64 / 2 ^ (64 * (w - 1)))) (2 ^ 64 - 1)

theorem r2dQ_K {w : Nat} (hw : 2 ≤ w) : 64 * (w - 1) = 64 * (w - 2) + 64 := by omega_arith

/-- The estimate is within one of the quotient (`WordStep.qhat3_norm`), for
`X < M` and `M`'s top word at least `2^63`; and `U < (2^64 + 1) D`, and the
2-by-1 estimate from `U`'s and `D`'s top words is at most 2 above it. -/
theorem r2dQ_norm {X M w : Nat} (hw : 2 ≤ w) (hXM : X < M) (hd : 2 ^ 63 ≤ M / 2 ^ (64 * (w - 1))) :
    X * 2 ^ 64 / 2 ^ (64 * (w - 2)) < (2 ^ 64 + 1) * (M * 2 ^ 64 / 2 ^ (64 * (w - 1))) ∧
      r2dQ X M w ≤ min (X * 2 ^ 64 / 2 ^ (64 * (w - 2)) / 2 ^ 64 / (M * 2 ^ 64 / 2 ^ (64 * (w - 1)) / 2 ^ 64))
        (2 ^ 64 - 1) ∧
      min (X * 2 ^ 64 / 2 ^ (64 * (w - 2)) / 2 ^ 64 / (M * 2 ^ 64 / 2 ^ (64 * (w - 1)) / 2 ^ 64)) (2 ^ 64 - 1) ≤
        r2dQ X M w + 2 ∧
      X * 2 ^ 64 / M ≤ r2dQ X M w ∧ r2dQ X M w ≤ X * 2 ^ 64 / M + 1 := by
  have e : ∀ Y, Y * 2 ^ 64 / 2 ^ (64 * (w - 2) + 64) = Y / 2 ^ (64 * (w - 2)) := fun Y => by
    rw [Nat.pow_add, Nat.mul_div_mul_right _ _ (Nat.two_pow_pos 64)]
  have hd' : 2 ^ 63 ≤ M * 2 ^ 64 / 2 ^ (64 * (w - 2) + 64) / 2 ^ 64 := by
    rw [e, Nat.div_div_eq_div_mul, ← Nat.pow_add, ← r2dQ_K hw]; exact hd
  have h := WordStep.qhat3_norm (P := 2 ^ 64) (K := 64 * (w - 2)) (Nat.two_pow_pos 64) hXM hd'
  rw [← r2dQ_K hw] at h
  exact h

/-! ## The pieces of a step -/

/-- The registers of a step after `bases`. -/
structure StepRegs (t : State) (B : Addr) (w : Nat) : Prop where
  x9 : t.gpr .x9 = off B (slot w aN)
  x11 : t.gpr .x11 = off B (slot w aR2)
  x6 : t.gpr .x6 = off B (slot w aTmp)
  x12 : t.gpr .x12 = BitVec.ofNat 64 w
  x7 : t.gpr .x7 = 0

theorem StepRegs.keep {t t' : State} {B : Addr} {w : Nat} (h : StepRegs t B w) {rs : List Reg} (k : Keep rs t t')
    (h9 : Reg.x9 ∉ rs := by decide) (h11 : Reg.x11 ∉ rs := by decide)
    (h6 : Reg.x6 ∉ rs := by decide) (h12 : Reg.x12 ∉ rs := by decide) (h7 : Reg.x7 ∉ rs := by decide) :
    StepRegs t' B w :=
  ⟨(k.gpr .x9 h9).trans h.x9, (k.gpr .x11 h11).trans h.x11,
    (k.gpr .x6 h6).trans h.x6, (k.gpr .x12 h12).trans h.x12, (k.gpr .x7 h7).trans h.x7⟩

/-- `bases`: the registers of a step. -/
theorem r2dBasesRun_ok {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good t B Z w minv)
    (hZ : slot w 8 ≤ Z) : WP isa (.block R2Div.bases) t fun t' => (StepRegs t' B w ∧ t'.mem = t.mem) ∧
      Keep [.x6, .x7, .x9, .x11, .x12] t t' := by
  have hs := hg.scr
  have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off B (8 * i)) 8 := fun i hi =>
    hs.ld (by have := hdr_lt_slot w 8 hi; have := slot_le (w := w) (show 7 < 8 by decide); omega_arith)
  refine WP.keep [.x6, .x7, .x9, .x11, .x12] (Q := fun t' => StepRegs t' B w ∧ t'.mem = t.mem)
    (WP.mono (Q := fun (t' : State) => (t'.gpr .x9 = off B (slot w aN) ∧
        t'.gpr .x11 = off B (slot w aR2) ∧ t'.gpr .x6 = off B (slot w aTmp) ∧ t'.gpr .x12 = BitVec.ofNat 64 w ∧
        t'.gpr .x7 = 0) ∧ t'.mem = t.mem) ?_ fun t' ⟨⟨a, b, c, d, e⟩, g⟩ => ⟨⟨a, b, c, d, e⟩, g⟩)
    (by decide) (by decide) (by decide +kernel)
  brun [R2Div.bases, hg.x0, hdr_enc (show sArr aN < 32 by decide),
    hdr_enc (show sArr aR2 < 32 by decide), hdr_enc (show sArr aTmp < 32 by decide),
    hdr_enc (show sW < 32 by decide), hl (sArr aN) (by decide),
    hl (sArr aR2) (by decide), hl (sArr aTmp) (by decide), hl sW (by decide),
    hg.hdr.harr aN (by decide), hg.hdr.harr aR2 (by decide),
    hg.hdr.harr aTmp (by decide), hg.hdr.hw]

/-- `bases` and `quot`: the registers, `q̂₀` in `x1`, and `x`'s and `m`'s top
words in `x2` and `x5`. -/
theorem r2dHead_ok {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good t B Z w minv)
    (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hu : (word t.mem B (slot w aR2 + 8 * (w - 1))).toNat ≤ (word t.mem B (slot w aN + 8 * (w - 1))).toNat)
    (hd : 2 ^ 63 ≤ (word t.mem B (slot w aN + 8 * (w - 1))).toNat)
    (hv : (word t.mem B (slot w aTmp)).toNat = (2 ^ 128 - 1) / (word t.mem B (slot w aN + 8 * (w - 1))).toNat - 2 ^ 64) :
    WP isa (.block (R2Div.bases ++ quot)) t fun t' => StepRegs t' B w ∧
      t'.gpr .x1 = BitVec.ofNat 64 (min (((word t.mem B (slot w aR2 + 8 * (w - 1))).toNat * 2 ^ 64 +
        (word t.mem B (slot w aR2 + 8 * (w - 2))).toNat) / (word t.mem B (slot w aN + 8 * (w - 1))).toNat)
          (2 ^ 64 - 1)) ∧
      t'.gpr .x2 = word t.mem B (slot w aR2 + 8 * (w - 1)) ∧ t'.gpr .x5 = word t.mem B (slot w aN + 8 * (w - 1)) ∧
      t'.mem = t.mem ∧ Keep mmRegs t t' := by
  have hs := hg.scr
  have sl : ∀ j < 8, slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_le hj) hZ
  rw [WP.block_append_iff]
  refine WP.mono (r2dBasesRun_ok hg hZ) fun t₁ ⟨⟨hr, hm₁⟩, k₁⟩ => ?_
  have hs₁ := hs.congr k₁.wr
  rw [← hm₁] at hu hd hv
  refine WP.mono (r2dQuot_ok hs₁ hr.x11 hr.x9 hr.x12 hr.x6 hr.x7 hw hw' (by have := sl aR2 (by decide); omega_arith)
    (by have := sl aN (by decide); omega_arith) (by have := sl aTmp (by decide); omega_arith) hu hd hv)
    fun t' ⟨h1, h2, h5, hm, k⟩ => ⟨hr.keep k, by rw [h1, hm₁], by rw [h2, hm₁], by rw [h5, hm₁], by rw [hm, hm₁],
      (k₁.trans k).mono (by decide)⟩

/-- `8 w - 24` added to an offset `e ≥ 8`, as `quot3Load` computes it. -/
theorem off_w24 (B : Addr) {e w : Nat} (he : 8 ≤ e) (hw : 2 ≤ w) (hw' : w < 2 ^ 61) :
    off B e + (BitVec.ofNat 64 w <<< 3 - BitVec.ofNat 64 24) = off B (e + 8 * w - 24) := by
  rw [r2d_ofNat_shl3 hw']
  apply BitVec.eq_of_toNat_eq
  have := B.isLt
  simp only [off, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega_arith

/-- `w - 2` is zero iff `w = 2`, as `quot3Load` tests it. -/
theorem w2_test {w : Nat} (hw : 2 ≤ w) (hw' : w < 2 ^ 61) :
    decide ((BitVec.ofNat 64 w - BitVec.ofNat 64 2 &&& BitVec.ofNat 64 w - BitVec.ofNat 64 2) = 0) = decide (w = 2) := by
  rw [BitVec.and_self]
  apply decide_eq_decide.mpr
  rw [BitVec.sub_eq_iff_eq_add, show (0 : BitVec 64) + BitVec.ofNat 64 2 = BitVec.ofNat 64 2 from rfl]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith : w < 2 ^ 64),
      Nat.mod_eq_of_lt (by decide : 2 < 2 ^ 64)] at this
    exact this
  · rintro rfl; rfl

/-- `quot3Load`: `u₁ = x[w - 2]` (`x3`), `u₀ = x[w - 3]` or 0 for `w = 2`
(`x4`), and `dₗ = m[w - 2]` (`x15`). -/
theorem quot3Load_ok {t : State} {B : Addr} {Z w eX eM : Nat} (hs : Scr t B Z)
    (h11 : t.gpr .x11 = off B eX) (h9 : t.gpr .x9 = off B eM) (h12 : t.gpr .x12 = BitVec.ofNat 64 w)
    (hw : 2 ≤ w) (hw' : w < 2 ^ 31) (hX8 : 8 ≤ eX) (hM8 : 8 ≤ eM) (hX : eX + 8 * w ≤ Z) (hM : eM + 8 * w ≤ Z) :
    WP isa (.block quot3Load) t fun t' => (t'.gpr .x3 = word t.mem B (eX + 8 * (w - 2)) ∧
      t'.gpr .x4 = (if w = 2 then 0 else word t.mem B (eX + 8 * w - 24)) ∧
      t'.gpr .x15 = word t.mem B (eM + 8 * (w - 2)) ∧ t'.mem = t.mem) ∧
      Keep [.x3, .x4, .x13, .x14, .x15, .x16, .x17] t t' := by
  have hn := hs.nowrap
  have e1 : eX + 8 * w - 24 + 8 = eX + 8 * (w - 2) := by omega_arith
  have e2 : eM + 8 * w - 24 + 8 = eM + 8 * (w - 2) := by omega_arith
  refine WP.keep _ ?_ (by decide) (by decide) (by decide +kernel)
  brun [quot3Load, h11, h9, h12, off_w24 B hX8 hw (show w < 2 ^ 61 by omega_arith),
    off_w24 B hM8 hw (show w < 2 ^ 61 by omega_arith), e1, e2, r2d_exec_tst, r2d_exec_cselc, CondCode.holds,
    w2_test hw (show w < 2 ^ 61 by omega_arith), hs.ld (show eX + 8 * (w - 2) + 8 ≤ Z by omega_arith),
    hs.ld (show eX + 8 * w - 24 + 8 ≤ Z by omega_arith), hs.ld (show eM + 8 * (w - 2) + 8 ≤ Z by omega_arith)]
  by_cases h2 : w = 2
  · subst h2; simp
  · simp [h2]

/-- `quot3`, after `quot` (`q̂₀` in `x1`, `x`'s and `m`'s top words `u₂` and
`d` in `x2` and `x5`), for the top three words `U` of `x 2^64` and the top
two `D` of `m`: `min(⌊U / D⌋, 2^64 - 1)` in `x1`. -/
theorem r2dQuot3Gen_ok {t : State} {B : Addr} {Z w eX eM U D : Nat} (hs : Scr t B Z)
    (h11 : t.gpr .x11 = off B eX) (h9 : t.gpr .x9 = off B eM) (h12 : t.gpr .x12 = BitVec.ofNat 64 w)
    (h7 : t.gpr .x7 = 0) (hw : 2 ≤ w) (hw' : w < 2 ^ 31) (hX8 : 8 ≤ eX) (hM8 : 8 ≤ eM) (hX : eX + 8 * w ≤ Z)
    (hM : eM + 8 * w ≤ Z) {u2 d : BitVec 64}
    (h2 : t.gpr .x2 = u2) (h5 : t.gpr .x5 = d) (hd : 2 ^ 63 ≤ d.toNat)
    (hU : U = u2.toNat * 2 ^ 128 + (word t.mem B (eX + 8 * (w - 2))).toNat * 2 ^ 64 +
      (if w = 2 then 0 else (word t.mem B (eX + 8 * w - 24)).toNat))
    (hD : D = d.toNat * 2 ^ 64 + (word t.mem B (eM + 8 * (w - 2))).toNat)
    (hUD : U < (2 ^ 64 + 1) * D)
    (h1 : t.gpr .x1 = BitVec.ofNat 64 (min ((u2.toNat * 2 ^ 64 + (word t.mem B (eX + 8 * (w - 2))).toNat) / d.toNat)
      (2 ^ 64 - 1)))
    (hle : min (U / D) (2 ^ 64 - 1) ≤ min (U / 2 ^ 64 / (D / 2 ^ 64)) (2 ^ 64 - 1))
    (hge : min (U / 2 ^ 64 / (D / 2 ^ 64)) (2 ^ 64 - 1) ≤ min (U / D) (2 ^ 64 - 1) + 2) :
    WP isa (.block quot3) t fun t' => ((t'.gpr .x1).toNat = min (U / D) (2 ^ 64 - 1) ∧ t'.mem = t.mem) ∧
      Keep [.x1, .x2, .x3, .x4, .x13, .x14, .x15, .x16, .x17] t t' := by
  have l1 := (word t.mem B (eX + 8 * (w - 2))).isLt
  have hU2 : U / 2 ^ 64 = u2.toNat * 2 ^ 64 + (word t.mem B (eX + 8 * (w - 2))).toNat := by
    rw [hU]; split
    · exact div64_3 (by decide)
    · exact div64_3 (BitVec.isLt _)
  have hD2 : D / 2 ^ 64 = d.toNat := by rw [hD]; exact div64_2 (BitVec.isLt _)
  have hD0 : 0 < D := by
    rw [hD]; exact Nat.lt_of_lt_of_le (Nat.mul_pos (by omega_arith) (Nat.two_pow_pos 64)) (Nat.le_add_right _ _)
  rw [hU2, hD2] at hle hge
  unfold quot3
  refine WP.block_append (WP.mono (quot3Load_ok hs h11 h9 h12 hw hw' hX8 hM8 hX hM) fun t₁ ⟨⟨h3, h4, h15, hm₁⟩, k₁⟩ => ?_)
  have q0 : (t₁.gpr .x1).toNat = min ((u2.toNat * 2 ^ 64 + (word t.mem B (eX + 8 * (w - 2))).toNat) / d.toNat)
      (2 ^ 64 - 1) := by
    rw [k₁.gpr .x1 (by decide), h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.min_le_right _ _)
      (by decide))]
  refine WP.mono (quot3Core_ok t₁ ((k₁.gpr .x7 (by decide)).trans h7) (U := U) (D := D) ?_ ?_ hD0 hUD
    (by rw [q0]; exact hle) (by rw [q0]; exact hge)) fun t' ⟨⟨ht1, hm⟩, k⟩ =>
      ⟨⟨ht1, by rw [hm, hm₁]⟩, (k₁.trans k).mono (by decide)⟩
  · have e4 : (t₁.gpr .x4).toNat = if w = 2 then 0 else (word t.mem B (eX + 8 * w - 24)).toNat := by
      rw [h4]; exact apply_ite BitVec.toNat _ _ _
    rw [k₁.gpr .x2 (by decide), h2, h3, e4, hU]
  · rw [k₁.gpr .x5 (by decide), h5, h15, hD]

/-- `quot3`, after `quot`: `q̂ = r2dQ X M w` in `x1`, for `X < M` of `w`
words at `x11` and `x9` and `M`'s top word at least `2^63`. -/
theorem r2dQuot3_ok {t : State} {B : Addr} {Z w eX eM : Nat} (hs : Scr t B Z)
    (h11 : t.gpr .x11 = off B eX) (h9 : t.gpr .x9 = off B eM) (h12 : t.gpr .x12 = BitVec.ofNat 64 w)
    (h7 : t.gpr .x7 = 0) (hw : 2 ≤ w) (hw' : w < 2 ^ 31) (hX8 : 8 ≤ eX) (hM8 : 8 ≤ eM) (hX : eX + 8 * w ≤ Z)
    (hM : eM + 8 * w ≤ Z)
    (h1 : t.gpr .x1 = BitVec.ofNat 64 (min (((word t.mem B (eX + 8 * (w - 1))).toNat * 2 ^ 64 +
        (word t.mem B (eX + 8 * (w - 2))).toNat) / (word t.mem B (eM + 8 * (w - 1))).toNat) (2 ^ 64 - 1)))
    (h2 : t.gpr .x2 = word t.mem B (eX + 8 * (w - 1))) (h5 : t.gpr .x5 = word t.mem B (eM + 8 * (w - 1)))
    (hXM : wv t.mem B eX w < wv t.mem B eM w) (hd : 2 ^ 63 ≤ (word t.mem B (eM + 8 * (w - 1))).toNat) :
    WP isa (.block quot3) t fun t' =>
      ((t'.gpr .x1).toNat = r2dQ (wv t.mem B eX w) (wv t.mem B eM w) w ∧ t'.mem = t.mem) ∧
      Keep [.x1, .x2, .x3, .x4, .x13, .x14, .x15, .x16, .x17] t t' := by
  have hd' : 2 ^ 63 ≤ wv t.mem B eM w / 2 ^ (64 * (w - 1)) := by
    rw [wv_top1 t.mem B eM (by omega_arith)]; exact hd
  obtain ⟨hUD, hle, hge, -, -⟩ := r2dQ_norm hw hXM hd'
  exact r2dQuot3Gen_ok hs h11 h9 h12 h7 hw hw' hX8 hM8 hX hM h2 h5 hd (wv_top3 t.mem B eX hw)
    (wv_top2 t.mem B eM hw) hUD h1 hle hge

/-! ## Adding `m` back -/

/-- What `addBack` does (`r2dAddBack_ok`): `m` (the `w` words at `x9`) added
to the `w + 1` words `t` of `x` (at `x11`) if `t` is negative. -/
def AddBackSpec (ab : Prog isa) : Prop :=
  ∀ {s : State} {B : Addr} {Z w eA eM : Nat}, Scr s B Z → s.gpr .x11 = off B eA → s.gpr .x9 = off B eM →
    s.gpr .x12 = BitVec.ofNat 64 w → s.gpr .x7 = 0 → 1 ≤ w → w < 2 ^ 31 → eA + 8 * (w + 1) ≤ Z →
    eM + 8 * w ≤ Z → (eA + 8 * (w + 1) ≤ eM ∨ eM + 8 * w ≤ eA) →
    WP isa ab s fun t => ∃ c : Bool,
      wv t.mem B eA (w + 1) + 2 ^ (64 * (w + 1)) * c.toNat =
        wv s.mem B eA (w + 1) + (if 2 ^ (64 * (w + 1)) / 2 ≤ wv s.mem B eA (w + 1) then wv s.mem B eM w else 0) ∧
      Outside B eA (8 * (w + 1)) s.mem t.mem ∧ Keep [.x3, .x4, .x13, .x14, .x15, .x16, .x17] s t

theorem addBack_spec : AddBackSpec addBack := r2dAddBack_ok

/-- `signTest`: the sign of `t` into `x3`. -/
theorem signTest_ok {s : State} {B : Addr} {Z w eA : Nat} (hs : Scr s B Z) (h11 : s.gpr .x11 = off B eA)
    (h12 : s.gpr .x12 = BitVec.ofNat 64 w) (hw' : w < 2 ^ 31) (hA : eA + 8 * (w + 1) ≤ Z) :
    WP isa (.block signTest) s fun t =>
      (t.gpr .x3 = BitVec.ofNat 64 (decide (2 ^ 63 ≤ (word s.mem B (eA + 8 * w)).toNat)).toNat ∧ t.mem = s.mem) ∧
        Keep [.x3, .x13] s t := by
  have hn := hs.nowrap
  refine WP.keep [.x3, .x13] (Q := fun t =>
      t.gpr .x3 = BitVec.ofNat 64 (decide (2 ^ 63 ≤ (word s.mem B (eA + 8 * w)).toNat)).toNat ∧ t.mem = s.mem)
    ?_ (by decide) (by decide) (by decide +kernel)
  refine WP.mono (Q := fun (t : State) => t.gpr .x3 = word s.mem B (eA + 8 * w) >>> 63 ∧ t.mem = s.mem) ?_
    fun t ⟨h3, hm⟩ => ⟨by rw [h3, shr63_toNat], hm⟩
  brun [signTest, h11, h12, r2d_ofNat_shl3 (show w < 2 ^ 61 by omega_arith), hs.ld (show eA + 8 * w + 8 ≤ Z by omega_arith)]

/-- `addBackPub` does what `addBack` does: when `t` is not negative, `addBack`
adds nothing, and `addBackPub` skips it. -/
theorem addBackPub_spec : AddBackSpec addBackPub := by
  intro s B Z w eA eM hs h11 h9 h12 h7 hw hw' hA hM sM
  unfold addBackPub
  refine WP.seq (WP.mono (signTest_ok hs h11 h12 hw' hA) fun t₁ ⟨⟨h3, hm₁⟩, k₁⟩ => ?_)
  have hT : (2 ^ (64 * (w + 1)) / 2 ≤ wv s.mem B eA (w + 1)) ↔ 2 ^ 63 ≤ (word s.mem B (eA + 8 * w)).toNat :=
    (decide_eq_decide.mp (sign_top s.mem B eA w)).symm
  by_cases hneg : 2 ^ 63 ≤ (word s.mem B (eA + 8 * w)).toNat
  · refine WP.ite false (by rw [eval_zero, h3, decide_eq_true hneg]; rfl) (by simp) fun _ => ?_
    refine WP.mono (addBack_spec (hs.congr k₁.wr) ((k₁.gpr .x11 (by decide)).trans h11)
      ((k₁.gpr .x9 (by decide)).trans h9) ((k₁.gpr .x12 (by decide)).trans h12)
      ((k₁.gpr .x7 (by decide)).trans h7) hw hw' hA hM sM) fun t ⟨c, hv, o, k⟩ =>
      ⟨c, by rw [hm₁] at hv; exact hv, by rw [← hm₁]; exact o, (k₁.trans k).mono (by decide)⟩
  · refine WP.ite true (by rw [eval_zero, h3, decide_eq_false hneg]; rfl) (fun _ => ?_) (by simp)
    refine WP.block_nil ⟨false, ?_, by rw [hm₁]; exact Outside.refl _ _ _ _, k₁.mono (by decide)⟩
    simp only [hT, hneg, ↓reduceIte, hm₁, Bool.toNat_false, Nat.mul_zero, Nat.add_zero]

/-! ## A step -/

/-- A step's first pieces: `t = x 2^64 - q̂ m` in place of `x`, its `w + 1`
words, with a borrow `b`, for `q̂ = r2dQ X M w`. -/
theorem r2dStepPre_ok {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {M D : Nat} (hg : Good t B Z w minv)
    (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31) (hM : wv t.mem B (slot w aN) w = M)
    (hD : (word t.mem B (slot w aN + 8 * (w - 1))).toNat = D) (hd : 2 ^ 63 ≤ D)
    (hv : (word t.mem B (slot w aTmp)).toNat = (2 ^ 128 - 1) / D - 2 ^ 64)
    (hX : wv t.mem B (slot w aR2) w < M) :
    WP isa (seqs [.block (R2Div.bases ++ quot), .block quot3, mulSub]) t fun t₃ =>
      Good t₃ B Z w minv ∧ StepRegs t₃ B w ∧ wv t₃.mem B (slot w aN) w = M ∧
      (∃ b : Bool, wv t₃.mem B (slot w aR2) (w + 1) + r2dQ (wv t.mem B (slot w aR2) w) M w * M =
        2 ^ 64 * wv t.mem B (slot w aR2) w + 2 ^ (64 * (w + 1)) * b.toNat) ∧
      Arrays B w [aR2] t.mem t₃.mem ∧ Keep mmRegs t t₃ := by
  have hs := hg.scr
  have hn := hs.nowrap
  have sl : ∀ j < 8, slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_le hj) hZ
  have lM := sl aN (by decide)
  have lX := sl aR2 (by decide)
  have sXM := slot_sep (w := w) (show aR2 ≠ aN by decide)
  have h8X : 8 ≤ slot w aR2 := by have := hdr_lt_slot w aR2 (show 0 < 32 by decide); omega_arith
  have h8M : 8 ≤ slot w aN := by have := hdr_lt_slot w aN (show 0 < 32 by decide); omega_arith
  have hu := r2d_top_le (m := t.mem) (B := B) (by omega_arith : 1 ≤ w) (hM ▸ hX)
  simp only [seqs]
  refine WP.seq (WP.mono (r2dHead_ok hg hZ hw hw' hu (by rw [hD]; exact hd) (by rw [hv, hD]))
    fun t₁ ⟨r₁, h1, h2, h5, hm₁, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.wr
  rw [← hm₁] at h1 h2 h5
  refine WP.seq (WP.mono (r2dQuot3_ok hs₁ r₁.x11 r₁.x9 r₁.x12 r₁.x7 hw hw' h8X h8M (by omega_arith) (by omega_arith)
    h1 h2 h5 (by rw [hm₁, hM]; exact hX) (by rw [hm₁, hD]; exact hd)) fun t₂ ⟨⟨hq₂, hm₂⟩, k₂⟩ => ?_)
  rw [hm₁, hM] at hq₂
  have r₂ := r₁.keep k₂
  have hs₂ := hs₁.congr k₂.wr
  generalize hXv : wv t.mem B (slot w aR2) w = X at hX hq₂ ⊢
  generalize hQ : r2dQ X M w = q at hq₂ ⊢
  have hqB : q < 2 ^ 64 := by rw [← hQ]; exact Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by decide)
  refine WP.mono (mulSub_ok hs₂ r₂.x11 r₂.x9 r₂.x12 r₂.x7 (by rw [← hq₂, BitVec.ofNat_toNat, BitVec.setWidth_eq]) hqB
    (by omega_arith) hw' (by omega_arith) (by omega_arith) (by omega_arith)) fun t₃ ⟨b, hv₃, o₃, k₃⟩ => ?_
  rw [hm₂, hm₁, hM, hXv] at hv₃
  have kk : Keep mmRegs t t₃ := ((k₁.trans k₂).trans k₃).mono (by decide)
  have ha : Arrays B w [aR2] t.mem t₃.mem := by
    rw [← hm₁, ← hm₂]
    exact Arrays.of_outside (List.mem_singleton_self _) o₃ (Nat.le_refl _) (by omega_arith)
  exact ⟨⟨hs₂.congr k₃.wr, (kk.gpr .x0 (by decide)).trans hg.x0, ha.hdr hg.hdr⟩, r₂.keep k₃,
    by rw [o₃.wv (by omega_arith) (by omega_arith), hm₂, hm₁, hM], ⟨b, hv₃⟩, ha, kk⟩

/-- The end of a step: `m` added back to `t = x 2^64 - q̂ m` by `ab`, which
does what `addBack` does, for `q ≤ q̂ ≤ q + 1` (`WordStep.wordStepQ1_val`):
`x 2^64 mod m` in `x`. -/
theorem r2dStepFin_ok {ab : Prog isa} (hab : AddBackSpec ab) {t : State} {B : Addr} {Z w : Nat}
    {minv : BitVec 64} {M X q : Nat} (hg : Good t B Z w minv) (r : StepRegs t B w)
    (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hM : wv t.mem B (slot w aN) w = M) (hXM : X < M)
    (hge : X * 2 ^ 64 / M ≤ q) (hle : q ≤ X * 2 ^ 64 / M + 1)
    (hT : ∃ b : Bool, wv t.mem B (slot w aR2) (w + 1) + q * M = 2 ^ 64 * X + 2 ^ (64 * (w + 1)) * b.toNat) :
    WP isa ab t fun t' => Good t' B Z w minv ∧ wv t'.mem B (slot w aR2) w = X * 2 ^ 64 % M ∧
      Arrays B w [aR2] t.mem t'.mem ∧ Keep [.x3, .x4, .x13, .x14, .x15, .x16, .x17] t t' := by
  have hs := hg.scr
  have hn := hs.nowrap
  have sl : ∀ j < 8, slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_le hj) hZ
  have lM := sl aN (by decide)
  have lX := sl aR2 (by decide)
  have sXM := slot_sep (w := w) (show aR2 ≠ aN by decide)
  have hMB : M < 2 ^ (64 * w) := hM ▸ wv_lt _ _ _ _
  obtain ⟨b, hT⟩ := hT
  refine WP.mono (hab hs r.x11 r.x9 r.x12 r.x7 hw hw' (by omega_arith) (by omega_arith) (by omega_arith))
    fun t' ⟨c, hv, o, k⟩ => ?_
  rw [hM] at hv
  have hW : 2 * M < 2 ^ (64 * (w + 1)) / 2 := by
    rw [pow64_succ, show (2 : Nat) ^ 64 = 2 * 2 ^ 63 from rfl, ← Nat.mul_assoc, Nat.mul_comm _ 2, Nat.mul_assoc,
      Nat.mul_div_cancel_left _ (by decide)]
    have : 2 ^ (64 * w) ≤ 2 ^ (64 * w) * 2 ^ 62 := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
    rw [show (2 : Nat) ^ 63 = 2 * 2 ^ 62 from rfl]
    omega_arith
  have hT2 : wv t'.mem B (slot w aR2) (w + 1) = X * 2 ^ 64 % M :=
    WordStep.wordStepQ1_val (W := 2 ^ (64 * (w + 1))) (by omega_arith) hW hge hle (wv_lt _ _ _ _) (Bool.toNat_lt b)
      (by rw [Nat.mul_comm X]; exact hT) (wv_lt _ _ _ _) (Bool.toNat_lt c) hv
  have hMod : X * 2 ^ 64 % M < 2 ^ (64 * w) := Nat.lt_trans (Nat.mod_lt _ (by omega_arith)) hMB
  have ha : Arrays B w [aR2] t.mem t'.mem :=
    Arrays.of_outside (List.mem_singleton_self _) o (Nat.le_refl _) (by omega_arith)
  refine ⟨⟨hs.congr k.wr, (k.gpr .x0 (by decide)).trans hg.x0, ha.hdr hg.hdr⟩, ?_, ha, k⟩
  rw [wv_low_top t'.mem B (slot w aR2) w (by rw [hT2]; exact hMod), hT2]

/-- `x := x 2^64 mod m` by a step whose `ab` does what `addBack` does: `x < m`
(array `aR2`) for `m` (array `aN`) of `w ≥ 2` words, its top word
`D ≥ 2^63`, and `v` for `D` in the first word of `aTmp`. -/
theorem r2dStepWith_ok {ab : Prog isa} (hab : AddBackSpec ab) {t : State} {B : Addr} {Z w : Nat}
    {minv : BitVec 64} {M D : Nat} (hg : Good t B Z w minv)
    (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31) (hM : wv t.mem B (slot w aN) w = M)
    (hD : (word t.mem B (slot w aN + 8 * (w - 1))).toNat = D) (hd : 2 ^ 63 ≤ D)
    (hv : (word t.mem B (slot w aTmp)).toNat = (2 ^ 128 - 1) / D - 2 ^ 64)
    (hX : wv t.mem B (slot w aR2) w < M) :
    WP isa (seqs [.block (R2Div.bases ++ quot), .block quot3, mulSub, ab]) t fun t' =>
      Good t' B Z w minv ∧
      wv t'.mem B (slot w aR2) w = wv t.mem B (slot w aR2) w * 2 ^ 64 % M ∧
      Arrays B w [aAcc, aR2] t.mem t'.mem ∧ Keep mmRegs t t' := by
  have hd' : 2 ^ 63 ≤ M / 2 ^ (64 * (w - 1)) := by
    rw [← hM, wv_top1 t.mem B _ (by omega_arith), hD]; exact hd
  obtain ⟨-, -, -, hge, hle⟩ := r2dQ_norm hw hX hd'
  refine wp_seqs_append (a := [.block (R2Div.bases ++ quot), .block quot3, mulSub]) (b := [ab]) (by simp) (by simp)
    (WP.mono (r2dStepPre_ok hg hZ hw hw' hM hD hd hv hX) fun t₃ ⟨g₃, r₃, M₃, hT, a₃, k₃⟩ => ?_)
  refine WP.mono (r2dStepFin_ok hab g₃ r₃ hZ (by omega_arith) hw' M₃ hX hge hle hT) fun t' ⟨g', hx, a', k'⟩ =>
    ⟨g', hx, (a₃.trans a').mono (fun j hj => by simp only [List.mem_singleton] at hj; subst hj; decide),
      (k₃.trans k').mono (by decide)⟩

/-- `step`: `x := x 2^64 mod m` (`r2dStepWith_ok`). -/
theorem r2dStep_ok {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {M D : Nat} (hg : Good t B Z w minv)
    (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31) (hM : wv t.mem B (slot w aN) w = M)
    (hD : (word t.mem B (slot w aN + 8 * (w - 1))).toNat = D) (hd : 2 ^ 63 ≤ D)
    (hv : (word t.mem B (slot w aTmp)).toNat = (2 ^ 128 - 1) / D - 2 ^ 64)
    (hX : wv t.mem B (slot w aR2) w < M) :
    WP isa step t fun t' => Good t' B Z w minv ∧
      wv t'.mem B (slot w aR2) w = wv t.mem B (slot w aR2) w * 2 ^ 64 % M ∧
      Arrays B w [aAcc, aR2] t.mem t'.mem ∧ Keep mmRegs t t' :=
  r2dStepWith_ok addBack_spec hg hZ hw hw' hM hD hd hv hX

/-- `stepPub`: `x := x 2^64 mod m` (`r2dStepWith_ok`). -/
theorem r2dStepPub_ok {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {M D : Nat} (hg : Good t B Z w minv)
    (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31) (hM : wv t.mem B (slot w aN) w = M)
    (hD : (word t.mem B (slot w aN + 8 * (w - 1))).toNat = D) (hd : 2 ^ 63 ≤ D)
    (hv : (word t.mem B (slot w aTmp)).toNat = (2 ^ 128 - 1) / D - 2 ^ 64)
    (hX : wv t.mem B (slot w aR2) w < M) :
    WP isa stepPub t fun t' => Good t' B Z w minv ∧
      wv t'.mem B (slot w aR2) w = wv t.mem B (slot w aR2) w * 2 ^ 64 % M ∧
      Arrays B w [aAcc, aR2] t.mem t'.mem ∧ Keep mmRegs t t' :=
  r2dStepWith_ok addBackPub_spec hg hZ hw hw' hM hD hd hv hX

end VG.Proof.Bignum.AArch64
