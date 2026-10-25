module
public import VerifiedGarbage.Impl.Bignum.AArch64.R2Div
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import VerifiedGarbage.Proof.Bignum.WordStep
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
word of array `aTmp` (`r2dStep_ok`), by `WordStep.wordStep_val`; and so
does `stepPub`, whose `addBackPub` branches on the sign that `addBack` masks
by (`r2dStepPub_ok`): both are `r2dStepWith_ok` for a program that does what
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
  rw [← hm₁] at hu hd hv
  refine WP.mono (r2dQuot_ok hs₁ hr.x11 hr.x9 hr.x12 hr.x6 hr.x7 hw hw' (by have := sl aR2 (by decide); omega_arith)
    (by have := sl aN (by decide); omega_arith) (by have := sl aTmp (by decide); omega_arith) hu hd hv)
    fun t' ⟨h1, hm, k⟩ => ⟨hr.keep k, by rw [h1, hm₁], by rw [hm, hm₁], (k₁.trans k).mono (by decide)⟩

/-! ## Adding `m` back -/

/-- What `addBack` does (`r2dAddBack_ok`): `m` (the `w` words at `x9`) added
to the `w + 1` words `t` of the accumulator (at `x8`) if `t` is negative. -/
def AddBackSpec (ab : Prog isa) : Prop :=
  ∀ {s : State} {B : Addr} {Z w eA eM : Nat}, Scr s B Z → s.gpr .x8 = off B eA → s.gpr .x9 = off B eM →
    s.gpr .x12 = BitVec.ofNat 64 w → s.gpr .x7 = 0 → 1 ≤ w → w < 2 ^ 31 → eA + 8 * (w + 1) ≤ Z →
    eM + 8 * w ≤ Z → (eA + 8 * (w + 1) ≤ eM ∨ eM + 8 * w ≤ eA) →
    WP isa ab s fun t => ∃ c : Bool,
      wv t.mem B eA (w + 1) + 2 ^ (64 * (w + 1)) * c.toNat =
        wv s.mem B eA (w + 1) + (if 2 ^ (64 * (w + 1)) / 2 ≤ wv s.mem B eA (w + 1) then wv s.mem B eM w else 0) ∧
      Outside B eA (8 * (w + 1)) s.mem t.mem ∧ Keep [.x3, .x4, .x13, .x14, .x15, .x16, .x17] s t

theorem addBack_spec : AddBackSpec addBack := r2dAddBack_ok

/-- `signTest`: the sign of `t` into `x3`. -/
theorem signTest_ok {s : State} {B : Addr} {Z w eA : Nat} (hs : Scr s B Z) (h8 : s.gpr .x8 = off B eA)
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
  brun [signTest, h8, h12, r2d_ofNat_shl3 (show w < 2 ^ 61 by omega_arith), hs.ld (show eA + 8 * w + 8 ≤ Z by omega_arith)]

/-- `addBackPub` does what `addBack` does: when `t` is not negative, `addBack`
adds nothing, and `addBackPub` skips it. -/
theorem addBackPub_spec : AddBackSpec addBackPub := by
  intro s B Z w eA eM hs h8 h9 h12 h7 hw hw' hA hM sM
  unfold addBackPub
  refine WP.seq (WP.mono (signTest_ok hs h8 h12 hw' hA) fun t₁ ⟨⟨h3, hm₁⟩, k₁⟩ => ?_)
  have hT : (2 ^ (64 * (w + 1)) / 2 ≤ wv s.mem B eA (w + 1)) ↔ 2 ^ 63 ≤ (word s.mem B (eA + 8 * w)).toNat :=
    (decide_eq_decide.mp (sign_top s.mem B eA w)).symm
  by_cases hneg : 2 ^ 63 ≤ (word s.mem B (eA + 8 * w)).toNat
  · refine WP.ite false (by rw [eval_zero, h3, decide_eq_true hneg]; rfl) (by simp) fun _ => ?_
    refine WP.mono (addBack_spec (hs.congr k₁.wr) ((k₁.gpr .x8 (by decide)).trans h8)
      ((k₁.gpr .x9 (by decide)).trans h9) ((k₁.gpr .x12 (by decide)).trans h12)
      ((k₁.gpr .x7 (by decide)).trans h7) hw hw' hA hM sM) fun t ⟨c, hv, o, k⟩ =>
      ⟨c, by rw [hm₁] at hv; exact hv, by rw [← hm₁]; exact o, (k₁.trans k).mono (by decide)⟩
  · refine WP.ite true (by rw [eval_zero, h3, decide_eq_false hneg]; rfl) (fun _ => ?_) (by simp)
    refine WP.block_nil ⟨false, ?_, by rw [hm₁]; exact Outside.refl _ _ _ _, k₁.mono (by decide)⟩
    simp only [hT, hneg, ↓reduceIte, hm₁, Bool.toNat_false, Nat.mul_zero, Nat.add_zero]

/-! ## A step -/

/-- The estimate `q̂` of a step's quotient: `x`'s top two words by `m`'s top
word `D`. -/
def r2dQ (m : Mem) (B : Addr) (w D : Nat) : Nat :=
  min (((word m B (slot w aR2 + 8 * (w - 1))).toNat * 2 ^ 64 + (word m B (slot w aR2 + 8 * (w - 2))).toNat) / D)
    (2 ^ 64 - 1)

/-- A step's first pieces: `t = x 2^64 - q̂ m` in the accumulator's `w + 1`
words, with a borrow `b` out of them. -/
theorem r2dStepPre_ok {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {M D : Nat} (hg : Good t B Z w minv)
    (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31) (hM : wv t.mem B (slot w aN) w = M)
    (hD : (word t.mem B (slot w aN + 8 * (w - 1))).toNat = D) (hd : 2 ^ 63 ≤ D)
    (hv : (word t.mem B (slot w aTmp)).toNat = (2 ^ 128 - 1) / D - 2 ^ 64)
    (hX : wv t.mem B (slot w aR2) w < M) :
    WP isa (seqs [.block (R2Div.bases ++ quot), zeroAcc, mulAddRow, subPass]) t fun t₄ =>
      Good t₄ B Z w minv ∧ StepRegs t₄ B w ∧ wv t₄.mem B (slot w aN) w = M ∧
      (∃ b : Bool, wv t₄.mem B (slot w aAcc) (w + 1) + r2dQ t.mem B w D * M =
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
  have hu := r2d_top_le (m := t.mem) (B := B) (by omega_arith : 1 ≤ w) (hM ▸ hX)
  simp only [seqs]
  refine WP.seq (WP.mono (r2dHead_ok hg hZ hw hw' hu (by rw [hD]; exact hd) (by rw [hv, hD]))
    fun t₁ ⟨r₁, h1, hm₁, k₁⟩ => ?_)
  rw [hD] at h1
  have hq : r2dQ t.mem B w D = min (((word t.mem B (slot w aR2 + 8 * (w - 1))).toNat * 2 ^ 64 +
    (word t.mem B (slot w aR2 + 8 * (w - 2))).toNat) / D) (2 ^ 64 - 1) := rfl
  rw [← hq] at h1
  generalize r2dQ t.mem B w D = q at h1 hq ⊢
  have hqB : q < 2 ^ 64 := by rw [hq]; exact Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by decide)
  have hs₁ := hs.congr k₁.wr
  generalize hXv : wv t.mem B (slot w aR2) w = X at hX ⊢
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

/-- `x := x 2^64 mod m` by a step whose `ab` does what `addBack` does: `x < m`
(array `aR2`) for `m` (array `aN`) of `w ≥ 2` words, its top word
`D ≥ 2^63`, and `v` for `D` in the first word of `aTmp`. -/
theorem r2dStepWith_ok {ab : Prog isa} (hab : AddBackSpec ab) {t : State} {B : Addr} {Z w : Nat}
    {minv : BitVec 64} {M D : Nat} (hg : Good t B Z w minv)
    (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31) (hM : wv t.mem B (slot w aN) w = M)
    (hD : (word t.mem B (slot w aN + 8 * (w - 1))).toNat = D) (hd : 2 ^ 63 ≤ D)
    (hv : (word t.mem B (slot w aTmp)).toNat = (2 ^ 128 - 1) / D - 2 ^ 64)
    (hX : wv t.mem B (slot w aR2) w < M) :
    WP isa (seqs [.block (R2Div.bases ++ quot), zeroAcc, mulAddRow, subPass, ab, ab, copyBack]) t fun t' =>
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
  have hXw := wv_split2 t.mem B (slot w aR2) hw
  have hMw := wv_split1 t.mem B (slot w aN) (show 1 ≤ w by omega_arith)
  have hXl := wv_lt t.mem B (slot w aR2) (w - 2)
  have hml := wv_lt t.mem B (slot w aN) (w - 1)
  rw [hM, hD] at hMw
  have hMB : M < 2 ^ (64 * w) := hM ▸ wv_lt _ _ _ _
  refine wp_seqs_append (a := [.block (R2Div.bases ++ quot), zeroAcc, mulAddRow, subPass])
    (b := [ab, ab, copyBack]) (by simp) (by simp)
    (WP.mono (r2dStepPre_ok hg hZ hw hw' hM hD hd hv hX) fun t₄ ⟨g₄, r₄, M₄, ⟨b, hv₄⟩, a₄, k₄⟩ => ?_)
  have hs₄ := g₄.scr
  have hq : r2dQ t.mem B w D = min (((word t.mem B (slot w aR2 + 8 * (w - 1))).toNat * 2 ^ 64 +
    (word t.mem B (slot w aR2 + 8 * (w - 2))).toNat) / D) (2 ^ 64 - 1) := rfl
  generalize r2dQ t.mem B w D = q at hv₄ hq
  generalize hXv : wv t.mem B (slot w aR2) w = X at hX hXw hv₄ ⊢
  simp only [seqs]
  -- `m` added back while `t` is negative.
  refine WP.seq (WP.mono (hab hs₄ r₄.x8 r₄.x9 r₄.x12 r₄.x7 (by omega_arith) hw' (by omega_arith) (by omega_arith)
    (by omega_arith)) fun t₅ ⟨c1, hv₅, o₅, k₅⟩ => ?_)
  rw [M₄] at hv₅
  have r₅ := r₄.keep k₅
  have hs₅ := hs₄.congr k₅.wr
  have M₅ : wv t₅.mem B (slot w aN) w = M := by rw [o₅.wv (by omega_arith) (by omega_arith), M₄]
  refine WP.seq (WP.mono (hab hs₅ r₅.x8 r₅.x9 r₅.x12 r₅.x7 (by omega_arith) hw' (by omega_arith) (by omega_arith)
    (by omega_arith)) fun t₆ ⟨c2, hv₆, o₆, k₆⟩ => ?_)
  rw [M₅] at hv₆
  have r₆ := r₅.keep k₆
  have hs₆ := hs₅.congr k₆.wr
  -- The value.
  have hT3 : wv t₆.mem B (slot w aAcc) (w + 1) = X * 2 ^ 64 % M := by
    refine WordStep.wordStep_val hw hXw hXl hMw hml hd (hD ▸ BitVec.isLt _) hX (wv_lt _ _ _ _) (Bool.toNat_lt b)
      ?_ (wv_lt _ _ _ _) (Bool.toNat_lt c1) hv₅ (wv_lt _ _ _ _) (Bool.toNat_lt c2) hv₆
    rw [← hq]; omega_arith
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
