module
public import VerifiedGarbage.Impl.Bignum.AArch64.R2Div
public import VerifiedGarbage.Proof.Bignum.AArch64.Run

import VerifiedGarbage.Proof.Bignum.AArch64.R2dSub
import VerifiedGarbage.Proof.Bignum.AArch64.Csub
import VerifiedGarbage.Proof.Bignum.WordStepNorm
import VerifiedGarbage.Proof.Bignum.WordStep
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# `R² mod m` by long division on AArch64: the estimate of the quotient

`quotMG` computes `mgq v u a d`, which for `u < d`, `d ≥ 2^63` and the
reciprocal `v = ⌊(2^128 - 1) / d⌋ - 2^64` is `⌊(u 2^64 + a) / d⌋` (`mgq_val`,
Möller and Granlund's division, `mg_quot`); `quot` loads `d`, `u₂` and `u₁`
and takes all ones for `u₂ = d` (`r2dQuot_ok`): `q̂`.
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Impl.Bignum.AArch64.R2Div VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

/-- What `quotMG` computes from `v` (`[x6]`), `u` (`x2`), `a` (`x3`) and `d`
(`x5`), instruction by instruction. -/
def mgq (v u a d : BitVec 64) : BitVec 64 :=
  let c := decide (2 ^ 64 ≤ (v * u).toNat + a.toNat + (false : Bool).toNat)
  let q0 := v * u + a + BitVec.ofNat 64 (false : Bool).toNat
  let Q := BitVec.ofNat 64 (v.toNat * u.toNat / 2 ^ 64) + u + BitVec.ofNat 64 (c.toNat + 1)
  let r := a - Q * d
  let lt := !decide (2 ^ 64 ≤ q0.toNat + (~~~r).toNat + (true : Bool).toNat)
  let Q1 := if lt then Q - BitVec.ofNat 64 1 else Q
  let r1 := if lt then r + d else r
  Q1 + 0 + BitVec.ofNat 64 (decide (2 ^ 64 ≤ r1.toNat + (~~~d).toNat + (true : Bool).toNat)).toNat

theorem r2d_add_zero (x : BitVec 64) : x + BitVec.ofNat 64 0 = x := BitVec.add_zero x

theorem r2d_add_succ (x : BitVec 64) (c : Nat) :
    x + BitVec.ofNat 64 (c + 1) = x + BitVec.ofNat 64 c + BitVec.ofNat 64 1 := by
  rw [BitVec.ofNat_add, BitVec.add_assoc]

theorem r2d_ofNat_bool (c : Bool) : BitVec.ofNat 64 c.toNat = (BitVec.ofBool c).setWidth 64 := by
  cases c <;> rfl

/-- The complement's carry: `x + ~y + 1 ≥ 2^64` iff `y ≤ x`. -/
theorem not_carry (x y : BitVec 64) :
    decide (2 ^ 64 ≤ x.toNat + (~~~y).toNat + (true : Bool).toNat) = decide (y.toNat ≤ x.toNat) := by
  rw [BitVec.toNat_not]
  have := y.isLt
  apply decide_eq_decide.mpr
  simp only [Bool.toNat_true]
  omega_arith

theorem mgq_val {v u a d : Nat} (hd : d < 2 ^ 64) (hn : 2 ^ 63 ≤ d) (hu : u < d) (ha : a < 2 ^ 64)
    (hv : v = (2 ^ 128 - 1) / d - 2 ^ 64) :
    (mgq (BitVec.ofNat 64 v) (BitVec.ofNat 64 u) (BitVec.ofNat 64 a) (BitVec.ofNat 64 d)).toNat =
      (u * 2 ^ 64 + a) / d := by
  have hd0 : 0 < d := by omega_using [hu]
  have hVd : (2 ^ 128 - 1) / d * d ≤ 2 ^ 128 - 1 := Nat.div_mul_le_self _ _
  have hVB : 2 ^ 64 ≤ (2 ^ 128 - 1) / d := by
    rw [Nat.le_div_iff_mul_le hd0]
    have := Nat.mul_le_mul_left (2 ^ 64) (show d ≤ 2 ^ 64 - 1 by omega_using [hd])
    omega_using [this]
  generalize hV : (2 ^ 128 - 1) / d = V at hVd hVB hv
  have hVu : V * u + V ≤ V * d := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hu
  have hPe : v * u + a + 2 ^ 64 * u = V * u + a := by
    rw [hv, Nat.sub_mul]; have := Nat.mul_le_mul_right u hVB; omega_using [this]
  have hVd' : V * d = d * V := Nat.mul_comm _ _
  have hPB : V * u + a < 2 ^ 128 := by omega_using [ha, hVd, hVB, hVu, hVd']
  have hvl : v < 2 ^ 64 := by
    rw [hv]
    have : V < 2 ^ 65 := by
      rw [← hV, Nat.div_lt_iff_lt_mul hd0]
      have := Nat.mul_le_mul_left (2 ^ 65) hn
      omega_using [this]
    omega_using [this]
  have hul : u < 2 ^ 64 := by omega_using [hu, hd]
  have hU : (BitVec.ofNat 64 u).toNat = u := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hul]
  have hA : (BitVec.ofNat 64 a).toNat = a := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]
  have hD : (BitVec.ofNat 64 d).toNat = d := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd]
  have hVv : (BitVec.ofNat 64 v).toNat = v := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hvl]
  unfold mgq
  simp only [Bool.toNat_false, Nat.add_zero, r2d_add_zero, r2d_add_succ]
  rw [hVv, hU, r2d_ofNat_bool]
  -- `(q₁, q₀) = V u + a`.
  have hl : v * u ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega_using [hvl]) (by omega_using [hul])
  have e := VG.Proof.Poly1305.Limbs64.add_adc_toNat (BitVec.ofNat 64 v * BitVec.ofNat 64 u) (BitVec.ofNat 64 a)
    (BitVec.ofNat 64 (v * u / 2 ^ 64)) (BitVec.ofNat 64 u) (by
      simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hvl, Nat.mod_eq_of_lt hul,
        Nat.mod_eq_of_lt ha]
      omega_using [hPe, hPB, hl])
  have emul : (BitVec.ofNat 64 v * BitVec.ofNat 64 u).toNat = v * u % 2 ^ 64 := by
    rw [BitVec.toNat_mul, hVv, hU]
  rw [emul, hA, BitVec.toNat_ofNat, hU, Nat.mod_eq_of_lt (show v * u / 2 ^ 64 < 2 ^ 64 by omega_using [hl])] at e
  generalize hq0 : BitVec.ofNat 64 v * BitVec.ofNat 64 u + BitVec.ofNat 64 a = q0 at e ⊢
  generalize hq1 : BitVec.ofNat 64 (v * u / 2 ^ 64) + BitVec.ofNat 64 u +
    (BitVec.ofBool (decide (2 ^ 64 ≤ v * u % 2 ^ 64 + a))).setWidth 64 = q1 at e ⊢
  rw [emul, hA]
  rw [hq1]
  have hq0v : q0.toNat = (V * u + a) % 2 ^ 64 := by
    have := q0.isLt; have := q1.isLt; omega_using [e, hPe]
  have hq1v : q1.toNat = (V * u + a) / 2 ^ 64 := by
    have := q0.isLt; have := q1.isLt; omega_using [e, hPe]
  -- The candidate and its remainder.
  rw [BitVec.add_zero q1]
  generalize hQ : q1 + BitVec.ofNat 64 1 = Q
  have hQv : Q.toNat = ((V * u + a) / 2 ^ 64 + 1) % 2 ^ 64 := by
    rw [← hQ, BitVec.toNat_add, hq1v, BitVec.toNat_ofNat]
  generalize hr : BitVec.ofNat 64 a - Q * BitVec.ofNat 64 d = r
  have hrv : r.toNat = (a + (2 ^ 64 - Q.toNat * d % 2 ^ 64)) % 2 ^ 64 := by
    rw [← hr, BitVec.toNat_sub, BitVec.toNat_mul, hA, hD]
    have := Q.isLt
    have : Q.toNat * d % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by decide)
    rw [Nat.add_comm]
  have hnd : (!decide (r.toNat ≤ q0.toNat)) = decide ((V * u + a) % 2 ^ 64 < r.toNat) := by
    rw [hq0v]; cases h : decide ((V * u + a) % 2 ^ 64 < r.toNat) <;> simp_all <;> omega_using [h]
  rw [not_carry, hnd, not_carry]
  -- The two corrections.
  have hQ1 : ∀ c : Bool, (if c then Q - BitVec.ofNat 64 1 else Q).toNat =
      (Q.toNat + if c then 2 ^ 64 - 1 else 0) % 2 ^ 64 := by
    intro c; have := Q.isLt
    cases c
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Nat.mod_eq_of_lt this]
    · simp only [↓reduceIte, BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega_using []
  have hr1 : ∀ c : Bool, (if c then r + BitVec.ofNat 64 d else r).toNat = (r.toNat + if c then d else 0) % 2 ^ 64 := by
    intro c; have := r.isLt
    cases c
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Nat.mod_eq_of_lt this]
    · simp only [↓reduceIte, BitVec.toNat_add, hD]
  generalize hc : decide ((V * u + a) % 2 ^ 64 < r.toNat) = c
  generalize hQ1v : (if c = true then Q - BitVec.ofNat 64 1 else Q) = Q1
  generalize hr1v : (if c = true then r + BitVec.ofNat 64 d else r) = r1
  have eQ1 := hQ1 c; rw [hQ1v] at eQ1
  have er1 := hr1 c; rw [hr1v] at er1
  have hfin := WordStep.mg_quot hd hn hu ha hV.symm rfl hQv hrv (Q1 := Q1.toNat) (r1 := r1.toNat)
    (by rw [eQ1, ← hc]; simp only [decide_eq_true_eq]) (by rw [er1, ← hc]; simp only [decide_eq_true_eq])
  rw [← hfin, BitVec.toNat_add, BitVec.toNat_add, hD, show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero,
    BitVec.toNat_ofNat]
  have := Q1.isLt
  by_cases h : d ≤ r1.toNat
  · simp only [h, decide_true, Bool.toNat_true, show d - 1 < r1.toNat by omega_using [h, hd0], ↓reduceIte]
    omega_using []
  · simp only [h, decide_false, Bool.toNat_false, show ¬ d - 1 < r1.toNat by omega_using [h, hd0], ↓reduceIte]
    omega_using []

theorem shr63_toNat (r : BitVec 64) : (r >>> 63) = BitVec.ofNat 64 (decide (2 ^ 63 ≤ r.toNat)).toNat := by
  have := r.isLt
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  by_cases h : 2 ^ 63 ≤ r.toNat <;> simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;>
    omega_using [h]

/-! ## `quot` -/

theorem r2d_exec_tst (s : State) (n m : Reg) :
    exec (.tst .x n m) s = some { s with
      nf := (s.gpr n &&& s.gpr m).msb
      zf := decide ((s.gpr n &&& s.gpr m) = 0)
      c := false
      vf := false } := rfl

theorem r2d_exec_cselc (s : State) {d n m : Reg} {cond : CondCode} :
    exec (.cselc .x d n m cond) s = some (s.write .x d (if cond.holds s then s.gpr n else s.gpr m)) := rfl

/-- `8 (w - 1)`, as `quotHead` computes it. -/
theorem shl3_sub8 {w : Nat} (hw : 1 ≤ w) (hw' : w < 2 ^ 61) :
    BitVec.ofNat 64 w <<< 3 - BitVec.ofNat 64 8 = BitVec.ofNat 64 (8 * (w - 1)) := by
  rw [r2d_ofNat_shl3 hw']
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega_arith

theorem off_sub8 (B : Addr) {e : Nat} (he : 8 ≤ e) : off B e - BitVec.ofNat 64 8 = off B (e - 8) := by
  rw [show off B e = off B (e - 8) + BitVec.ofNat 64 8 by
    rw [off_add, Nat.sub_add_cancel he], BitVec.add_sub_cancel]

/-- The estimate of the quotient of `x 2^64` by `m`:
`q̂ = min(⌊(u₂ 2^64 + u₁) / d⌋, 2^64 - 1)` into `x1`, for `x` at `x11` and `m`
at `x9` of `w` words, `u₂ ≤ d`, `d ≥ 2^63`, and `v` at `x6`. -/
theorem r2dQuot_ok {t : State} {B : Addr} {Z w eX eM eV : Nat} (hs : Scr t B Z)
    (h11 : t.gpr .x11 = off B eX) (h9 : t.gpr .x9 = off B eM) (h12 : t.gpr .x12 = BitVec.ofNat 64 w)
    (h6 : t.gpr .x6 = off B eV) (h7 : t.gpr .x7 = 0) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hX : eX + 8 * w ≤ Z) (hM : eM + 8 * w ≤ Z) (hE : eV + 8 ≤ Z)
    (hu : (word t.mem B (eX + 8 * (w - 1))).toNat ≤ (word t.mem B (eM + 8 * (w - 1))).toNat)
    (hd : 2 ^ 63 ≤ (word t.mem B (eM + 8 * (w - 1))).toNat)
    (hv : (word t.mem B eV).toNat = (2 ^ 128 - 1) / (word t.mem B (eM + 8 * (w - 1))).toNat - 2 ^ 64) :
    WP isa (.block quot) t fun t' =>
      t'.gpr .x1 = BitVec.ofNat 64 (min (((word t.mem B (eX + 8 * (w - 1))).toNat * 2 ^ 64 +
        (word t.mem B (eX + 8 * (w - 2))).toNat) / (word t.mem B (eM + 8 * (w - 1))).toNat) (2 ^ 64 - 1)) ∧
      t'.gpr .x2 = word t.mem B (eX + 8 * (w - 1)) ∧ t'.gpr .x5 = word t.mem B (eM + 8 * (w - 1)) ∧
      t'.mem = t.mem ∧ Keep [.x1, .x2, .x3, .x4, .x5, .x13, .x14, .x15, .x16, .x17] t t' := by
  have hn := hs.nowrap
  have e1 : eX + 8 * (w - 1) - 8 = eX + 8 * (w - 2) := by omega_arith
  generalize hD : word t.mem B (eM + 8 * (w - 1)) = D at hu hd hv
  generalize hU2 : word t.mem B (eX + 8 * (w - 1)) = U2 at hu
  generalize hU1 : word t.mem B (eX + 8 * (w - 2)) = U1
  generalize hVw : word t.mem B eV = Vw at hv
  refine WP.mono (WP.keep [.x1, .x2, .x3, .x4, .x5, .x13, .x14, .x15, .x16, .x17] (Q := fun t' =>
      t'.gpr .x1 = (if decide ((D - U2 &&& D - U2) = 0) then (BitVec.ofNat 16 0).setWidth 64 - BitVec.ofNat 64 1
        else mgq Vw U2 U1 D) ∧ t'.gpr .x2 = U2 ∧ t'.gpr .x5 = D ∧ t'.mem = t.mem) (by
    brun [h11, h9, h12, h6, h7, r2d_exec_tst, r2d_exec_cselc, CondCode.holds, shl3_sub8 (show 1 ≤ w by omega_arith)
      (show w < 2 ^ 61 by omega_arith), off_add, off_sub8 B (show 8 ≤ eX + 8 * (w - 1) by omega_arith), e1,
      hs.ld (show eM + 8 * (w - 1) + 8 ≤ Z by omega_arith), hs.ld (show eX + 8 * (w - 1) + 8 ≤ Z by omega_arith),
      hs.ld (show eX + 8 * (w - 2) + 8 ≤ Z by omega_arith), hs.ld hE, hD, hU2, hU1, hVw, quot, quotHead, quotMG]
    all_goals rfl) (by decide) (by decide) (by decide +kernel)) fun t' ⟨⟨h1, h2, h5, hm⟩, k⟩ =>
      ⟨?_, h2, h5, hm, k⟩
  rw [h1]
  have hD' := D.isLt
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

/-- `sbc`, for `simp`. -/
theorem r2d_exec_sbc (s : State) {d n m : Reg} :
    exec (.sbc .x d n m) s = some (s.write .x d (s.gpr n + ~~~s.gpr m + BitVec.ofNat 64 s.c.toNat)) := rfl

/-- `tst x x` sets `N` to the top bit of `x`. -/
theorem tst_msb (x : BitVec 64) : (x &&& x).msb = decide (2 ^ 63 ≤ x.toNat) := by
  rw [BitVec.and_self, BitVec.msb_eq_decide]

/-! ## The 3-by-2 estimate -/

/-- `quot3Mul`: `q̂₀ D` over three words, for `q̂₀` in `x1` and
`D = (d, dₗ)` in `x5`, `x15`. -/
theorem mul3_ok (s : State) (h7 : s.gpr .x7 = 0) : WP isa (.block quot3Mul) s fun t =>
    ((t.gpr .x17).toNat * 2 ^ 128 + (t.gpr .x14).toNat * 2 ^ 64 + (t.gpr .x13).toNat =
      (s.gpr .x1).toNat * ((s.gpr .x5).toNat * 2 ^ 64 + (s.gpr .x15).toNat) ∧ t.mem = s.mem) ∧
    Keep [.x13, .x14, .x16, .x17] s t := by
  refine WP.keep _ ?_ (by decide) (by decide) (by decide +kernel)
  brun [quot3Mul, h7]
  have e := adcs_val (BitVec.ofNat 64 ((s.gpr .x1).toNat * (s.gpr .x15).toNat / 2 ^ 64)) (s.gpr .x1 * s.gpr .x5) false
  generalize decide (2 ^ 64 ≤ (BitVec.ofNat 64 ((s.gpr .x1).toNat * (s.gpr .x15).toNat / 2 ^ 64)).toNat +
    (s.gpr .x1 * s.gpr .x5).toNat + (false : Bool).toNat) = c at e ⊢
  have hq := (s.gpr .x1).isLt; have hd := (s.gpr .x5).isLt; have hl := (s.gpr .x15).isLt
  simp only [BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ofNat, Bool.toNat_false, Nat.add_zero,
    show (0 : BitVec 64).toNat = 0 from rfl] at e ⊢
  generalize (s.gpr .x1).toNat = q at *
  generalize (s.gpr .x5).toNat = d at *
  generalize (s.gpr .x15).toNat = l at *
  have b1 : q * d / 2 ^ 64 ≤ 2 ^ 64 - 2 := Nat.le_trans (Nat.div_le_div_right (c := 2 ^ 64)
    (Nat.mul_le_mul (show q ≤ 2 ^ 64 - 1 by omega_arith) (show d ≤ 2 ^ 64 - 1 by omega_arith))) (by decide)
  have b0 : q * l / 2 ^ 64 < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.div_le_div_right (c := 2 ^ 64)
    (Nat.mul_le_mul (show q ≤ 2 ^ 64 - 1 by omega_arith) (show l ≤ 2 ^ 64 - 1 by omega_arith))) (by decide)
  have hc := Bool.toNat_le c
  simp only [Nat.zero_mod, Nat.add_zero, Nat.mod_mod, Nat.mod_eq_of_lt b0,
    Nat.mod_eq_of_lt (show q * d / 2 ^ 64 < 2 ^ 64 by omega_arith),
    Nat.mod_eq_of_lt (show c.toNat < 2 ^ 64 by omega_arith)] at e ⊢
  rw [Nat.mod_eq_of_lt (show q * d / 2 ^ 64 + c.toNat < 2 ^ 64 by omega_arith)]
  have hr := Nat.mod_lt (q * l / 2 ^ 64 + q * d % 2 ^ 64) (show 0 < 2 ^ 64 by decide)
  generalize (q * l / 2 ^ 64 + q * d % 2 ^ 64) % 2 ^ 64 = r at e hr ⊢
  have A := Nat.div_add_mod (q * d) (2 ^ 64)
  have C := Nat.div_add_mod (q * l) (2 ^ 64)
  rw [Nat.mul_add, ← Nat.mul_assoc]
  generalize q * d = P1 at *
  generalize q * l = P0 at *
  generalize P1 / 2 ^ 64 = hi at *
  generalize P1 % 2 ^ 64 = ml at *
  generalize P0 / 2 ^ 64 = lh at *
  generalize P0 % 2 ^ 64 = lo at *
  omega_arith

/-- `quot3Sub`: `t = U - P` over three words, with its borrow `b`, for `U` in
`x2`, `x3`, `x4` and `P` in `x17`, `x14`, `x13`. -/
theorem sub3_ok (s : State) : WP isa (.block quot3Sub) s fun t => ((∃ b < 2,
      (t.gpr .x2).toNat * 2 ^ 128 + (t.gpr .x3).toNat * 2 ^ 64 + (t.gpr .x4).toNat +
        ((s.gpr .x17).toNat * 2 ^ 128 + (s.gpr .x14).toNat * 2 ^ 64 + (s.gpr .x13).toNat) =
      (s.gpr .x2).toNat * 2 ^ 128 + (s.gpr .x3).toNat * 2 ^ 64 + (s.gpr .x4).toNat + 2 ^ 192 * b) ∧
      t.mem = s.mem) ∧ Keep [.x2, .x3, .x4] s t := by
  refine WP.keep _ ?_ (by decide) (by decide) (by decide +kernel)
  brun [quot3Sub, r2d_exec_sbc]
  have e0 := sbcs_toNat (s.gpr .x4) (s.gpr .x13) true
  generalize decide (2 ^ 64 ≤ (s.gpr .x4).toNat + (~~~s.gpr .x13).toNat + (true : Bool).toNat) = c1 at e0 ⊢
  have e1 := sbcs_toNat (s.gpr .x3) (s.gpr .x14) c1
  generalize decide (2 ^ 64 ≤ (s.gpr .x3).toNat + (~~~s.gpr .x14).toNat + c1.toNat) = c2 at e1 ⊢
  have e2 := sbcs_toNat (s.gpr .x2) (s.gpr .x17) c2
  generalize decide (2 ^ 64 ≤ (s.gpr .x2).toNat + (~~~s.gpr .x17).toNat + c2.toNat) = c3 at e2
  refine ⟨(!c3).toNat, by cases c3 <;> decide, ?_⟩
  simp only [Bool.not_true, Bool.toNat_false, Nat.add_zero] at e0
  generalize (s.gpr .x4 + ~~~s.gpr .x13 + BitVec.ofNat 64 (true : Bool).toNat).toNat = r0 at e0 ⊢
  generalize (s.gpr .x3 + ~~~s.gpr .x14 + BitVec.ofNat 64 c1.toNat).toNat = r1 at e1 ⊢
  generalize (s.gpr .x2 + ~~~s.gpr .x17 + BitVec.ofNat 64 c2.toNat).toNat = r2 at e2 ⊢
  omega_arith

/-- `quot3Fix`: `q̂ := q̂ - 1` (`x1`) and `t := t + D` if `t` (`x2`, `x3`,
`x4`) is negative, `D = (d, dₗ)` in `x5`, `x15`: the new `t` is `T₂`, with
the carry `c`, and its top word is in `x2`. -/
theorem fix3_ok (s : State) (h7 : s.gpr .x7 = 0) : WP isa (.block quot3Fix) s fun t =>
    ((t.gpr .x1 = if 2 ^ 63 ≤ (s.gpr .x2).toNat then s.gpr .x1 - BitVec.ofNat 64 1 else s.gpr .x1) ∧
      (∃ T₂ c, T₂ < 2 ^ 192 ∧ c < 2 ∧ T₂ / 2 ^ 128 = (t.gpr .x2).toNat ∧
        T₂ + 2 ^ 192 * c = (s.gpr .x2).toNat * 2 ^ 128 + (s.gpr .x3).toNat * 2 ^ 64 + (s.gpr .x4).toNat +
          if 2 ^ 63 ≤ (s.gpr .x2).toNat then (s.gpr .x5).toNat * 2 ^ 64 + (s.gpr .x15).toNat else 0) ∧
      t.mem = s.mem) ∧ Keep [.x1, .x2, .x3, .x4, .x16, .x17] s t := by
  refine WP.keep _ ?_ (by decide) (by decide) (by decide +kernel)
  brun [quot3Fix, h7, r2d_exec_tst, r2d_exec_cselc, CondCode.holds, tst_msb, RegUpd.nf_write]
  have e0 := adcs_val (s.gpr .x4) (s.gpr .x15) false
  generalize decide (2 ^ 64 ≤ (s.gpr .x4).toNat + (s.gpr .x15).toNat + (false : Bool).toNat) = c1 at e0 ⊢
  have e1 := adcs_val (s.gpr .x3) (s.gpr .x5) c1
  generalize decide (2 ^ 64 ≤ (s.gpr .x3).toNat + (s.gpr .x5).toNat + c1.toNat) = c2 at e1 ⊢
  have e2 := adcs_val (s.gpr .x2) 0 c2
  generalize decide (2 ^ 64 ≤ (s.gpr .x2).toNat + (0 : BitVec 64).toNat + c2.toNat) = c3 at e2
  have l0 := (s.gpr .x4 + s.gpr .x15 + BitVec.ofNat 64 (false : Bool).toNat).isLt
  have l1 := (s.gpr .x3 + s.gpr .x5 + BitVec.ofNat 64 c1.toNat).isLt
  have l2 := (s.gpr .x2 + 0 + BitVec.ofNat 64 c2.toNat).isLt
  have m2 := (s.gpr .x2).isLt; have m3 := (s.gpr .x3).isLt; have m4 := (s.gpr .x4).isLt
  by_cases hn : 2 ^ 63 ≤ (s.gpr .x2).toNat
  · simp only [hn, decide_true, ↓reduceIte]
    refine ⟨trivial, (s.gpr .x2 + 0 + BitVec.ofNat 64 c2.toNat).toNat * 2 ^ 128 +
      (s.gpr .x3 + s.gpr .x5 + BitVec.ofNat 64 c1.toNat).toNat * 2 ^ 64 +
      (s.gpr .x4 + s.gpr .x15 + BitVec.ofNat 64 (false : Bool).toNat).toNat, c3.toNat, by omega_arith, by cases c3 <;> decide, ?_, ?_⟩
    · generalize (s.gpr .x2 + 0 + BitVec.ofNat 64 c2.toNat).toNat = r2 at l2 ⊢
      generalize (s.gpr .x3 + s.gpr .x5 + BitVec.ofNat 64 c1.toNat).toNat = r1 at l1 ⊢
      generalize (s.gpr .x4 + s.gpr .x15 + BitVec.ofNat 64 (false : Bool).toNat).toNat = r0 at l0 ⊢
      omega_arith
    · generalize (s.gpr .x2 + 0 + BitVec.ofNat 64 c2.toNat).toNat = r2 at l2 e2 ⊢
      generalize (s.gpr .x3 + s.gpr .x5 + BitVec.ofNat 64 c1.toNat).toNat = r1 at l1 e1 ⊢
      generalize (s.gpr .x4 + s.gpr .x15 + BitVec.ofNat 64 (false : Bool).toNat).toNat = r0 at l0 e0 ⊢
      simp only [Bool.toNat_false, Nat.add_zero, show (0 : BitVec 64).toNat = 0 from rfl] at e0 e2
      omega_arith
  · simp only [hn, decide_false, Bool.false_eq_true, ↓reduceIte]
    exact ⟨trivial, (s.gpr .x2).toNat * 2 ^ 128 + (s.gpr .x3).toNat * 2 ^ 64 + (s.gpr .x4).toNat, 0, by omega_arith,
      by decide, by omega_arith, by omega_arith⟩

/-- `quot3Core`: `q̂ = min(⌊U / D⌋, 2^64 - 1)` into `x1` from an estimate
`q̂₀` (`x1`) at most 2 above it, for `U` in `x2`, `x3`, `x4` and `D` in `x5`,
`x15` (`WordStep.quot3_val`). -/
theorem quot3Core_ok (s : State) (h7 : s.gpr .x7 = 0) {U D : Nat}
    (hU : (s.gpr .x2).toNat * 2 ^ 128 + (s.gpr .x3).toNat * 2 ^ 64 + (s.gpr .x4).toNat = U)
    (hD : (s.gpr .x5).toNat * 2 ^ 64 + (s.gpr .x15).toNat = D) (hD0 : 0 < D)
    (hUD : U < (2 ^ 64 + 1) * D) (hge : min (U / D) (2 ^ 64 - 1) ≤ (s.gpr .x1).toNat)
    (hle : (s.gpr .x1).toNat ≤ min (U / D) (2 ^ 64 - 1) + 2) :
    WP isa (.block quot3Core) s fun t => ((t.gpr .x1).toNat = min (U / D) (2 ^ 64 - 1) ∧ t.mem = s.mem) ∧
      Keep [.x1, .x2, .x3, .x4, .x13, .x14, .x16, .x17] s t := by
  have hDW : 4 * D < 2 ^ 192 / 2 := by
    rw [← hD]; have := (s.gpr .x5).isLt; have := (s.gpr .x15).isLt; omega_arith
  unfold quot3Core
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (mul3_ok s h7) fun s₁ ⟨⟨pq, m1⟩, k1⟩ => ?_)
  refine WP.block_append (WP.mono (sub3_ok s₁) fun s₂ ⟨⟨⟨b, hb, tb⟩, m2⟩, k2⟩ => ?_)
  have h7' : s₂.gpr .x7 = 0 := (k2.gpr .x7 (by decide)).trans ((k1.gpr .x7 (by decide)).trans h7)
  refine WP.block_append (WP.mono (fix3_ok s₂ h7') fun s₃ ⟨⟨q3e, ⟨T₂, c, hT₂, hc, hT₂t, tc⟩, m3⟩, k3⟩ => ?_)
  refine WP.mono (WP.keep [.x1, .x2] (Q := fun t => t.gpr .x1 = s₃.gpr .x1 - s₃.gpr .x2 >>> 63 ∧
    t.mem = s₃.mem) (by brun []) (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨t1, tm⟩, kt⟩ =>
    ⟨⟨?_, by rw [tm, m3, m2, m1]⟩, (((k1.trans k2).trans k3).trans kt).mono (by decide)⟩
  have g2 : s₁.gpr .x2 = s.gpr .x2 := k1.gpr .x2 (by decide)
  have g3 : s₁.gpr .x3 = s.gpr .x3 := k1.gpr .x3 (by decide)
  have g4 : s₁.gpr .x4 = s.gpr .x4 := k1.gpr .x4 (by decide)
  have g1 : s₂.gpr .x1 = s.gpr .x1 := (k2.gpr .x1 (by decide)).trans (k1.gpr .x1 (by decide))
  have g5 : s₂.gpr .x5 = s.gpr .x5 := (k2.gpr .x5 (by decide)).trans (k1.gpr .x5 (by decide))
  have g15 : s₂.gpr .x15 = s.gpr .x15 := (k2.gpr .x15 (by decide)).trans (k1.gpr .x15 (by decide))
  rw [g2, g3, g4, hU, pq, hD] at tb
  rw [g5, g15, hD] at tc
  have l2 := (s₂.gpr .x2).isLt; have l3 := (s₂.gpr .x3).isLt; have l4 := (s₂.gpr .x4).isLt
  have hs1 : (2 ^ 192 / 2 ≤ (s₂.gpr .x2).toNat * 2 ^ 128 + (s₂.gpr .x3).toNat * 2 ^ 64 + (s₂.gpr .x4).toNat) ↔
      2 ^ 63 ≤ (s₂.gpr .x2).toNat := by omega_arith
  have hs2 : (2 ^ 192 / 2 ≤ T₂) ↔ 2 ^ 63 ≤ (s₃.gpr .x2).toNat := by rw [← hT₂t]; omega_arith
  have hv := WordStep.quot3_val (W := 2 ^ 192) hD0 hDW hUD hge hle (s.gpr .x1).isLt
    (by omega_arith) hb tb hT₂ hc (by rw [tc]; simp only [hs1])
  simp only [hs1, hs2] at hv
  rw [t1, q3e, g1, shr63_toNat]
  have q1 := (s.gpr .x1).isLt
  generalize min (U / D) (2 ^ 64 - 1) = Q at hv ⊢
  by_cases e1 : 2 ^ 63 ≤ (s₂.gpr .x2).toNat <;> by_cases e2 : 2 ^ 63 ≤ (s₃.gpr .x2).toNat <;>
    simp only [e1, e2, ite_true, ite_false, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false,
      BitVec.toNat_sub, BitVec.toNat_ofNat] at hv ⊢ <;> omega_arith

end VG.Proof.Bignum.AArch64
