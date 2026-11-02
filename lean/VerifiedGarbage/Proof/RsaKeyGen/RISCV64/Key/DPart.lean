module

public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Key.DEnv
public import VerifiedGarbage.Spec.Rsa
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.RsaKeyGen.KeyMath
import VerifiedGarbage.Proof.RsaKeyGen.KeyInv
import VerifiedGarbage.Proof.RsaKeyGen.OddInverseQuotient
import VerifiedGarbage.Proof.Rsa.KeyMath
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_keygen_key` on RISC-V: `d = e⁻¹ mod L`

The code computes all three cases of `e` and selects one (`okv`, whether
`d` exists, and `d`), as on PPC64LE:

* `e` odd and at least 3 (with the modulus `mE`, `e`, or 3 otherwise):
  `L = mE Q + R`, `x = R⁻¹ mod mE`, `d = Q (mE - x) + (R (mE - x) + 1) / mE`
  (`Proof/RsaKeyGen/OddInverseQuotient.lean`), `dOdd_ok`;
* `e = 1`: `d = 1`, for `L ≠ 1`, `dOne_ok`;
* `e` even (with the modulus `mL`, `L` if it is odd and at least 3, or 3
  otherwise): `d = e⁻¹ mod mL`, `dEven_ok`, run only for an even `e`
  (`dPar_ok`; for an odd `e`, `[aD] := [aS]`).

`dPart_ok`: `X6` whether `d` exists (`okv`), and `[aD]` the inverse when it
does; `smallPart_ok`: `X7` := `X6` and `d < [aC]`.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.RISCV64.Key

open VG VG.RISCV64 VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Keys VG.Proof.RsaKeyGen
open VG.Impl.Rsa.RISCV64.Keys (seqs copy sub3 sel eqS bitOf andS)
open VG.Impl.RsaKeyGen.RISCV64.Key (aZero)
open VG.Impl.Rsa.RISCV64.Div (div)
open VG.Impl.RsaKeyGen.RISCV64.Key (nArr aDv aT aS aOne aTwo aThree aE aL aME aQd aDr aDt aTt aQt aRt aNc
  aRp aDo aMl aD aC X0 X1 X2 X3 X4 X5 X6 X7 notS ltS andNotS selS eFlags dOdd dOne dEven dPar dPart smallPart
  invOf mulTo nTwo nW)
open VG.Impl.RsaKeyGen.RISCV64.Key renaming aR → aRm

/-! ## The math -/

/-- The modulus of the odd case: `e`, if it is odd and at least 3, or 3. -/
def mE (e : Nat) : Nat := if ¬ e < 3 ∧ e % 2 = 1 then e else 3

/-- Whether `L` is odd and at least 3. -/
def good (L : Nat) : Prop := ¬ L < 3 ∧ L % 2 = 1

instance (L : Nat) : Decidable (good L) := by unfold good; infer_instance

/-- The modulus of the even case: `L`, if it is odd and at least 3, or 3. -/
def mL (L : Nat) : Nat := if good L then L else 3

/-- Whether `d` exists, by `e`'s case. -/
def okv (e L : Nat) : Prop :=
  (e % 2 = 1 ∧ ((e = 1 ∧ L ≠ 1) ∨ (e ≠ 1 ∧ ¬ L < 2 ∧ Nat.gcd (L % mE e) (mE e) = 1))) ∨
    (e % 2 ≠ 1 ∧ good L ∧ Nat.gcd e (mL L) = 1)

instance (e L : Nat) : Decidable (okv e L) := by unfold okv; infer_instance

theorem mE_odd (e : Nat) : mE e % 2 = 1 ∧ 1 < mE e := by
  unfold mE
  split
  · rename_i h
    have := h.1
    exact ⟨h.2, by omega⟩
  · decide

theorem mL_odd (L : Nat) : mL L % 2 = 1 ∧ 1 < mL L := by
  unfold mL
  by_cases h : good L
  · simp only [h, ↓reduceIte]; unfold good at h; exact ⟨h.2, by omega⟩
  · simp only [h, ↓reduceIte]; decide

theorem mE_of {e : Nat} (h1 : e % 2 = 1) (h2 : e ≠ 1) : mE e = e := by
  unfold mE; simp [show ¬ e < 3 by omega, h1]

theorem mL_of {L : Nat} (h : good L) : mL L = L := by unfold mL; simp [h]

/-- Without `okv`, no inverse. -/
theorem okv_none {e L : Nat} (h : ¬ okv e L) : Spec.Rsa.inverse e L = none := by
  unfold okv at h
  by_cases he : e % 2 = 1
  · by_cases h1 : e = 1
    · have : L = 1 := Decidable.byContradiction fun hL => h (.inl ⟨he, .inl ⟨h1, hL⟩⟩)
      subst h1 this
      exact inverse_mod_one 1
    · rw [mE_of he h1] at h
      exact inverse_odd_none (Q := L / e) (R := L % e) (by omega) (Nat.div_add_mod L e).symm
        fun ⟨a, b⟩ => h (.inl ⟨he, .inr ⟨h1, by omega, b⟩⟩)
  · refine inverse_even_none' (by omega) fun ⟨a, b, c⟩ => h (.inr ⟨he, ⟨by omega, a⟩, ?_⟩)
    rw [mL_of ⟨by omega, a⟩]; exact c

/-- `e` odd, not 1: `d = Q t + (R t + 1) / e`. -/
theorem inverse_odd' {e L x : Nat} (h1 : e % 2 = 1) (h2 : e ≠ 1) (hL : ¬ L < 2)
    (hx : (e : Int) ∣ (x : Int) * (L % e : Nat) - 1) (hxe : x < e) :
    Spec.Rsa.inverse e L = some (L / e * (e - x) + (L % e * (e - x) + 1) / e) :=
  oddQuotient_inverse (Q := L / e) (R := L % e) (by omega) (by omega) (Nat.div_add_mod L e).symm hx hxe

/-- `e = 1`: `d = 1`, for `L ≠ 1`. -/
theorem inverse_one' {L : Nat} (h : L ≠ 1) : Spec.Rsa.inverse 1 L = some 1 := by
  rw [inverse_one]; simp [h]

/-- `e` even: `d = e⁻¹ mod L`, for an odd `L ≥ 3`. -/
theorem inverse_even' {e L x : Nat} (hL : good L) (hx : (L : Int) ∣ (x : Int) * e - 1) (hxL : x < L) :
    Spec.Rsa.inverse e L = some x :=
  VG.Proof.Rsa.inverse_eq (by unfold good at hL; omega) hxL hx

/-- The odd case's numbers fit: `Q t ≤ L` and `R t + 1 < 2^128`, and the
sum `Q t + c ≤ L`, for `t ≤ e < 2^64`. -/
theorem odd_fits {e L x : Nat} (he : e < 2 ^ 64) (h2 : 2 ≤ e) :
    L / e * (e - x) ≤ L ∧ L % e * (e - x) + 1 < 2 ^ 128 ∧
      L / e * (e - x) + (L % e * (e - x) + 1) / e ≤ L := by
  have q : L / e * (e - x) ≤ L / e * e := Nat.mul_le_mul_left _ (Nat.sub_le e x)
  have q' : L / e * e ≤ L := Nat.div_mul_le_self L e
  refine ⟨by omega, odd_numerator_fits he (Nat.mod_lt _ (by omega)), ?_⟩
  exact oddQuotient_le (Q := L / e) (R := L % e) (x := x) (by omega) (Nat.div_add_mod L e).symm

/-! ## The flags of `e`, and the odd case -/

section
variable {s0 s : State} {V F : Nat → Nat}

theorem eFlags_eq : eFlags = seqs (([.block (bitOf X3 aE), eqS X4 aE aOne] : List (Prog isa)) ++
    ltS X5 aE aThree) := rfl

/-- The flags of `e`: `X3` `e` odd, `X4` `e = 1`, `X5` `e < 3`. -/
theorem eFlags_ok (e : KE s0 V F s) (one : V aOne = 1) (three : V aThree = 3) :
    WP isa eFlags s fun t => ∃ V' F', KE s0 V' F' t ∧ (∀ j, j ≠ aT → V' j = V j) ∧
      (∀ d, d ≠ X3 → d ≠ X4 → d ≠ X5 → F' d = F d) ∧
      F' X3 = V aE % 2 ∧ F' X4 = (if V aE = 1 then 1 else 0) ∧ F' X5 = (if V aE < 3 then 1 else 0) := by
  rw [eFlags_eq, wp_seqs_append (by simp) (by simp [ltS])]
  change WP isa (.seq (.block _) (eqS X4 aE aOne)) s _
  rw [WP.seq_iff, ← List.append_nil (bitOf X3 aE)]
  refine bitOfE e (d := X3) (j := aE) (k := fun t1 e1 => WP.block_nil ?_)
  obtain ⟨F1, e1, g1, p1⟩ := e1.fx
  refine WP.mono (eqSE e1 (d := X4) (a := aE) (b := aOne)) fun t2 e2 => ?_
  obtain ⟨F2, e2, g2, p2⟩ := e2.fx
  refine WP.mono (ltSE e2 (d := X5) (a := aE) (b := aThree)) fun t e3 => ?_
  obtain ⟨V3, e3, _, o3⟩ := e3.vx
  obtain ⟨F3, e3, g3, p3⟩ := e3.fx
  exact ⟨V3, F3, e3, o3, fun d a b c => by rw [p3 d c, p2 d b, p1 d a], by
    rw [p3 X3 (by decide), p2 X3 (by decide), g1], by rw [p3 X4 (by decide), g2, one], by rw [g3, three]⟩

/-- The arrays `dOdd` writes. -/
abbrev dOddArrs : List Nat := [aME, aQd, aDv, aRm, aDr, aDt, aTt, aQt, aRt, aNc, aRp, aDo, aT] ++ invOfArrs

theorem dOdd_eq : dOdd = seqs (([.block (andNotS X0 X5 X3), sel aME aThree aE X0, copy aQd aL, copy aDv aME,
    div aQd aRm aDv aDt, invOf aRm aME nTwo, eqS X1 1 aOne, sub3 aTt aME 3, mulTo aQt aQd aTt, mulTo aRt aRm aTt,
    VG.Impl.Rsa.RISCV64.RecoverDet.add aRp aRt aOne aZero aNc, div aRp aDr aDv aDt,
    VG.Impl.Rsa.RISCV64.RecoverDet.add aDo aQt aRp aZero aNc] : List (Prog isa)) ++
    (ltS X2 aL aTwo ++ ([.block (andNotS X6 X2 X1)] : List (Prog isa)))) := rfl

/-- The odd case: `[aDo] = Q t + (R t + 1) / mE` and `X6` := `L ≥ 2` and `gcd(R, mE) = 1`. -/
theorem dOdd_ok [VG.Proof.Rsa.RISCV64.InvLaw] (hp : PreC s0) (e : KE s0 V F s) (he : V aE < 2 ^ 64)
    (one : V aOne = 1) (two : V aTwo = 2) (three : V aThree = 3) (zero : V aZero = 0)
    (b3 : F X3 = V aE % 2) (b5 : F X5 = if V aE < 3 then 1 else 0) :
    WP isa dOdd s fun t => ∃ V' F', KE s0 V' F' t ∧ (∀ j < nArr, j ∉ dOddArrs → V' j = V j) ∧
      (∀ d, d ≠ X0 → d ≠ X1 → d ≠ X2 → d ≠ X6 → F' d = F d) ∧
      (∃ x, x < mE (V aE) ∧ ((mE (V aE) : Nat) : Int) ∣ (x : Int) * (V aL % mE (V aE) : Nat) -
          Nat.gcd (V aL % mE (V aE)) (mE (V aE)) ∧
        V' aDo = V aL / mE (V aE) * (mE (V aE) - x) + (V aL % mE (V aE) * (mE (V aE) - x) + 1) / mE (V aE) ∧
        F' X6 = if ¬ V aL < 2 ∧ Nat.gcd (V aL % mE (V aE)) (mE (V aE)) = 1 then 1 else 0) := by
  have hM : 2 ^ 128 ≤ 2 ^ (64 * wOf s0) :=
    Nat.pow_le_pow_right (by decide) (by have := hp.fits.2.1; omega_arith)
  have mo := mE_odd (V aE)
  have mlt : mE (V aE) < 2 ^ 64 := by unfold mE; split <;> omega_arith
  have Llt := e.lt (j := aL) (by decide)
  rw [dOdd_eq, wp_seqs_append (by simp) (by simp [ltS])]
  -- `X0` := `e` odd and at least 3; `[aME] := mE`.
  change WP isa (.seq (.block (andNotS X0 X5 X3 ++ [])) _) s _
  rw [WP.seq_iff]
  refine andNotSE e (d := X0) (a := X5) (b := X3) (ba := by rw [b5]; exact flag01 _)
    (bb := by rw [b3]; omega_arith) (k := fun t1 e1 => WP.block_nil ?_)
  obtain ⟨F1, e1, g1, p1⟩ := e1.fx
  refine WP.seq (WP.mono (selE e1 (o := aME) (a := aThree) (b := aE) (sl := X0)
    (bit := by rw [g1, b5, b3]; split <;> omega_arith)) fun t2 e2 => ?_)
  obtain ⟨V2, e2, v2, o2⟩ := e2.vx
  have vME : V2 aME = mE (V aE) := by
    rw [v2, g1, b5, b3, three, mE]
    by_cases a : V aE < 3 <;> by_cases b : V aE % 2 = 1 <;> simp [a, b]
  -- `L = mE Q + R`.
  refine WP.seq (WP.mono (copyE e2 (o := aQd) (a := aL)) fun t3 e3 => ?_)
  obtain ⟨V3, e3, v3, o3⟩ := e3.vx
  refine WP.seq (WP.mono (copyE e3 (o := aDv) (a := aME)) fun t4 e4 => ?_)
  obtain ⟨V4, e4, v4, o4⟩ := e4.vx
  have vDv : V4 aDv = mE (V aE) := by rw [v4, o3 aME (by decide), vME]
  have vL : V4 aQd = V aL := by rw [o4 aQd (by decide), v3, o2 aL (by decide)]
  refine WP.seq (WP.mono (divE e4 (q := aQd) (r := aRm) (t := aDt)) fun t5 ⟨V5, e5, o5, v5⟩ => ?_)
  have pos4 : 0 < V4 aDv := by rw [vDv]; omega_arith
  have vQ : V5 aQd = V aL / mE (V aE) := by rw [(v5 pos4).1, vL, vDv]
  have vR : V5 aRm = V aL % mE (V aE) := by rw [(v5 pos4).2, vL, vDv]
  -- `x = R⁻¹ mod mE`.
  have c5 : ∀ j < nArr, j ≠ aME → j ≠ aQd → j ≠ aDv → j ≠ aRm → j ≠ aDt → V5 j = V j :=
    fun j hj a b c d f => by rw [o5 j hj b d f, o4 j c, o3 j b, o2 j a]
  have vM5 : V5 aME = mE (V aE) := by vsimp [o5, o4, o3, vME]
  have rlt : V5 aRm < 2 ^ 64 := by rw [vR]; exact Nat.lt_trans (Nat.mod_lt _ (by omega_arith)) mlt
  refine WP.seq (WP.mono (invOfE e5 (a := aRm) (m := aME) (n := 2)
    (hw := by have := hp.fits.2.1; omega_arith) (hn1 := by decide)
    (hnw := by have := hp.fits.2.1; omega_arith)
    (hk := fun u _ => nTwo_ok u) (odd := by rw [vM5]; exact mo.1) (gt := by rw [vM5]; exact mo.2)
    (xlt := rlt) (mlt := by rw [vM5]; exact mlt))
    fun t6 ⟨V6, e6, o6, g6, d6, l6⟩ => ?_)
  simp only [vM5, vR] at g6 d6 l6
  -- `X1` := `gcd(R, mE) = 1`, `t = mE - x`.
  refine WP.seq (WP.mono (eqSE e6 (d := X1) (a := 1) (b := aOne)) fun t7 e7 => ?_)
  obtain ⟨F7, e7, g7, p7⟩ := e7.fx
  refine WP.seq (WP.mono (sub3E e7 (o := aTt) (a := aME) (b := 3)) fun t8 ⟨e8, _⟩ => ?_)
  obtain ⟨V8, e8, v8, o8⟩ := e8.vx
  have vM6 : V6 aME = mE (V aE) := by rw [o6 aME (by decide) (by decide), vM5]
  have vT : V8 aTt = mE (V aE) - V6 3 := by
    rw [v8, vM6]
    unfold subW
    rw [show mE (V aE) + 2 ^ (64 * wOf s0) - V6 3 = (mE (V aE) - V6 3) + 2 ^ (64 * wOf s0) by omega_arith,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega_arith)]
  -- `Q t` and `R t`.
  have z8 : V8 aZero = 0 := by vsimp [o8, o6, o5, o4, o3, o2, zero]
  refine WP.seq (WP.mono (mulToE e8 (o := aQt) (a := aQd) (b := aTt) (zero := z8)) fun t9 e9 => ?_)
  obtain ⟨V9, e9, v9, o9⟩ := e9.vx
  refine WP.seq (WP.mono (mulToE e9 (o := aRt) (a := aRm) (b := aTt) (zero := by rw [o9 _ (by decide), z8]))
    fun t10 e10 => ?_)
  obtain ⟨V10, e10, v10, o10⟩ := e10.vx
  have tlt : V8 aTt < 2 ^ 64 := by rw [vT]; omega_arith
  have fit := odd_fits (L := V aL) (x := V6 3) mlt (by omega_arith)
  have vQt : V10 aQt = V aL / mE (V aE) * (mE (V aE) - V6 3) := by
    rw [o10 aQt (by decide), v9, o8 aQd (by decide), o6 aQd (by decide) (by decide), vQ, vT,
      Nat.mod_eq_of_lt (by omega_arith)]
  have vRt : V10 aRt = V aL % mE (V aE) * (mE (V aE) - V6 3) := by
    rw [v10, o9 aRm (by decide), o8 aRm (by decide), o6 aRm (by decide) (by decide), vR, o9 aTt (by decide), vT,
      Nat.mod_eq_of_lt (by omega_arith)]
  -- `R t + 1`, `c = (R t + 1) / mE`, `d = Q t + c`.
  have z10 : V10 aZero = 0 := by rw [o10 _ (by decide), o9 _ (by decide), z8]
  have one10 : V10 aOne = 1 := by vsimp [o10, o9, o8, o6, o5, o4, o3, o2, one]
  refine WP.seq (WP.mono (addE e10 (o := aRp) (a := aRt) (b := aOne) (t := aNc) (zero := z10))
    fun t11 ⟨V11, e11, o11, v11⟩ => ?_)
  have vRp : V11 aRp = V aL % mE (V aE) * (mE (V aE) - V6 3) + 1 := by
    rw [v11, vRt, one10, Nat.mod_eq_of_lt (by omega_arith)]
  have vDv11 : V11 aDv = mE (V aE) := by vsimp [o11, o10, o9, o8, o6, o5, vDv]
  refine WP.seq (WP.mono (divE e11 (q := aRp) (r := aDr) (t := aDt)) fun t12 ⟨V12, e12, o12, v12⟩ => ?_)
  have vC : V12 aRp = (V aL % mE (V aE) * (mE (V aE) - V6 3) + 1) / mE (V aE) := by
    rw [(v12 (by rw [vDv11]; omega_arith)).1, vRp, vDv11]
  have z12 : V12 aZero = 0 := by vsimp [o12, o11, z10]
  refine WP.mono (addE e12 (o := aDo) (a := aQt) (b := aRp) (t := aNc) (zero := z12))
    fun t13 ⟨V13, e13, o13, v13⟩ => ?_
  have vQt12 : V12 aQt = V aL / mE (V aE) * (mE (V aE) - V6 3) := by vsimp [o12, o11, vQt]
  have vDo : V13 aDo = V aL / mE (V aE) * (mE (V aE) - V6 3) +
      (V aL % mE (V aE) * (mE (V aE) - V6 3) + 1) / mE (V aE) := by
    rw [v13, vQt12, vC, Nat.mod_eq_of_lt (by omega_arith)]
  have c13 : ∀ j < nArr, j ∉ dOddArrs → V13 j = V j := fun j hj hn => by
    have hi : j ∉ invOfArrs := fun m => hn (List.mem_append_right _ m)
    rw [o13 j hj (ne_of_nm hn) (ne_of_nm hn), o12 j hj (ne_of_nm hn) (ne_of_nm hn) (ne_of_nm hn),
      o11 j hj (ne_of_nm hn) (ne_of_nm hn), o10 j (ne_of_nm hn), o9 j (ne_of_nm hn), o8 j (ne_of_nm hn),
      o6 j hj hi, c5 j hj (ne_of_nm hn) (ne_of_nm hn) (ne_of_nm hn) (ne_of_nm hn) (ne_of_nm hn)]
  -- `X2` := `L < 2`, `X6` := `L ≥ 2` and `gcd(R, mE) = 1`.
  rw [wp_seqs_append (by simp [ltS]) (by simp)]
  refine WP.mono (ltSE e13 (d := X2) (a := aL) (b := aTwo)) fun t14 e14 => ?_
  obtain ⟨V14, e14, _, o14⟩ := e14.vx
  obtain ⟨F14, e14, g14, p14⟩ := e14.fx
  change WP isa (.block (andNotS X6 X2 X1)) t14 _
  rw [← List.append_nil (andNotS X6 X2 X1)]
  refine andNotSE e14 (d := X6) (a := X2) (b := X1) (ba := by rw [g14]; exact flag01 _)
    (bb := by rw [p14 X1 (by decide), g7]; exact flag01 _) (k := fun t e15 => WP.block_nil ?_)
  obtain ⟨F15, e15, g15, p15⟩ := e15.fx
  refine ⟨V14, F15, e15, fun j hj hn => by rw [o14 j (ne_of_nm hn), c13 j hj hn],
    fun d a b c e => by rw [p15 d e, p14 d c, p7 d b, p1 d a],
    V6 3, l6, by rw [← g6]; exact d6, by rw [o14 aDo (by decide), vDo], ?_⟩
  have one6 : V6 aOne = 1 := by vsimp [o6, o5, o4, o3, o2, one]
  rw [g15, g14, p14 X1 (by decide), g7, c13 aL (by decide) (by decide), c13 aTwo (by decide) (by decide), two,
    g6, one6]
  by_cases a : V aL < 2 <;> by_cases b : (V aL % mE (V aE)).gcd (mE (V aE)) = 1 <;> simp [a, b]


/-! ## The case `e = 1`, the even case, and `d` -/

theorem dOne_eq : dOne = seqs [eqS X0 aL aOne, .block (notS X7 X0 ++ (selS X6 X6 X7 X4 ++ ([] : List Instr))),
    sel aS aDo aOne X4] := rfl

/-- `e = 1`: `X7` := `L ≠ 1`, and `X6`, `[aS]` the odd case's or `e = 1`'s. -/
theorem dOne_ok (e : KE s0 V F s) (one : V aOne = 1) (b4 : F X4 ≤ 1) (b6 : F X6 ≤ 1) :
    WP isa dOne s fun t => ∃ V' F', KE s0 V' F' t ∧ (∀ j, j ≠ aS → V' j = V j) ∧
      (∀ d, d ≠ X0 → d ≠ X6 → d ≠ X7 → F' d = F d) ∧
      F' X6 = (if F X4 = 1 then (if V aL = 1 then 0 else 1) else F X6) ∧
      V' aS = (if F X4 = 0 then V aDo else 1) := by
  rw [dOne_eq]
  refine WP.seq (WP.mono (eqSE e (d := X0) (a := aL) (b := aOne)) fun t1 e1 => ?_)
  obtain ⟨F1, e1, g1, p1⟩ := e1.fx
  refine WP.seq ?_
  refine notSE e1 (d := X7) (a := X0) (ba := by rw [g1]; exact flag01 _) (k := fun t2 e2 => ?_)
  obtain ⟨F2, e2, g2, p2⟩ := e2.fx
  have c6 : F2 X6 ≤ 1 := by rw [p2 X6 (by decide), p1 X6 (by decide)]; exact b6
  have c7 : F2 X7 ≤ 1 := by rw [g2]; omega_arith
  have c4' : F2 X4 ≤ 1 := by rw [p2 X4 (by decide), p1 X4 (by decide)]; exact b4
  refine selSE e2 (d := X6) (a := X6) (b := X7) (c := X4) (ba := c6) (bb := c7) (bc := c4')
    (k := fun t3 e3 => WP.block_nil ?_)
  obtain ⟨F3, e3, g3, p3⟩ := e3.fx
  have c4 : F3 X4 = F X4 := by rw [p3 X4 (by decide), p2 X4 (by decide), p1 X4 (by decide)]
  refine WP.mono (selE e3 (o := aS) (a := aDo) (b := aOne) (sl := X4) (bit := by rw [c4]; exact b4))
    fun t e4 => ?_
  obtain ⟨V4, e4, v4, o4⟩ := e4.vx
  refine ⟨V4, F3, e4, o4, fun d a b c => by rw [p3 d b, p2 d c, p1 d a], ?_, by rw [v4, c4, one]⟩
  rw [g3, p2 X4 (by decide), p1 X4 (by decide), g2, p2 X6 (by decide), p1 X6 (by decide), g1, one]
  rcases (show F X4 = 0 ∨ F X4 = 1 by omega) with h | h <;> by_cases a : V aL = 1 <;> simp [a, h]

/-- The arrays `dEven` writes. -/
abbrev dEvenArrs : List Nat := [aT, aMl, aD] ++ invOfArrs

theorem dEven_eq : dEven = seqs (([.block (bitOf X0 aL ++ ([] : List Instr))] : List (Prog isa)) ++
    (ltS X1 aL aThree ++ ([.block (andNotS X2 X1 X0 ++ ([] : List Instr)), sel aMl aThree aL X2, invOf aE aMl nW,
      eqS X0 1 aOne, .block (andS X1 X2 X0 ++ (selS X6 X1 X6 X3 ++ ([] : List Instr))), sel aD 3 aS X3] :
      List (Prog isa)))) := rfl

/-- `e` even: `x = e⁻¹ mod mL`; `[aD]` and `X6` by whether `e` is odd. -/
theorem dEven_ok [VG.Proof.Rsa.RISCV64.InvLaw] (hp : PreC s0) (e : KE s0 V F s) (he : V aE < 2 ^ 64)
    (one : V aOne = 1) (three : V aThree = 3) (zero : V aZero = 0) (b3 : F X3 = V aE % 2) (b6 : F X6 ≤ 1) :
    WP isa dEven s fun t => ∃ V' F', KE s0 V' F' t ∧ (∀ j < nArr, j ∉ dEvenArrs → V' j = V j) ∧
      (∀ d, d ≠ X0 → d ≠ X1 → d ≠ X2 → d ≠ X6 → F' d = F d) ∧
      (∃ x, x < mL (V aL) ∧ ((mL (V aL) : Nat) : Int) ∣ (x : Int) * V aE - Nat.gcd (V aE) (mL (V aL)) ∧
        V' aD = (if V aE % 2 = 1 then V aS else x)) ∧
      F' X6 = (if V aE % 2 = 1 then F X6 else
        if good (V aL) ∧ Nat.gcd (V aE) (mL (V aL)) = 1 then 1 else 0) := by
  have mo := mL_odd (V aL)
  rw [dEven_eq, wp_seqs_append (by simp) (by simp [ltS])]
  change WP isa (.block (bitOf X0 aL ++ [])) s _
  refine bitOfE e (d := X0) (j := aL) (k := fun t1 e1 => WP.block_nil ?_)
  obtain ⟨F1, e1, g1, p1⟩ := e1.fx
  rw [wp_seqs_append (by simp [ltS]) (by simp)]
  refine WP.mono (ltSE e1 (d := X1) (a := aL) (b := aThree)) fun t2 e2 => ?_
  obtain ⟨V2, e2, v2, o2⟩ := e2.vx
  obtain ⟨F2, e2, g2, p2⟩ := e2.fx
  rw [wp_seqs_cons (by simp)]
  refine andNotSE e2 (d := X2) (a := X1) (b := X0) (ba := by rw [g2]; exact flag01 _)
    (bb := by rw [p2 X0 (by decide), g1]; omega_arith) (k := fun t3 e3 => WP.block_nil ?_)
  obtain ⟨F3, e3, g3, p3⟩ := e3.fx
  have vG : F3 X2 = if good (V aL) then 1 else 0 := by
    rw [g3, g2, p2 X0 (by decide), g1, three]
    unfold good
    rcases Nat.mod_two_eq_zero_or_one (V aL) with b | b <;> by_cases a : V aL < 3 <;> simp [a, b]
  rw [wp_seqs_cons (by simp)]
  refine WP.mono (selE e3 (o := aMl) (a := aThree) (b := aL) (sl := X2) (bit := by rw [vG]; exact flag01 _))
    fun t4 e4 => ?_
  obtain ⟨V4, e4, v4, o4⟩ := e4.vx
  have vMl : V4 aMl = mL (V aL) := by
    rw [v4, vG, o2 aThree (by decide), o2 aL (by decide), three, mL]
    by_cases a : good (V aL) <;> simp [a]
  have one4 : V4 aOne = 1 := by rw [o4 aOne (by decide), o2 aOne (by decide), one]
  have zero4 : V4 aZero = 0 := by rw [o4 aZero (by decide), o2 aZero (by decide), zero]
  have vE4 : V4 aE = V aE := by rw [o4 aE (by decide), o2 aE (by decide)]
  have w8 := hp.fits.2.1
  have w128 := hp.fits.2.2
  have wl := hp.wOf_eq
  rw [wp_seqs_cons (by simp)]
  have e32 : 32 * (pLen s0 / 2) = 64 * wOf s0 := by omega_arith
  refine WP.mono (invOfE e4 (a := aE) (m := aMl) (n := pLen s0 / 2) (hw := by omega_arith)
    (hn1 := by omega_arith) (hnw := by omega_arith)
    (hk := fun u hu => nW_ok u (by rw [hu .a1 (by decide), pLen_ofNat e4.st.cb]) (by omega_arith))
    (odd := by rw [vMl]; exact mo.1) (gt := by rw [vMl]; exact mo.2)
    (xlt := by
      rw [vE4, e32]
      exact Nat.lt_of_lt_of_le he (Nat.pow_le_pow_right (by decide) (by omega_arith)))
    (mlt := by rw [e32]; exact e4.lt (by decide)))
    fun t5 ⟨V5, e5, o5, g5, d5, l5⟩ => ?_
  simp only [vMl, vE4] at g5 d5 l5
  have one5 : V5 aOne = 1 := by rw [o5 aOne (by decide) (by decide), one4]
  rw [wp_seqs_cons (by simp)]
  refine WP.mono (eqSE e5 (d := X0) (a := 1) (b := aOne)) fun t6 e6 => ?_
  obtain ⟨F6, e6, g6, p6⟩ := e6.fx
  have vX0 : F6 X0 = if Nat.gcd (V aE) (mL (V aL)) = 1 then 1 else 0 := by rw [g6, g5, one5]
  have vX2 : F6 X2 = if good (V aL) then 1 else 0 := by rw [p6 X2 (by decide), vG]
  rw [wp_seqs_cons (by simp)]
  refine andSE e6 (d := X1) (a := X2) (b := X0) (ba := by rw [vX2]; exact flag01 _)
    (bb := by rw [vX0]; exact flag01 _) (k := fun t7 e7 => ?_)
  obtain ⟨F7, e7, g7, p7⟩ := e7.fx
  have v6 : F7 X6 = F X6 := by vsimp [p7, p6, p3, p2, p1]
  have v3 : F7 X3 = V aE % 2 := by vsimp [p7, p6, p3, p2, p1, b3]
  have c6 : F7 X6 ≤ 1 := by rw [v6]; exact b6
  have c1 : F7 X1 ≤ 1 := by rw [g7, vX2, vX0]; split <;> split <;> omega_arith
  have c3 : F7 X3 ≤ 1 := by rw [v3]; omega_arith
  refine selSE e7 (d := X6) (a := X1) (b := X6) (c := X3) (ba := c1) (bb := c6) (bc := c3)
    (k := fun t8 e8 => WP.block_nil ?_)
  obtain ⟨F8, e8, g8, p8⟩ := e8.fx
  have v3' : F8 X3 = V aE % 2 := by rw [p8 X3 (by decide), v3]
  refine WP.mono (selE e8 (o := aD) (a := 3) (b := aS) (sl := X3) (bit := by rw [v3']; omega_arith))
    fun t e9 => ?_
  obtain ⟨V9, e9, v9, o9⟩ := e9.vx
  refine ⟨V9, F8, e9, fun j hj hn => ?_, fun d a b c e => ?_, ⟨V5 3, l5, by rw [← g5]; exact d5, ?_⟩, ?_⟩
  · have hi : j ∉ invOfArrs := fun m => hn (List.mem_append_right _ m)
    rw [o9 j (ne_of_nm hn), o5 j hj hi, o4 j (ne_of_nm hn), o2 j (ne_of_nm hn)]
  · rw [p8 d e, p7 d b, p6 d a, p3 d c, p2 d b, p1 d a]
  · rw [v9, v3', o5 aS (by decide) (by decide), o4 aS (by decide), o2 aS (by decide)]
    rcases Nat.mod_two_eq_zero_or_one (V aE) with a | a <;> simp [a]
  · rw [g8, v3, v6, g7, vX2, vX0]
    rcases Nat.mod_two_eq_zero_or_one (V aE) with a | a <;>
      by_cases g : good (V aL) <;> by_cases h : (V aE).gcd (mL (V aL)) = 1 <;> simp [a, g, h]

/-- The load of `X3` (`e` odd) into `t5`. -/
theorem ldX3_ok (e : KE s0 V F s) :
    WP isa (.block [.load .d .t5 .s11 X3]) s fun u => KE s0 V F u ∧ (u.gpr .t5).toNat = F X3 := by
  have h := e.ws
  have nw := h.nowrap
  have hz := h.hdr_le
  have hd : X3 + 8 ≤ hdr := by decide
  have hk : WP isa (.block [.load .d .t5 .s11 X3]) s fun u =>
      (u.gpr .t5 = word s.mem (bOf s0) X3 ∧ u.mem = s.mem) ∧ Keep [.t5] s u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [h.s11, h.scr.ld (d := X3) (n := 8) (by omega_arith), h.scr.al8 (d := X3) (by omega_arith) (by decide),
      show X3 < 2048 by decide]
  refine WP.mono hk fun u ⟨⟨v, m⟩, k⟩ => ⟨⟨e.st.regs k m, fun j hj => by rw [m]; exact e.arrs j hj,
    fun d hd => by rw [m]; exact e.flg d hd, by rw [m]; exact e.dv⟩, ?_⟩
  rw [v, ← e.flg X3 (by decide)]

/-- The branch on `e`'s parity: for an odd `e`, `[aD] := [aS]`; for an even `e`, `dEven`. -/
theorem dPar_ok [VG.Proof.Rsa.RISCV64.InvLaw] (hp : PreC s0) (e : KE s0 V F s) (he : V aE < 2 ^ 64)
    (one : V aOne = 1) (three : V aThree = 3) (zero : V aZero = 0) (b3 : F X3 = V aE % 2) (b6 : F X6 ≤ 1) :
    WP isa dPar s fun t => ∃ V' F', KE s0 V' F' t ∧ (∀ j < nArr, j ∉ dEvenArrs → V' j = V j) ∧
      (∀ d, d ≠ X0 → d ≠ X1 → d ≠ X2 → d ≠ X6 → F' d = F d) ∧
      (V aE % 2 = 1 → V' aD = V aS) ∧
      (V aE % 2 = 0 → ∃ x, x < mL (V aL) ∧
        ((mL (V aL) : Nat) : Int) ∣ (x : Int) * V aE - Nat.gcd (V aE) (mL (V aL)) ∧ V' aD = x) ∧
      F' X6 = (if V aE % 2 = 1 then F X6 else
        if good (V aL) ∧ Nat.gcd (V aE) (mL (V aL)) = 1 then 1 else 0) := by
  refine WP.seq (WP.mono (ldX3_ok e) fun u ⟨eu, hu⟩ => ?_)
  refine WP.ite _ (Steps.eval_nonzero u .t5) (fun hb => ?_) (fun _ => ?_)
  · have odd : V aE % 2 = 1 := by
      have h0 : u.gpr .t5 ≠ 0 := by simpa using hb
      have h1 : (u.gpr .t5).toNat ≠ 0 := fun h => h0 (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
      omega_arith
    refine WP.mono (copyE eu (o := aD) (a := aS)) fun t et => ?_
    obtain ⟨V', et, v', o'⟩ := et.vx
    exact ⟨V', F, et, fun j _ hn => o' j (ne_of_nm hn), fun _ _ _ _ _ => rfl, fun _ => v',
      fun h => absurd h (by omega_arith), by simp [odd]⟩
  · refine WP.mono (dEven_ok hp eu he one three zero b3 b6) fun t ⟨V', F', et, ov, of, ⟨x, xl, xd, vD⟩, x6⟩ => ?_
    refine ⟨V', F', et, ov, of, fun h => by simp only [vD, h, ↓reduceIte], fun h => ⟨x, xl, xd, ?_⟩, x6⟩
    have h' : ¬ V aE % 2 = 1 := by omega
    simp only [vD, h', ↓reduceIte]

/-- The arrays `dPart` writes. -/
abbrev dPartArrs : List Nat := [aT, aS] ++ dOddArrs ++ dEvenArrs

/-- `X6` whether `d` exists, and then `[aD] = d`; `X3` `e` odd, `X5` `e < 3`. -/
theorem dPart_ok [VG.Proof.Rsa.RISCV64.InvLaw] (hp : PreC s0) (e : KE s0 V F s) (he : V aE < 2 ^ 64)
    (one : V aOne = 1) (two : V aTwo = 2) (three : V aThree = 3) (zero : V aZero = 0) :
    WP isa dPart s fun t => ∃ V' F', KE s0 V' F' t ∧ (∀ j < nArr, j ∉ dPartArrs → V' j = V j) ∧
      (∀ d, d ≠ X0 → d ≠ X1 → d ≠ X2 → d ≠ X3 → d ≠ X4 → d ≠ X5 → d ≠ X6 → d ≠ X7 → F' d = F d) ∧
      F' X3 = V aE % 2 ∧ F' X5 = (if V aE < 3 then 1 else 0) ∧
      F' X6 = (if okv (V aE) (V aL) then 1 else 0) ∧
      (okv (V aE) (V aL) → Spec.Rsa.inverse (V aE) (V aL) = some (V' aD)) := by
  change WP isa (.seq eFlags (.seq dOdd (.seq dOne dPar))) s _
  refine WP.seq (WP.mono (eFlags_ok e one three) fun t1 ⟨V1, F1, e1, o1, p1, x3, x4, x5⟩ => ?_)
  have one1 : V1 aOne = 1 := by rw [o1 _ (by decide), one]
  have two1 : V1 aTwo = 2 := by rw [o1 _ (by decide), two]
  have three1 : V1 aThree = 3 := by rw [o1 _ (by decide), three]
  have zero1 : V1 aZero = 0 := by rw [o1 _ (by decide), zero]
  have ve1 : V1 aE = V aE := o1 _ (by decide)
  have l1 : V1 aL = V aL := o1 _ (by decide)
  refine WP.seq (WP.mono (dOdd_ok hp e1 (by rw [ve1]; exact he) one1 two1 three1 zero1 (by rw [x3, ve1])
    (by rw [x5, ve1])) fun t2 ⟨V2, F2, e2, o2, p2, x, xl, xd, vDo, x6⟩ => ?_)
  simp only [ve1, l1] at xl xd vDo x6
  have one2 : V2 aOne = 1 := by rw [o2 _ (by decide) (by decide), one1]
  have three2 : V2 aThree = 3 := by rw [o2 _ (by decide) (by decide), three1]
  have zero2 : V2 aZero = 0 := by rw [o2 _ (by decide) (by decide), zero1]
  have ve2 : V2 aE = V aE := by rw [o2 _ (by decide) (by decide), ve1]
  have l2 : V2 aL = V aL := by rw [o2 _ (by decide) (by decide), l1]
  have y4 : F2 X4 = if V aE = 1 then 1 else 0 := by rw [p2 X4 (by decide) (by decide) (by decide) (by decide), x4]
  have y3 : F2 X3 = V aE % 2 := by rw [p2 X3 (by decide) (by decide) (by decide) (by decide), x3]
  have y5 : F2 X5 = if V aE < 3 then 1 else 0 := by
    rw [p2 X5 (by decide) (by decide) (by decide) (by decide), x5]
  refine WP.seq (WP.mono (dOne_ok e2 one2 (by rw [y4]; exact flag01 _) (by rw [x6]; exact flag01 _))
    fun t3 ⟨V3, F3, e3, o3, p3, z6, vS⟩ => ?_)
  have one3 : V3 aOne = 1 := by rw [o3 _ (by decide), one2]
  have three3 : V3 aThree = 3 := by rw [o3 _ (by decide), three2]
  have zero3 : V3 aZero = 0 := by rw [o3 _ (by decide), zero2]
  have ve3 : V3 aE = V aE := by rw [o3 _ (by decide), ve2]
  have l3 : V3 aL = V aL := by rw [o3 _ (by decide), l2]
  have w3 : F3 X3 = V aE % 2 := by rw [p3 X3 (by decide) (by decide) (by decide), y3]
  refine WP.mono (dPar_ok hp e3 (by rw [ve3]; exact he) one3 three3 zero3 (by rw [w3, ve3])
    (by rw [z6, x6]; split <;> split <;> omega_arith))
    fun t ⟨V4, F4, e4, o4, p4, vOd, vEv, z6'⟩ => ?_
  simp only [ve3, l3] at vOd vEv z6'
  refine ⟨V4, F4, e4, fun j hj hn => ?_, fun d a b c d3 d4 d5 d6 d7 => ?_, ?_, ?_, ?_, ?_⟩
  · have n4 : j ∉ dEvenArrs := fun m => hn (List.mem_append_right _ m)
    have n3 : j ∉ dOddArrs := fun m => hn (List.mem_append_left _ (List.mem_append_right _ m))
    rw [o4 j hj n4, o3 j (ne_of_nm hn), o2 j hj n3, o1 j (ne_of_nm hn)]
  · rw [p4 d a b c d6, p3 d a d6 d7, p2 d a b c d6, p1 d d3 d4 d5]
  · rw [p4 X3 (by decide) (by decide) (by decide) (by decide), w3]
  · rw [p4 X5 (by decide) (by decide) (by decide) (by decide), p3 X5 (by decide) (by decide) (by decide), y5]
  · rw [z6', z6, y4, x6, l2]
    rcases Nat.mod_two_eq_zero_or_one (V aE) with a | a
    · simp [a, okv]
    · by_cases b : V aE = 1
      · rw [b]; simp [okv]
      · simp [a, b, okv]
  · intro ok
    rcases Nat.mod_two_eq_zero_or_one (V aE) with a | a
    · obtain ⟨x', xl', xd', vD⟩ := vEv a
      have ok' : good (V aL) ∧ Nat.gcd (V aE) (mL (V aL)) = 1 := by
        rcases ok with ⟨a', _⟩ | ⟨_, g1, g2⟩
        · omega_arith
        · exact ⟨g1, g2⟩
      rw [vD]
      have g := ok'.2
      rw [mL_of ok'.1] at g xd' xl'
      rw [g] at xd'
      exact inverse_even' ok'.1 (by exact_mod_cast xd') xl'
    · rw [vOd a, vS, y4]
      by_cases b : V aE = 1
      · have hL : V aL ≠ 1 := by
          rcases ok with ⟨_, (⟨_, h⟩ | ⟨b', _⟩)⟩ | ⟨a', _⟩
          · exact h
          · exact absurd b b'
          · omega_arith
        simp only [b, ↓reduceIte, Nat.one_ne_zero]
        exact inverse_one' hL
      · have ok' : ¬ V aL < 2 ∧ Nat.gcd (V aL % V aE) (V aE) = 1 := by
          rcases ok with ⟨_, (⟨b', _⟩ | ⟨_, hL, g⟩)⟩ | ⟨a', _⟩
          · exact absurd b' b
          · rw [mE_of a b] at g; exact ⟨hL, g⟩
          · omega_arith
        simp only [b, ↓reduceIte]
        rw [mE_of a b] at xd xl vDo
        rw [vDo]
        rw [ok'.2] at xd
        exact inverse_odd' a b ok'.1 (by exact_mod_cast xd) xl

theorem smallPart_eq : smallPart = seqs (ltS X0 aD aC ++
    ([.block (andS X7 X0 X6 ++ ([] : List Instr))] : List (Prog isa))) := rfl

/-- `X7` := `X6` and `d < [aC]`. -/
theorem smallPart_ok (e : KE s0 V F s) (b6 : F X6 ≤ 1) :
    WP isa smallPart s fun t => ∃ V' F', KE s0 V' F' t ∧ (∀ j, j ≠ aT → V' j = V j) ∧
      (∀ d, d ≠ X0 → d ≠ X7 → F' d = F d) ∧ F' X7 = (if F X6 = 1 ∧ V aD < V aC then 1 else 0) := by
  rw [smallPart_eq, wp_seqs_append (by simp [ltS]) (by simp)]
  refine WP.mono (ltSE e (d := X0) (a := aD) (b := aC)) fun t1 e1 => ?_
  obtain ⟨V1, e1, _, o1⟩ := e1.vx
  obtain ⟨F1, e1, g1, p1⟩ := e1.fx
  change WP isa (.block (andS X7 X0 X6 ++ [])) t1 _
  refine andSE e1 (d := X7) (a := X0) (b := X6) (ba := by rw [g1]; exact flag01 _)
    (bb := by rw [p1 X6 (by decide)]; exact b6) (k := fun t e2 => WP.block_nil ?_)
  obtain ⟨F2, e2, g2, p2⟩ := e2.fx
  refine ⟨V1, F2, e2, o1, fun d a b => by rw [p2 d b, p1 d a], ?_⟩
  rw [g2, g1, p1 X6 (by decide)]
  by_cases a : F X6 = 1 <;> by_cases b : V aD < V aC <;> simp [a, b]
  omega_arith

end

end VG.Proof.RsaKeyGen.RISCV64.Key
