module

public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Key.Mul
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Key.DMath
import VerifiedGarbage.Proof.Rsa.PPC64LE.InvParts
import VerifiedGarbage.Proof.RsaKeyGen.OddInverseQuotient
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Key.Env2
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Key.Env3

/-!
# `vg_rsa_keygen_key` on PPC64LE: the flags of `e`, and the odd case of `d`

`eFlags_ok`: `X3` `e` odd, `X4` `e = 1`, `X5` `e < 3`. `dOdd_ok`: with the
modulus `mE e`, `L = mE Q + R`, `x = R⁻¹ mod mE`, `t = mE - x`,
`[aDo] = Q t + (R t + 1) / mE` (exactly: every number fits), and `X6`
whether `L ≥ 2` and `gcd(R, mE) = 1`.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Key

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Keys (seqs copy sub3 sel eqS aZero)
open VG.Impl.Rsa.PPC64LE.Div (div)
open VG.Impl.RsaKeyGen.PPC64LE.Key (nArr aDv aT aOne aTwo aThree aE aL aME aQd aR aDr aDt aTt aQt aRt aNc aDo
  X0 X1 X2 X3 X4 X5 X6 ltS andNotS eFlags dOdd invOf mulTo addTo)
open VG.Proof.Rsa.PPC64LE (InvLaw)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot)

section
variable {s : State} {B : Addr} {Z w : Nat} {V F : Nat → Nat}

theorem eFlags_eq : eFlags = seqs (([.block (VG.Impl.Rsa.PPC64LE.Keys.bitOf X3 aE), eqS X4 aE aOne] :
    List (Prog isa)) ++ ltS X5 aE aThree) := rfl

/-- The flags of `e`. -/
theorem eFlags_ok (h : Ws s B Z w nArr) (ks : KS s.mem B w V F) (one : V aOne = 1) (three : V aThree = 3) :
    WP isa eFlags s fun t => Ws t B Z w nArr ∧
      (∃ V' F', KS t.mem B w V' F' ∧ (∀ j, j ≠ aT → V' j = V j) ∧
        (∀ d, d ≠ X3 → d ≠ X4 → d ≠ X5 → F' d = F d) ∧
        F' X3 = V aE % 2 ∧ F' X4 = (if V aE = 1 then 1 else 0) ∧ F' X5 = (if V aE < 3 then 1 else 0)) ∧
      KK B w s.mem t.mem ∧ Keep bodyRegs s t := by
  rw [eFlags_eq, wp_seqs_append (by simp) (by simp [ltS])]
  change WP isa (.seq (.block _) (eqS X4 aE aOne)) s _
  rw [WP.seq_iff, ← List.append_nil (VG.Impl.Rsa.PPC64LE.Keys.bitOf X3 aE)]
  refine bitOfE h ks (d := X3) (j := aE) (k := fun t1 h1 k1 f1 r1 => WP.block_nil ?_)
  obtain ⟨F1, k1, g1, p1⟩ := k1.fx
  refine WP.mono (eqSE h1 k1 (d := X4) (a := aE) (b := aOne)) fun t2 ⟨h2, k2, f2, r2⟩ => ?_
  obtain ⟨F2, k2, g2, p2⟩ := k2.fx
  refine WP.mono (ltSE h2 k2 (d := X5) (a := aE) (b := aThree)) fun t ⟨ht, kt, ft, rt⟩ => ?_
  obtain ⟨V3, kt, e3, o3⟩ := kt.vx
  obtain ⟨F3, kt, g3, p3⟩ := kt.fx
  exact ⟨ht, ⟨V3, F3, kt, o3, fun d a b c => by rw [p3 d c, p2 d b, p1 d a], by
      rw [p3 X3 (by decide), p2 X3 (by decide), g1], by rw [p3 X4 (by decide), g2, one], by rw [g3, three]⟩,
    (f1.trans f2).trans ft, ((r1.trans' r2).trans' rt).mono⟩

/-- The arrays `dOdd` writes. -/
abbrev dOddArrs : List Nat := [aME, aQd, aDv, aR, aDr, aDt, aTt, aQt, aRt, aNc, aDo, aT] ++ invOfArrs ++ mulArrs

theorem dOdd_eq : dOdd = seqs (([.block (andNotS X0 X5 X3), sel aME aThree aE X0, copy aQd aL, copy aDv aME,
    div aQd aR aDv aDt, invOf aR aME VG.Impl.RsaKeyGen.PPC64LE.Key.nTwo, eqS X1 1 aOne, sub3 aTt aME 3, mulTo aQt aQd aTt [.li .r11 64],
    mulTo aRt aR aTt [.li .r11 64], addTo aRt aOne aNc aZero, div aRt aDr aDv aDt, copy aDo aQt,
    addTo aDo aRt aNc aZero] : List (Prog isa)) ++ (ltS X2 aL aTwo ++ ([.block (andNotS X6 X2 X1)] : List (Prog isa)))) := rfl

theorem li64_ok (u : State) : WP isa (.block [.li .r11 64]) u fun u' =>
    (u'.gpr .r11 = BitVec.ofNat 64 64 ∧ u'.mem = u.mem) ∧ Keep [.r11] u u' := by
  refine WP.keep _ ?_ (by decide)
  prun

/-- The odd case: `[aDo] = Q t + (R t + 1) / mE` and `X6`. -/
theorem dOdd_ok [InvLaw] (h : Ws s B Z w nArr) (ks : KS s.mem B w V F) (hw : 10 ≤ w) (he : V aE < 2 ^ 64)
    (one : V aOne = 1) (two : V aTwo = 2) (three : V aThree = 3) (zero : V aZero = 0)
    (b3 : F X3 = V aE % 2) (b5 : F X5 = if V aE < 3 then 1 else 0) :
    WP isa dOdd s fun t => Ws t B Z w nArr ∧
      (∃ V' F', KS t.mem B w V' F' ∧ (∀ j < nArr, j ∉ dOddArrs → V' j = V j) ∧
        (∀ d, d ≠ X0 → d ≠ X1 → d ≠ X2 → d ≠ X6 → F' d = F d) ∧
        (∃ x, x < mE (V aE) ∧ ((mE (V aE) : Nat) : Int) ∣ (x : Int) * (V aL % mE (V aE) : Nat) -
            Nat.gcd (V aL % mE (V aE)) (mE (V aE)) ∧
          V' aDo = V aL / mE (V aE) * (mE (V aE) - x) + (V aL % mE (V aE) * (mE (V aE) - x) + 1) / mE (V aE) ∧
          F' X6 = if ¬ V aL < 2 ∧ Nat.gcd (V aL % mE (V aE)) (mE (V aE)) = 1 then 1 else 0)) ∧
      KK B w s.mem t.mem ∧ Keep bodyRegs s t := by
  have hM : 2 ^ 128 ≤ 2 ^ (32 * w) := Nat.pow_le_pow_right (by decide) (by omega_arith)
  have mo := mE_odd (V aE)
  have mlt : mE (V aE) < 2 ^ 64 := by unfold mE; split <;> omega_arith
  rw [dOdd_eq, wp_seqs_append (by simp) (by simp [ltS])]
  -- `X0` := `e` odd and at least 3; `[aME] := mE`.
  change WP isa (.seq (.block (andNotS X0 X5 X3 ++ [])) _) s _
  rw [WP.seq_iff]
  refine andNotSE h ks (d := X0) (a := X5) (b := X3) (ba := by rw [b5]; exact flag01 _)
    (bb := by rw [b3]; omega_arith) (k := fun t1 h1 k1 f1 r1 => WP.block_nil ?_)
  obtain ⟨F1, k1, g1, p1⟩ := k1.fx
  refine WP.seq (WP.mono (selE h1 k1 (o := aME) (a := aThree) (b := aE) (sl := X0)
    (bit := by rw [g1]; exact flag01 _)) fun t2 ⟨h2, k2, f2, r2⟩ => ?_)
  obtain ⟨V2, k2, e2, o2⟩ := k2.vx
  have vME : V2 aME = mE (V aE) := by
    rw [e2, g1, b5, b3, three, mE]
    have := Nat.mod_two_eq_zero_or_one (V aE)
    by_cases a : V aE < 3 <;> by_cases b : V aE % 2 = 1 <;> simp [a, b] <;> omega_arith
  -- `L = mE Q + R`.
  refine WP.seq (WP.mono (copyE h2 k2 (o := aQd) (a := aL)) fun t3 ⟨h3, k3, f3, r3⟩ => ?_)
  obtain ⟨V3, k3, e3, o3⟩ := k3.vx
  refine WP.seq (WP.mono (copyE h3 k3 (o := aDv) (a := aME)) fun t4 ⟨h4, k4, f4, r4⟩ => ?_)
  obtain ⟨V4, k4, e4, o4⟩ := k4.vx
  have vDv : V4 aDv = mE (V aE) := by rw [e4, o3 aME (by decide), vME]
  refine WP.seq (WP.mono (divE h4 k4 (q := aQd) (r := aR) (t := aDt)) fun t5 ⟨h5, ⟨V5, k5, o5, e5⟩, f5, r5⟩ => ?_)
  have vL : V4 aQd = V aL := by rw [o4 aQd (by decide), e3, o2 aL (by decide)]
  have vQ : V5 aQd = V aL / mE (V aE) := by rw [(e5 (by rw [vDv]; omega_arith)).1, vL, vDv]
  have vR : V5 aR = V aL % mE (V aE) := by rw [(e5 (by rw [vDv]; omega_arith)).2, vL, vDv]
  -- `x = R⁻¹ mod mE`.
  have c5 : ∀ j < nArr, j ≠ aME → j ≠ aQd → j ≠ aDv → j ≠ aR → j ≠ aDt → V5 j = V j := fun j hj a b c d f => by
    rw [o5 j hj b d f, o4 j c, o3 j b, o2 j a]
  have one5 : V5 aOne = 1 := by
    rw [c5 aOne (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), one]
  have zero5 : V5 aZero = 0 := by
    rw [c5 aZero (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), zero]
  have vM5 : V5 aME = mE (V aE) := by
    rw [o5 aME (by decide) (by decide) (by decide) (by decide), o4 aME (by decide), o3 aME (by decide), vME]
  refine WP.seq (WP.mono (invOfE h5 k5 hw (a := aR) (m := aME) (hk := nTwo_width) (hn1 := by decide)
    (hnw := by omega_arith) (han := by rw [vR]; exact Nat.lt_trans (Nat.mod_lt _ (by omega_arith)) mlt)
    (hmn := by rw [vM5]; exact mlt) (odd := by rw [vM5]; exact mo.1) (gt := by rw [vM5]; exact mo.2))
    fun t6 ⟨h6, ⟨V6, k6, o6, g6, d6, l6⟩, f6, r6⟩ => ?_)
  simp only [vM5, vR] at g6 d6 l6
  -- `X1` := `gcd(R, mE) = 1`, `t = mE - x`.
  refine WP.seq (WP.mono (eqSE h6 k6 (d := X1) (a := 1) (b := aOne)) fun t7 ⟨h7, k7, f7, r7⟩ => ?_)
  obtain ⟨F7, k7, g7, p7⟩ := k7.fx
  refine WP.seq (WP.mono (sub3E h7 k7 (o := aTt) (a := aME) (b := 3)) fun t8 ⟨h8, k8, _, f8, r8⟩ => ?_)
  obtain ⟨V8, k8, e8, o8⟩ := k8.vx
  have vM6 : V6 aME = mE (V aE) := by rw [o6 aME (by decide) (by decide), vM5]
  have vT : V8 aTt = mE (V aE) - V6 3 := by
    rw [e8, vM6]
    unfold subW
    rw [show mE (V aE) + 2 ^ (32 * w) - V6 3 = (mE (V aE) - V6 3) + 2 ^ (32 * w) by omega_arith, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega_arith)]
  -- `Q t` and `R t`.
  have o68 : ∀ j < nArr, j ∉ invOfArrs → j ≠ aTt → V8 j = V5 j := fun j hj hi ht => by rw [o8 j ht, o6 j hj hi]
  refine WP.seq (WP.mono (mulToE h8 k8 (o := aQt) (a := aQd) (b := aTt) (K := 64) (hK := by decide)
    (hK' := by decide) (hk := fun u _ => li64_ok u) (hZ := by rw [o68 aZero (by decide) (by decide) (by decide),
      c5 aZero (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), zero]))
    fun t9 ⟨h9, ⟨V9, k9, o9, e9⟩, f9, r9⟩ => ?_)
  refine WP.seq (WP.mono (mulToE h9 k9 (o := aRt) (a := aR) (b := aTt) (K := 64) (hK := by decide)
    (hK' := by decide) (hk := fun u _ => li64_ok u) (hZ := by rw [o9 aZero (by decide) (by decide) (by decide),
      o68 aZero (by decide) (by decide) (by decide), c5 aZero (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), zero])) fun t10 ⟨h10, ⟨V10, k10, o10, e10⟩, f10, r10⟩ => ?_)
  have tlt : V8 aTt < 2 ^ 64 := by rw [vT]; omega_arith
  have vQt : V10 aQt = V aL / mE (V aE) * (mE (V aE) - V6 3) := by
    have fit := odd_fits (L := V aL) (x := V6 3) mlt (by omega_arith)
    rw [o10 aQt (by decide) (by decide) (by decide), e9, o68 aQd (by decide) (by decide) (by decide), vQ, Nat.mod_eq_of_lt tlt,
      vT, Nat.mod_eq_of_lt]
    have := ks.lt (j := aL) (by decide)
    omega_arith
  have vRt : V10 aRt = V aL % mE (V aE) * (mE (V aE) - V6 3) := by
    have fit := odd_fits (L := V aL) (x := V6 3) mlt (by omega_arith)
    have t9 : V9 aTt = V8 aTt := o9 aTt (by decide) (by decide) (by decide)
    rw [e10, o9 aR (by decide) (by decide) (by decide), o68 aR (by decide) (by decide) (by decide), vR, t9,
      Nat.mod_eq_of_lt tlt, vT, Nat.mod_eq_of_lt (by omega_arith)]
  -- `R t + 1`, `c = (R t + 1) / mE`, `d = Q t + c`.
  have z10 : V10 aZero = 0 := by
    rw [o10 aZero (by decide) (by decide) (by decide), o9 aZero (by decide) (by decide) (by decide), o68 aZero (by decide) (by decide)
      (by decide), c5 aZero (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), zero]
  have one10 : V10 aOne = 1 := by
    rw [o10 aOne (by decide) (by decide) (by decide), o9 aOne (by decide) (by decide) (by decide), o68 aOne (by decide) (by decide)
      (by decide), c5 aOne (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), one]
  refine WP.seq (WP.mono (addToE h10 k10 (o := aRt) (a := aOne) (n := aNc) (z := aZero) (z0 := z10))
    fun t11 ⟨h11, k11, f11, r11⟩ => ?_)
  obtain ⟨V11, k11, e11, o11⟩ := k11.vx
  have fit := odd_fits (L := V aL) (x := V6 3) mlt (by omega_arith)
  have vRt1 : V11 aRt = V aL % mE (V aE) * (mE (V aE) - V6 3) + 1 := by
    rw [e11, vRt, one10, Nat.mod_eq_of_lt (by omega_arith)]
  have vDv10 : V10 aDv = mE (V aE) := by
    rw [o10 aDv (by decide) (by decide) (by decide), o9 aDv (by decide) (by decide) (by decide),
      o68 aDv (by decide) (by decide) (by decide), o5 aDv (by decide) (by decide) (by decide) (by decide), vDv]
  have vDv11 : V11 aDv = mE (V aE) := by rw [o11 aDv (by decide), upd_ne (by decide), vDv10]
  refine WP.seq (WP.mono (divE h11 k11 (q := aRt) (r := aDr) (t := aDt)) fun t12 ⟨h12, ⟨V12, k12, o12, e12⟩, f12,
    r12⟩ => ?_)
  have vC : V12 aRt = (V aL % mE (V aE) * (mE (V aE) - V6 3) + 1) / mE (V aE) := by
    rw [(e12 (by rw [vDv11]; omega_arith)).1, vRt1, vDv11]
  refine WP.seq (WP.mono (copyE h12 k12 (o := aDo) (a := aQt)) fun t13 ⟨h13, k13, f13, r13⟩ => ?_)
  obtain ⟨V13, k13, e13, o13⟩ := k13.vx
  have z13 : V13 aZero = 0 := by
    rw [o13 aZero (by decide), o12 aZero (by decide) (by decide) (by decide) (by decide), o11 aZero (by decide),
      upd_ne (by decide), z10]
  refine WP.mono (addToE h13 k13 (o := aDo) (a := aRt) (n := aNc) (z := aZero) (z0 := z13))
    fun t14 ⟨h14, k14, f14, r14⟩ => ?_
  obtain ⟨V14, k14, e14, o14⟩ := k14.vx
  have vQt12 : V12 aQt = V aL / mE (V aE) * (mE (V aE) - V6 3) := by
    rw [o12 aQt (by decide) (by decide) (by decide) (by decide), o11 aQt (by decide), upd_ne (by decide), vQt]
  have vDo : V14 aDo = V aL / mE (V aE) * (mE (V aE) - V6 3) +
      (V aL % mE (V aE) * (mE (V aE) - V6 3) + 1) / mE (V aE) := by
    rw [e14, e13, o13 aRt (by decide), vQt12, vC]
    have := ks.lt (j := aL) (by decide)
    rw [Nat.mod_eq_of_lt (by omega_arith)]
  -- `X2` := `L < 2`, `X6` := `L ≥ 2` and `gcd(R, mE) = 1`.
  have vL14 : V14 aL = V aL := by
    rw [o14 aL (by decide), upd_ne (by decide), o13 aL (by decide), o12 aL (by decide) (by decide) (by decide)
      (by decide), o11 aL (by decide), upd_ne (by decide), o10 aL (by decide) (by decide) (by decide),
      o9 aL (by decide) (by decide) (by decide), o68 aL (by decide) (by decide) (by decide),
      c5 aL (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  have vTwo14 : V14 aTwo = 2 := by
    rw [o14 aTwo (by decide), upd_ne (by decide), o13 aTwo (by decide), o12 aTwo (by decide) (by decide)
      (by decide) (by decide), o11 aTwo (by decide), upd_ne (by decide), o10 aTwo (by decide) (by decide)
      (by decide), o9 aTwo (by decide) (by decide) (by decide), o68 aTwo (by decide) (by decide) (by decide),
      c5 aTwo (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), two]
  rw [wp_seqs_append (by simp [ltS]) (by simp)]
  refine WP.mono (ltSE h14 k14 (d := X2) (a := aL) (b := aTwo)) fun t15 ⟨h15, k15, f15, r15⟩ => ?_
  obtain ⟨V15, k15, e15, o15⟩ := k15.vx
  obtain ⟨F15, k15, g15, p15⟩ := k15.fx
  change WP isa (.block (andNotS X6 X2 X1)) t15 _
  rw [← List.append_nil (andNotS X6 X2 X1)]
  refine andNotSE h15 k15 (d := X6) (a := X2) (b := X1) (ba := by rw [g15]; exact flag01 _)
    (bb := by rw [p15 X1 (by decide), g7]; exact flag01 _) (k := fun t h16 k16 f16 r16 => WP.block_nil ?_)
  obtain ⟨F16, k16, g16, p16⟩ := k16.fx
  refine ⟨h16, ⟨V15, F16, k16, fun j hj hn => ?_, fun d a b c e => ?_, V6 3, l6, (by rw [← g6]; exact d6), by rw [o15 aDo (by decide),
    vDo], ?_⟩, ?_, ?_⟩
  · simp only [dOddArrs, invOfArrs, mulArrs, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false, not_or] at hn
    obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21,
      n22, n23, n24, n25, n26, n27, n28, n29, n30, n31⟩ := hn
    have hi : j ∉ invOfArrs := by
      simp only [invOfArrs, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26⟩
    have hm : j ∉ mulArrs := by
      simp only [mulArrs, List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨n27, n28, n29, n30, n31⟩
    rw [o15 j n12, o14 j n11, upd_ne n10, o13 j n11, o12 j hj n9 n5 n6, o11 j n9, upd_ne n10,
      o10 j hj n9 hm, o9 j hj n8 hm, o8 j n7, o6 j hj hi, c5 j hj n1 n2 n3 n4 n6]
  · rw [p16 d e, p15 d c, p7 d b, p1 d a]
  · have one6 : V6 aOne = 1 := by rw [o6 aOne (by decide) (by decide), one5]
    rw [g16, g15, p15 X1 (by decide), g7, vL14, vTwo14, g6, one6]
    by_cases a : V aL < 2 <;> by_cases b : (V aL % mE (V aE)).gcd (mE (V aE)) = 1 <;> simp [a, b]
  · exact ((((((((((((((f1.trans f2).trans f3).trans f4).trans f5).trans f6).trans f7).trans f8).trans f9).trans
      f10).trans f11).trans f12).trans f13).trans f14).trans f15).trans f16
  · have K8 : Keep bodyRegs s t8 :=
      ((((((r1.trans' r2).trans' r3).trans' r4).trans' r5).mono.trans' r6).trans' r7.mono).trans' r8.mono
    exact (((((((K8.trans' r9.mono).trans' r10).trans' r11.mono).trans' r12.mono).trans' r13.mono).trans'
      r14.mono).trans' r15.mono).trans' r16.mono

end

end VG.Proof.RsaKeyGen.PPC64LE.Key
