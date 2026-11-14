module

public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Key.Stores
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Key.Init
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Key.DMath
public import VerifiedGarbage.Proof.Rsa.PPC64LE.InvLaw
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Key.Env3
public import VerifiedGarbage.Proof.Rsa.PPC64LE.Seqs
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Key.Env2
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Key.Env
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Key.Lcm
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Key.Mul
import VerifiedGarbage.Proof.RsaKeyGen.OddInverseQuotient
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvLoads

/-! ### `RsaKeyGen.PPC64LE.Key.Primes`, which only this module used -/

section

/-!
# `vg_rsa_keygen_key` on PPC64LE: the primes

`primes_ok`: `p` and `q` ordered (`p ≥ q`), and `p - 1` and `q - 1`.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Key

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Keys (seqs copy sub3 sel aZero)
open VG.Impl.RsaKeyGen.PPC64LE.Key (nArr aDv aT aOne aP0 aQ0 aP aQ aPm aQm X0 ltS primes)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot)

/-- `a - 1`, or 0 for 0, from the borrow of `a - 1`. -/
theorem pred_sel {w a : Nat} (ha : a < 2 ^ (32 * w)) : (if a < 1 then 0 else subW w a 1) = a - 1 := by
  by_cases h : a < 1
  · simp only [h, ↓reduceIte]; omega_using [h]
  · simp only [h, ↓reduceIte]
    unfold subW
    rw [show a + 2 ^ (32 * w) - 1 = (a - 1) + 2 ^ (32 * w) by omega_using [ha, h], Nat.add_mod_right, Nat.mod_eq_of_lt (by omega_using [ha])]

section
variable {s : State} {B : Addr} {Z w : Nat} {V F : Nat → Nat}

/-- The arrays `primes` writes. -/
abbrev primesArrs : List Nat := [aT, aP, aQ, aPm, aQm]

theorem primes_eq : primes = seqs (ltS X0 aP0 aQ0 ++ ([sel aP aP0 aQ0 X0, sel aQ aQ0 aP0 X0] ++
    (ltS X0 aP aOne ++ ([sel aPm aT aZero X0] ++ (ltS X0 aQ aOne ++ [sel aQm aT aZero X0]))))) := rfl

theorem primes_ok (h : Ws s B Z w nArr) (ks : KS s.mem B w V F) (one : V aOne = 1) (zero : V aZero = 0) :
    WP isa primes s fun t => Ws t B Z w nArr ∧
      (∃ V' F', KS t.mem B w V' F' ∧ (∀ j < nArr, j ∉ primesArrs → V' j = V j) ∧
        (∀ d ∈ flags, d ≠ X0 → F' d = F d) ∧
        V' aP = (if V aP0 < V aQ0 then V aQ0 else V aP0) ∧ V' aQ = (if V aP0 < V aQ0 then V aP0 else V aQ0) ∧
        V' aPm = V' aP - 1 ∧ V' aQm = V' aQ - 1) ∧
      KK B w s.mem t.mem ∧ Keep bodyRegs s t := by
  rw [primes_eq, wp_seqs_append (by simp [ltS]) (by simp)]
  refine WP.mono (ltSE h ks (d := X0) (a := aP0) (b := aQ0)) fun t1 ⟨h1, k1, f1, r1⟩ => ?_
  obtain ⟨V1, k1, e1, o1⟩ := k1.vx
  obtain ⟨F1, k1, g1, p1⟩ := k1.fx
  rw [wp_seqs_append (by simp) (by simp [ltS])]
  change WP isa (.seq (sel aP aP0 aQ0 X0) (sel aQ aQ0 aP0 X0)) t1 _
  refine WP.seq (WP.mono (selE h1 k1 (o := aP) (a := aP0) (b := aQ0) (sl := X0) (bit := by rw [g1]; exact flag01 _))
    fun t2 ⟨h2, k2, f2, r2⟩ => ?_)
  obtain ⟨V2, k2, e2, o2⟩ := k2.vx
  refine WP.mono (selE h2 k2 (o := aQ) (a := aQ0) (b := aP0) (sl := X0) (bit := by rw [g1]; exact flag01 _))
    fun t3 ⟨h3, k3, f3, r3⟩ => ?_
  obtain ⟨V3, k3, e3, o3⟩ := k3.vx
  rw [wp_seqs_append (by simp [ltS]) (by simp)]
  refine WP.mono (ltSE h3 k3 (d := X0) (a := aP) (b := aOne)) fun t4 ⟨h4, k4, f4, r4⟩ => ?_
  obtain ⟨V4, k4, e4, o4⟩ := k4.vx
  obtain ⟨F4, k4, g4, p4⟩ := k4.fx
  rw [wp_seqs_append (by simp) (by simp [ltS])]
  change WP isa (sel aPm aT aZero X0) t4 _
  refine WP.mono (selE h4 k4 (o := aPm) (a := aT) (b := aZero) (sl := X0) (bit := by rw [g4]; exact flag01 _))
    fun t5 ⟨h5, k5, f5, r5⟩ => ?_
  obtain ⟨V5, k5, e5, o5⟩ := k5.vx
  rw [wp_seqs_append (by simp [ltS]) (by simp)]
  refine WP.mono (ltSE h5 k5 (d := X0) (a := aQ) (b := aOne)) fun t6 ⟨h6, k6, f6, r6⟩ => ?_
  obtain ⟨V6, k6, e6, o6⟩ := k6.vx
  obtain ⟨F6, k6, g6, p6⟩ := k6.fx
  change WP isa (sel aQm aT aZero X0) t6 _
  refine WP.mono (selE h6 k6 (o := aQm) (a := aT) (b := aZero) (sl := X0) (bit := by rw [g6]; exact flag01 _))
    fun t ⟨ht, kt, ft, rt⟩ => ?_
  obtain ⟨V7, kt, e7, o7⟩ := kt.vx
  have hp := ks.lt (j := aP0) (by decide)
  have hq := ks.lt (j := aQ0) (by decide)
  have vP : V7 aP = if V aP0 < V aQ0 then V aQ0 else V aP0 := by
    simp (disch := decide) only [o7, o6, o5, o4, o3, e2, g1, o1]
    split <;> simp_all
  have vQ : V7 aQ = if V aP0 < V aQ0 then V aP0 else V aQ0 := by
    simp (disch := decide) only [o7, o6, o5, o4, e3, g1, o2, o1]
    split <;> simp_all
  refine ⟨ht, ⟨V7, F6, kt, fun j hj hn => ?_, fun d _ hd => ?_, vP, vQ, ?_, ?_⟩,
    ((((((f1.trans f2).trans f3).trans f4).trans f5).trans f6).trans ft),
    ((((((r1.trans' r2).trans' r3).trans' r4).trans' r5).trans' r6).trans' rt).mono⟩
  · simp only [primesArrs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    obtain ⟨n1, n2, n3, n4, n5⟩ := hn
    rw [o7 j n5, o6 j n1, o5 j n4, o4 j n1, o3 j n3, o2 j n2, o1 j n1]
  · rw [p6 d hd, p4 d hd, p1 d hd]
  · have hP : (if V aP0 < V aQ0 then V aQ0 else V aP0) < 2 ^ (32 * w) := by split <;> with_reducible assumption
    rw [vP]
    vsimp [o7, o6, o5, o4, o3, o2, o1, e7, e6, e5, e4, e3, e2, e1, g6, g4, g1, zero, one, sel_flag]
    exact pred_sel hP
  · have hQ : (if V aP0 < V aQ0 then V aP0 else V aQ0) < 2 ^ (32 * w) := by split <;> with_reducible assumption
    rw [vQ]
    vsimp [o7, o6, o5, o4, o3, o2, o1, e7, e6, e5, e4, e3, e2, e1, g6, g4, g1, zero, one, sel_flag]
    exact pred_sel hQ

end

end VG.Proof.RsaKeyGen.PPC64LE.Key

end

end

/-! ### `RsaKeyGen.PPC64LE.Key.DPart`, which only this module used -/

section

/-! ### `RsaKeyGen.PPC64LE.Key.DOdd`, which only this module used -/

section

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
    (hnw := by omega_arith) (hfit := by omega_arith) (han := by rw [vR]; exact Nat.lt_trans (Nat.mod_lt _ (by omega_arith)) mlt)
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

end

end


/-!
# `vg_rsa_keygen_key` on PPC64LE: `d = e⁻¹ mod L`

`dOne_ok` (the case `e = 1` selected under `X4`), `dEven_ok` (the even case,
selected under `X3`), and `dPart_ok`: `X6` whether `d` exists (`okv`), and
`[aD]` the inverse when it does.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Key

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Keys (seqs copy sub3 sel eqS andS aZero bitOf)
open VG.Impl.RsaKeyGen.PPC64LE.Key (nArr aDv aT aS aOne aTwo aThree aE aL aMl aD aDo
  X0 X1 X2 X3 X4 X5 X6 X7 ltS notS andNotS selS eFlags dOdd dOne dEven dPart invOf)
open VG.Proof.Rsa.PPC64LE (InvLaw)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot)

section
variable {s : State} {B : Addr} {Z w : Nat} {V F : Nat → Nat}

theorem dOne_eq : dOne = seqs [eqS X0 aL aOne, .block (notS X7 X0 ++ (selS X6 X6 X7 X4 ++ ([] : List Instr))),
    sel aS aDo aOne X4] := rfl

/-- `e = 1`: `X7` := `L ≠ 1`, and `X6`, `[aS]` the odd case's or `e = 1`'s. -/
theorem dOne_ok (h : Ws s B Z w nArr) (ks : KS s.mem B w V F) (one : V aOne = 1) (b4 : F X4 ≤ 1)
    (b6 : F X6 ≤ 1) :
    WP isa dOne s fun t => Ws t B Z w nArr ∧
      (∃ V' F', KS t.mem B w V' F' ∧ (∀ j, j ≠ aS → V' j = V j) ∧
        (∀ d, d ≠ X0 → d ≠ X6 → d ≠ X7 → F' d = F d) ∧
        F' X6 = (if F X4 = 1 then (if V aL = 1 then 0 else 1) else F X6) ∧
        V' aS = (if F X4 = 0 then V aDo else 1)) ∧
      KK B w s.mem t.mem ∧ Keep bodyRegs s t := by
  rw [dOne_eq]
  refine WP.seq (WP.mono (eqSE h ks (d := X0) (a := aL) (b := aOne)) fun t1 ⟨h1, k1, f1, r1⟩ => ?_)
  obtain ⟨F1, k1, g1, p1⟩ := k1.fx
  refine WP.seq ?_
  refine notSE h1 k1 (d := X7) (a := X0) (ba := by rw [g1]; exact flag01 _) (k := fun t2 h2 k2 f2 r2 => ?_)
  obtain ⟨F2, k2, g2, p2⟩ := k2.fx
  have c6 : F2 X6 ≤ 1 := by rw [p2 X6 (by decide), p1 X6 (by decide)]; exact b6
  have c7 : F2 X7 ≤ 1 := by rw [g2]; omega_arith
  have c4' : F2 X4 ≤ 1 := by rw [p2 X4 (by decide), p1 X4 (by decide)]; exact b4
  refine selSE h2 k2 (d := X6) (a := X6) (b := X7) (c := X4) (ba := c6) (bb := c7) (bc := c4')
    (k := fun t3 h3 k3 f3 r3 => WP.block_nil ?_)
  obtain ⟨F3, k3, g3, p3⟩ := k3.fx
  have c4 : F3 X4 = F X4 := by rw [p3 X4 (by decide), p2 X4 (by decide), p1 X4 (by decide)]
  refine WP.mono (selE h3 k3 (o := aS) (a := aDo) (b := aOne) (sl := X4) (bit := by rw [c4]; exact b4))
    fun t ⟨ht, kt, ft, rt⟩ => ?_
  obtain ⟨V4, kt, e4, o4⟩ := kt.vx
  refine ⟨ht, ⟨V4, F3, kt, o4, fun d a b c => by rw [p3 d b, p2 d c, p1 d a], ?_, by rw [e4, c4, one]⟩,
    ((f1.trans f2).trans f3).trans ft, (((r1.trans' r2).trans' r3).trans' rt).mono⟩
  rw [g3, p2 X4 (by decide), p1 X4 (by decide), g2, p2 X6 (by decide), p1 X6 (by decide), g1, one]
  by_cases a : V aL = 1 <;> simp [a]

/-- The arrays `dEven` writes. -/
abbrev dEvenArrs : List Nat := [aT, aMl, aD] ++ invOfArrs

theorem dEven_eq : dEven = seqs (([.block (bitOf X0 aL ++ ([] : List Instr))] : List (Prog isa)) ++ (ltS X1 aL aThree ++
    ([.block (andNotS X2 X1 X0 ++ ([] : List Instr)), sel aMl aThree aL X2, invOf aE aMl VG.Impl.RsaKeyGen.PPC64LE.Key.nW, eqS X0 1 aOne,
      .block (andS X1 X2 X0 ++ (selS X6 X1 X6 X3 ++ ([] : List Instr))), sel aD 3 aS X3] : List (Prog isa)))) := rfl

/-- `e` even: `x = e⁻¹ mod mL`; `[aD]` and `X6` by whether `e` is odd. -/
theorem dEven_ok [InvLaw] (h : Ws s B Z w nArr) (ks : KS s.mem B w V F) (hw : 10 ≤ w) (hwe : w % 2 = 0)
    (he : V aE < 2 ^ 64)
    (one : V aOne = 1) (three : V aThree = 3) (zero : V aZero = 0) (b3 : F X3 = V aE % 2) (b6 : F X6 ≤ 1) :
    WP isa dEven s fun t => Ws t B Z w nArr ∧
      (∃ V' F', KS t.mem B w V' F' ∧ (∀ j < nArr, j ∉ dEvenArrs → V' j = V j) ∧
        (∀ d, d ≠ X0 → d ≠ X1 → d ≠ X2 → d ≠ X6 → F' d = F d) ∧
        (∃ x, x < mL (V aL) ∧ ((mL (V aL) : Nat) : Int) ∣ (x : Int) * V aE - Nat.gcd (V aE) (mL (V aL)) ∧
          V' aD = (if V aE % 2 = 1 then V aS else x)) ∧
        F' X6 = (if V aE % 2 = 1 then F X6 else
          if good (V aL) ∧ Nat.gcd (V aE) (mL (V aL)) = 1 then 1 else 0)) ∧
      KK B w s.mem t.mem ∧ Keep bodyRegs s t := by
  have mo := mL_odd (V aL)
  rw [dEven_eq, wp_seqs_append (by simp) (by simp [ltS])]
  change WP isa (.block (bitOf X0 aL ++ [])) s _
  refine bitOfE h ks (d := X0) (j := aL) (k := fun t1 h1 k1 f1 r1 => WP.block_nil ?_)
  obtain ⟨F1, k1, g1, p1⟩ := k1.fx
  rw [wp_seqs_append (by simp [ltS]) (by simp)]
  refine WP.mono (ltSE h1 k1 (d := X1) (a := aL) (b := aThree)) fun t2 ⟨h2, k2, f2, r2⟩ => ?_
  obtain ⟨V2, k2, e2, o2⟩ := k2.vx
  obtain ⟨F2, k2, g2, p2⟩ := k2.fx
  rw [wp_seqs_cons (by simp)]
  refine andNotSE h2 k2 (d := X2) (a := X1) (b := X0) (ba := by rw [g2]; exact flag01 _)
    (bb := by rw [p2 X0 (by decide), g1]; omega_arith) (k := fun t3 h3 k3 f3 r3 => WP.block_nil ?_)
  obtain ⟨F3, k3, g3, p3⟩ := k3.fx
  have vG : F3 X2 = if good (V aL) then 1 else 0 := by
    rw [g3, g2, p2 X0 (by decide), g1, three]
    unfold good
    rcases Nat.mod_two_eq_zero_or_one (V aL) with b | b <;> by_cases a : V aL < 3 <;> simp [a, b]
  rw [wp_seqs_cons (by simp)]
  refine WP.mono (selE h3 k3 (o := aMl) (a := aThree) (b := aL) (sl := X2) (bit := by rw [vG]; exact flag01 _))
    fun t4 ⟨h4, k4, f4, r4⟩ => ?_
  obtain ⟨V4, k4, e4, o4⟩ := k4.vx
  have vMl : V4 aMl = mL (V aL) := by
    rw [e4, vG, o2 aThree (by decide), o2 aL (by decide), three, mL]
    by_cases a : good (V aL) <;> simp [a]
  have one4 : V4 aOne = 1 := by rw [o4 aOne (by decide), o2 aOne (by decide), one]
  have zero4 : V4 aZero = 0 := by rw [o4 aZero (by decide), o2 aZero (by decide), zero]
  have vE4 : V4 aE = V aE := by rw [o4 aE (by decide), o2 aE (by decide)]
  rw [wp_seqs_cons (by simp)]
  refine WP.mono (invOfE h4 k4 hw (a := aE) (m := aMl) (hk := nW_width h4) (hn1 := by omega_arith)
    (hnw := Nat.le_refl _) (hfit := by omega_arith)
    (han := by rw [vE4]; exact Nat.lt_of_lt_of_le he (Nat.pow_le_pow_right (by decide) (by omega_arith)))
    (hmn := k4.lt (by decide)) (odd := by rw [vMl]; exact mo.1) (gt := by rw [vMl]; exact mo.2))
    fun t5 ⟨h5, ⟨V5, k5, o5, g5, d5, l5⟩, f5, r5⟩ => ?_
  simp only [vMl, vE4] at g5 d5 l5
  have one5 : V5 aOne = 1 := by rw [o5 aOne (by decide) (by decide), one4]
  rw [wp_seqs_cons (by simp)]
  refine WP.mono (eqSE h5 k5 (d := X0) (a := 1) (b := aOne)) fun t6 ⟨h6, k6, f6, r6⟩ => ?_
  obtain ⟨F6, k6, g6, p6⟩ := k6.fx
  have vX0 : F6 X0 = if Nat.gcd (V aE) (mL (V aL)) = 1 then 1 else 0 := by rw [g6, g5, one5]
  have vX2 : F6 X2 = if good (V aL) then 1 else 0 := by rw [p6 X2 (by decide), vG]
  rw [wp_seqs_cons (by simp)]
  refine andSE h6 k6 (d := X1) (a := X2) (b := X0) (ba := by rw [vX2]; exact flag01 _)
    (bb := by rw [vX0]; exact flag01 _) (k := fun t7 h7 k7 f7 r7 => ?_)
  obtain ⟨F7, k7, g7, p7⟩ := k7.fx
  have v6 : F7 X6 = F X6 := by
    rw [p7 X6 (by decide), p6 X6 (by decide), p3 X6 (by decide), p2 X6 (by decide), p1 X6 (by decide)]
  have v3 : F7 X3 = V aE % 2 := by
    rw [p7 X3 (by decide), p6 X3 (by decide), p3 X3 (by decide), p2 X3 (by decide), p1 X3 (by decide), b3]
  have c6 : F7 X6 ≤ 1 := by rw [v6]; exact b6
  have c1 : F7 X1 ≤ 1 := by rw [g7]; exact flag01 _
  have c3 : F7 X3 ≤ 1 := by rw [v3]; omega_arith
  refine selSE h7 k7 (d := X6) (a := X1) (b := X6) (c := X3) (ba := c1) (bb := c6) (bc := c3)
    (k := fun t8 h8 k8 f8 r8 => WP.block_nil ?_)
  obtain ⟨F8, k8, g8, p8⟩ := k8.fx
  have v3' : F8 X3 = V aE % 2 := by rw [p8 X3 (by decide), v3]
  refine WP.mono (selE h8 k8 (o := aD) (a := 3) (b := aS) (sl := X3) (bit := by rw [v3']; omega_arith))
    fun t ⟨ht, kt, ft, rt⟩ => ?_
  obtain ⟨V9, kt, e9, o9⟩ := kt.vx
  refine ⟨ht, ⟨V9, F8, kt, fun j hj hn => ?_, fun d a b c e => ?_, ⟨V5 3, l5, by rw [← g5]; exact d5, ?_⟩, ?_⟩,
    (((((((f1.trans f2).trans f3).trans f4).trans f5).trans f6).trans f7).trans f8).trans ft,
    ((((((((r1.trans' r2).trans' r3).trans' r4).mono.trans' r5).trans' r6.mono).trans' r7.mono).trans' r8.mono).trans'
      rt.mono)⟩
  · simp only [dEvenArrs, invOfArrs, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false, not_or] at hn
    obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17⟩ := hn
    have hi : j ∉ invOfArrs := by
      simp only [invOfArrs, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17⟩
    rw [o9 j n3, o5 j hj hi, o4 j n2, o2 j n1]
  · rw [p8 d e, p7 d b, p6 d a, p3 d c, p2 d b, p1 d a]
  · rw [e9, v3', o5 aS (by decide) (by decide), o4 aS (by decide), o2 aS (by decide)]
    rcases Nat.mod_two_eq_zero_or_one (V aE) with a | a <;> simp [a]
  · rw [g8, v3, v6, g7, vX2, vX0]
    rcases Nat.mod_two_eq_zero_or_one (V aE) with a | a <;> simp [a]

/-- The arrays `dPart` writes. -/
abbrev dPartArrs : List Nat := [aT, aS] ++ dOddArrs ++ dEvenArrs

/-- `X6` whether `d` exists, and then `[aD] = d`; `X3` `e` odd, `X5` `e < 3`. -/
theorem dPart_ok [InvLaw] (h : Ws s B Z w nArr) (ks : KS s.mem B w V F) (hw : 10 ≤ w) (hwe : w % 2 = 0)
    (he : V aE < 2 ^ 64)
    (one : V aOne = 1) (two : V aTwo = 2) (three : V aThree = 3) (zero : V aZero = 0) :
    WP isa dPart s fun t => Ws t B Z w nArr ∧
      (∃ V' F', KS t.mem B w V' F' ∧ (∀ j < nArr, j ∉ dPartArrs → V' j = V j) ∧
        (∀ d, d ≠ X0 → d ≠ X1 → d ≠ X2 → d ≠ X3 → d ≠ X4 → d ≠ X5 → d ≠ X6 → d ≠ X7 → F' d = F d) ∧
        F' X3 = V aE % 2 ∧ F' X5 = (if V aE < 3 then 1 else 0) ∧
        F' X6 = (if okv (V aE) (V aL) then 1 else 0) ∧
        (okv (V aE) (V aL) → Spec.Rsa.inverse (V aE) (V aL) = some (V' aD))) ∧
      KK B w s.mem t.mem ∧ Keep bodyRegs s t := by
  change WP isa (.seq eFlags (.seq dOdd (.seq dOne dEven))) s _
  refine WP.seq (WP.mono (eFlags_ok h ks one three) fun t1 ⟨h1, ⟨V1, F1, k1, o1, p1, x3, x4, x5⟩, f1, r1⟩ => ?_)
  have one1 : V1 aOne = 1 := by rw [o1 _ (by decide), one]
  have two1 : V1 aTwo = 2 := by rw [o1 _ (by decide), two]
  have three1 : V1 aThree = 3 := by rw [o1 _ (by decide), three]
  have zero1 : V1 aZero = 0 := by rw [o1 _ (by decide), zero]
  have e1 : V1 aE = V aE := o1 _ (by decide)
  have l1 : V1 aL = V aL := o1 _ (by decide)
  refine WP.seq (WP.mono (dOdd_ok h1 k1 hw (by rw [e1]; exact he) one1 two1 three1 zero1 (by rw [x3, e1])
    (by rw [x5, e1])) fun t2 ⟨h2, ⟨V2, F2, k2, o2, p2, x, xl, xd, vDo, x6⟩, f2, r2⟩ => ?_)
  simp only [e1, l1] at xl xd vDo x6
  have one2 : V2 aOne = 1 := by rw [o2 _ (by decide) (by decide), one1]
  have three2 : V2 aThree = 3 := by rw [o2 _ (by decide) (by decide), three1]
  have zero2 : V2 aZero = 0 := by rw [o2 _ (by decide) (by decide), zero1]
  have e2 : V2 aE = V aE := by rw [o2 _ (by decide) (by decide), e1]
  have l2 : V2 aL = V aL := by rw [o2 _ (by decide) (by decide), l1]
  have y4 : F2 X4 = if V aE = 1 then 1 else 0 := by rw [p2 X4 (by decide) (by decide) (by decide) (by decide), x4]
  have y3 : F2 X3 = V aE % 2 := by rw [p2 X3 (by decide) (by decide) (by decide) (by decide), x3]
  have y5 : F2 X5 = if V aE < 3 then 1 else 0 := by rw [p2 X5 (by decide) (by decide) (by decide) (by decide), x5]
  refine WP.seq (WP.mono (dOne_ok h2 k2 one2 (by rw [y4]; exact flag01 _) (by rw [x6]; exact flag01 _))
    fun t3 ⟨h3, ⟨V3, F3, k3, o3, p3, z6, vS⟩, f3, r3⟩ => ?_)
  have one3 : V3 aOne = 1 := by rw [o3 _ (by decide), one2]
  have three3 : V3 aThree = 3 := by rw [o3 _ (by decide), three2]
  have zero3 : V3 aZero = 0 := by rw [o3 _ (by decide), zero2]
  have e3 : V3 aE = V aE := by rw [o3 _ (by decide), e2]
  have l3 : V3 aL = V aL := by rw [o3 _ (by decide), l2]
  have w3 : F3 X3 = V aE % 2 := by rw [p3 X3 (by decide) (by decide) (by decide), y3]
  refine WP.mono (dEven_ok h3 k3 hw hwe (by rw [e3]; exact he) one3 three3 zero3 (by rw [w3, e3]) (by rw [z6, x6]; split <;> split <;> omega_arith))
    fun t ⟨ht, ⟨V4, F4, k4, o4, p4, ⟨x', xl', xd', vD⟩, z6'⟩, f4, r4⟩ => ?_
  simp only [e3, l3] at xl' xd' vD z6'
  refine ⟨ht, ⟨V4, F4, k4, fun j hj hn => ?_, fun d a b c d3 d4 d5 d6 d7 => ?_, ?_, ?_, ?_, ?_⟩,
    ((f1.trans f2).trans f3).trans f4, (((r1.trans' r2).trans' r3).trans' r4)⟩
  · have n4 : j ∉ dEvenArrs := fun m => hn (List.mem_append_right _ m)
    have n3 : j ∉ dOddArrs := fun m => hn (List.mem_append_left _ (List.mem_append_right _ m))
    have n12 : j ≠ aT ∧ j ≠ aS := ⟨fun e => hn (by rw [e]; decide), fun e => hn (by rw [e]; decide)⟩
    rw [o4 j hj n4, o3 j n12.2, o2 j hj n3, o1 j n12.1]
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
    rw [vD, vS, y4]
    rcases Nat.mod_two_eq_zero_or_one (V aE) with a | a
    · have ok' : good (V aL) ∧ Nat.gcd (V aE) (mL (V aL)) = 1 := by
        rcases ok with ⟨a', _⟩ | ⟨_, g1, g2⟩
        · omega_arith
        · exact ⟨g1, g2⟩
      simp only [a, show ¬ (0 = 1) by decide, ↓reduceIte]
      have g := ok'.2
      rw [mL_of ok'.1] at g xd' xl'
      rw [g] at xd'
      exact inverse_even' ok'.1 (by exact_mod_cast xd') xl'
    · simp only [a, ↓reduceIte]
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

end

end VG.Proof.RsaKeyGen.PPC64LE.Key

end

end

/-! ### `RsaKeyGen.PPC64LE.Key.Tail`, which only this module used -/

section

/-!
# `vg_rsa_keygen_key` on PPC64LE: from `d` to the mask

`smallPart_ok` (`X7`: `d` exists and `d ≤ 2^(8 p_len)`), `qinvPart_ok`
(`qInv` modulo `mL p`, `X0` `p` odd, `X1` `gcd(q, mL p) = 1`),
`crtPart_ok` (`dP`, `dQ`), `nPart_ok` (`n = p q`) and `maskPart_ok` (`X8`,
the mask of the checks).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Key

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Keys (seqs copy sub3 sel eqS andS aZero bitOf)
open VG.Impl.Rsa.PPC64LE.Div (div)
open VG.Impl.RsaKeyGen.PPC64LE.Key (nArr aDv aT aS aOne aThree aE aP aQ aPm aQm aD aC aC33 aTop aN aQi aMq
  aDP aDQ aQd aDt X0 X1 X2 X3 X4 X5 X6 X7 X8 ltS andNotS invOf smallPart qinvPart crtOf crtPart nPart
  maskPart cnt8)
open VG.Proof.Rsa.PPC64LE (InvLaw)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot)

/-- A flag is 1 exactly when its condition holds. -/
theorem flag_one (c : Prop) [Decidable c] : ((if c then 1 else 0 : Nat) = 1) ↔ c := by
  by_cases h : c <;> simp [h]

/-- A flag is 0 exactly when its condition fails. -/
theorem flag_zero (c : Prop) [Decidable c] : ((if c then 1 else 0 : Nat) = 0) ↔ ¬ c := by
  by_cases h : c <;> simp [h]

section
variable {s : State} {B : Addr} {Z w : Nat} {V F : Nat → Nat}

theorem smallPart_eq : smallPart = seqs (ltS X0 aD aC ++
    ([.block (andS X7 X0 X6 ++ ([] : List Instr))] : List (Prog isa))) := rfl

/-- `X7` := `X6` and `d < 2^(8 p_len) + 1`. -/
theorem smallPart_ok (h : Ws s B Z w nArr) (ks : KS s.mem B w V F) (b6 : F X6 ≤ 1) :
    WP isa smallPart s fun t => Ws t B Z w nArr ∧
      (∃ V' F', KS t.mem B w V' F' ∧ (∀ j, j ≠ aT → V' j = V j) ∧
        (∀ d, d ≠ X0 → d ≠ X7 → F' d = F d) ∧ F' X7 = (if F X6 = 1 ∧ V aD < V aC then 1 else 0)) ∧
      KK B w s.mem t.mem ∧ Keep bodyRegs s t := by
  rw [smallPart_eq, wp_seqs_append (by simp [ltS]) (by simp)]
  refine WP.mono (ltSE h ks (d := X0) (a := aD) (b := aC)) fun t1 ⟨h1, k1, f1, r1⟩ => ?_
  obtain ⟨V1, k1, e1, o1⟩ := k1.vx
  obtain ⟨F1, k1, g1, p1⟩ := k1.fx
  change WP isa (.block (andS X7 X0 X6 ++ [])) t1 _
  refine andSE h1 k1 (d := X7) (a := X0) (b := X6) (ba := by rw [g1]; exact flag01 _)
    (bb := by rw [p1 X6 (by decide)]; exact b6) (k := fun t h2 k2 f2 r2 => WP.block_nil ?_)
  obtain ⟨F2, k2, g2, p2⟩ := k2.fx
  refine ⟨h2, ⟨V1, F2, k2, o1, fun d a b => by rw [p2 d b, p1 d a], ?_⟩, f1.trans f2, (r1.trans' r2).mono⟩
  rw [g2, g1, p1 X6 (by decide)]
  by_cases a : F X6 = 1 <;> by_cases b : V aD < V aC <;> simp [a, b]

/-- The arrays `qinvPart` writes. -/
abbrev qinvArrs : List Nat := [aT, aMq, aQi] ++ invOfArrs

theorem qinvPart_eq : qinvPart = seqs (([.block (bitOf X0 aP ++ ([] : List Instr))] : List (Prog isa)) ++
    (ltS X1 aP aThree ++ ([.block (andNotS X2 X1 X0 ++ ([] : List Instr)), sel aMq aThree aP X2, invOf aQ aMq VG.Impl.RsaKeyGen.PPC64LE.Key.nP,
      eqS X1 1 aOne, copy aQi 3] : List (Prog isa)))) := rfl

/-- `qInv` modulo `mL p`, `X0` `p` odd, `X1` `gcd(q, mL p) = 1`. -/
theorem qinvPart_ok [InvLaw] (h : Ws s B Z w nArr) (ks : KS s.mem B w V F) (one : V aOne = 1) (three : V aThree = 3)
    (zero : V aZero = 0) (hw10 : 10 ≤ w) (hwe : w % 2 = 0) {L : Nat} (h22 : s.gpr .r22 = BitVec.ofNat 64 L)
    (hL' : 8 * L < 2 ^ 64) (hL4 : L % 4 = 0) (hL1 : 4 ≤ L) (hLw : L ≤ 4 * w) (hp : V aP < 2 ^ (8 * L))
    (hq : V aQ < 2 ^ (8 * L)) :
    WP isa qinvPart s fun t => Ws t B Z w nArr ∧
      (∃ V' F', KS t.mem B w V' F' ∧ (∀ j < nArr, j ∉ qinvArrs → V' j = V j) ∧
        (∀ d, d ≠ X0 → d ≠ X1 → d ≠ X2 → F' d = F d) ∧
        F' X0 = V aP % 2 ∧ F' X1 = (if Nat.gcd (V aQ) (mL (V aP)) = 1 then 1 else 0) ∧
        V' aQi < mL (V aP) ∧
        ((mL (V aP) : Nat) : Int) ∣ (V' aQi : Int) * V aQ - Nat.gcd (V aQ) (mL (V aP))) ∧
      KK B w s.mem t.mem ∧ Keep bodyRegs s t := by
  have mo := mL_odd (V aP)
  rw [qinvPart_eq, wp_seqs_append (by simp) (by simp [ltS])]
  change WP isa (.block (bitOf X0 aP ++ [])) s _
  refine bitOfE h ks (d := X0) (j := aP) (k := fun t1 h1 k1 f1 r1 => WP.block_nil ?_)
  obtain ⟨F1, k1, g1, p1⟩ := k1.fx
  rw [wp_seqs_append (by simp [ltS]) (by simp)]
  refine WP.mono (ltSE h1 k1 (d := X1) (a := aP) (b := aThree)) fun t2 ⟨h2, k2, f2, r2⟩ => ?_
  obtain ⟨V2, k2, e2, o2⟩ := k2.vx
  obtain ⟨F2, k2, g2, p2⟩ := k2.fx
  rw [wp_seqs_cons (by simp)]
  refine andNotSE h2 k2 (d := X2) (a := X1) (b := X0) (ba := by rw [g2]; exact flag01 _)
    (bb := by rw [p2 X0 (by decide), g1]; omega_arith) (k := fun t3 h3 k3 f3 r3 => WP.block_nil ?_)
  obtain ⟨F3, k3, g3, p3⟩ := k3.fx
  have vG : F3 X2 = if good (V aP) then 1 else 0 := by
    rw [g3, g2, p2 X0 (by decide), g1, three]
    unfold good
    rcases Nat.mod_two_eq_zero_or_one (V aP) with b | b <;> by_cases a : V aP < 3 <;> simp [a, b]
  rw [wp_seqs_cons (by simp)]
  refine WP.mono (selE h3 k3 (o := aMq) (a := aThree) (b := aP) (sl := X2) (bit := by rw [vG]; exact flag01 _))
    fun t4 ⟨h4, k4, f4, r4⟩ => ?_
  obtain ⟨V4, k4, e4, o4⟩ := k4.vx
  have vMq : V4 aMq = mL (V aP) := by
    rw [e4, vG, o2 aThree (by decide), o2 aP (by decide), three, mL]
    by_cases a : good (V aP) <;> simp [a]
  have one4 : V4 aOne = 1 := by rw [o4 aOne (by decide), o2 aOne (by decide), one]
  have zero4 : V4 aZero = 0 := by rw [o4 aZero (by decide), o2 aZero (by decide), zero]
  have vQ4 : V4 aQ = V aQ := by rw [o4 aQ (by decide), o2 aQ (by decide)]
  rw [wp_seqs_cons (by simp)]
  have e32 : 32 * (L / 4) = 8 * L := by omega_arith
  have K4 : Keep opsRegs s t4 := ((r1.trans' r2).trans' r3).trans' r4
  refine WP.mono (invOfE h4 k4 hw10 (a := aQ) (m := aMq)
    (hk := nP_width (by rw [K4.gpr .r22 (by decide)]; exact h22) (by omega_arith)) (hn1 := by omega_arith)
    (hnw := by omega_arith) (hfit := by omega_arith) (han := by rw [vQ4, e32]; exact hq)
    (hmn := by
      rw [vMq, e32, mL]; split
      · exact hp
      · exact Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by decide) (by omega_arith : 2 ≤ 8 * L)))
    (odd := by rw [vMq]; exact mo.1) (gt := by rw [vMq]; exact mo.2))
    fun t5 ⟨h5, ⟨V5, k5, o5, g5, d5, l5⟩, f5, r5⟩ => ?_
  simp only [vMq, vQ4] at g5 d5 l5
  have one5 : V5 aOne = 1 := by rw [o5 aOne (by decide) (by decide), one4]
  refine WP.seq (WP.mono (eqSE h5 k5 (d := X1) (a := 1) (b := aOne)) fun t6 ⟨h6, k6, f6, r6⟩ => ?_)
  obtain ⟨F6, k6, g6, p6⟩ := k6.fx
  refine WP.mono (copyE h6 k6 (o := aQi) (a := 3)) fun t ⟨ht, kt, ft, rt⟩ => ?_
  obtain ⟨V7, kt, e7, o7⟩ := kt.vx
  refine ⟨ht, ⟨V7, F6, kt, fun j hj hn => ?_, fun d a b c => ?_, ?_, by rw [g6, g5, one5], by rw [e7]; exact l5,
    by rw [e7, ← g5]; exact d5⟩, (((((f1.trans f2).trans f3).trans f4).trans f5).trans f6).trans ft,
    ((K4.mono.trans' r5).trans' r6.mono).trans' rt.mono⟩
  · simp only [qinvArrs, invOfArrs, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false, not_or] at hn
    obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17⟩ := hn
    have hi : j ∉ invOfArrs := by
      simp only [invOfArrs, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17⟩
    rw [o7 j n3, o5 j hj hi, o4 j n2, o2 j n1]
  · rw [p6 d b, p3 d c, p2 d b, p1 d a]
  · rw [p6 X0 (by decide), p3 X0 (by decide), p2 X0 (by decide), g1]

/-- The arrays `crtOf o` writes. -/
abbrev crtArrs (o : Nat) : List Nat := [aS, aQd, aDv, aDt, o]

/-- `[o] := d mod [j]`, by 1 for `[j] = 0`. -/
theorem crtOf_ok (h : Ws s B Z w nArr) (ks : KS s.mem B w V F) {o j : Nat} (ho : o < nArr := by decide)
    (hj : j < nArr := by decide) (hjS : aS ≠ j := by decide) (hoQ : aQd ≠ o := by decide)
    (hoT : o ≠ aDt := by decide) (hoD : o ≠ aDv := by decide) (one : V aOne = 1) (zero : V aZero = 0) :
    WP isa (crtOf o j) s fun t => Ws t B Z w nArr ∧
      (∃ V' F', KS t.mem B w V' F' ∧ (∀ k < nArr, k ∉ crtArrs o → V' k = V k) ∧
        (∀ d, d ≠ X2 → F' d = F d) ∧ V' o = V aD % (if V j = 0 then 1 else V j)) ∧
      KK B w s.mem t.mem ∧ Keep bodyRegs s t := by
  change WP isa (.seq (eqS X2 j aZero) (.seq (sel aS j aOne X2) (.seq (copy aQd aD)
    (.seq (copy aDv aS) (div aQd o aDv aDt))))) s _
  refine WP.seq (WP.mono (eqSE h ks (d := X2) (a := j) (b := aZero) (ha := hj)) fun t1 ⟨h1, k1, f1, r1⟩ => ?_)
  obtain ⟨F1, k1, g1, p1⟩ := k1.fx
  refine WP.seq (WP.mono (selE h1 k1 (o := aS) (a := j) (b := aOne) (sl := X2) (ha := hj) (hoa := hjS)
    (bit := by rw [g1]; exact flag01 _)) fun t2 ⟨h2, k2, f2, r2⟩ => ?_)
  obtain ⟨V2, k2, e2, o2⟩ := k2.vx
  refine WP.seq (WP.mono (copyE h2 k2 (o := aQd) (a := aD)) fun t3 ⟨h3, k3, f3, r3⟩ => ?_)
  obtain ⟨V3, k3, e3, o3⟩ := k3.vx
  refine WP.seq (WP.mono (copyE h3 k3 (o := aDv) (a := aS)) fun t4 ⟨h4, k4, f4, r4⟩ => ?_)
  obtain ⟨V4, k4, e4, o4⟩ := k4.vx
  refine WP.mono (divE h4 k4 (q := aQd) (r := o) (t := aDt) (hr := ho) (hqr := hoQ) (hrt := hoT) (hrd := hoD))
    fun t ⟨ht, ⟨V5, k5, o5, e5⟩, f5, r5⟩ => ?_
  have vS : V2 aS = if V j = 0 then 1 else V j := by
    rw [e2, g1, zero, sel_flag, one]
  have vDv : V4 aDv = if V j = 0 then 1 else V j := by
    rw [e4, o3 aS (by decide), vS]
  have pos : 0 < V4 aDv := by rw [vDv]; split <;> omega_arith
  refine ⟨ht, ⟨V5, F1, k5, fun k hk hn => ?_, p1, ?_⟩, (((f1.trans f2).trans f3).trans f4).trans f5,
    ((((r1.trans' r2).trans' r3).trans' r4).trans' r5).mono⟩
  · simp only [crtArrs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    obtain ⟨n1, n2, n3, n4, n5⟩ := hn
    rw [o5 k hk n2 n5 n4, o4 k n3, o3 k n2, o2 k n1]
  · rw [(e5 pos).2, vDv, o4 aQd (by decide), e3, o2 aD (by decide)]

/-- The arrays `crtPart` writes. -/
abbrev crtPartArrs : List Nat := [aS, aQd, aDv, aDt, aDP, aDQ]

/-- `dP` and `dQ`. -/
theorem crtPart_ok (h : Ws s B Z w nArr) (ks : KS s.mem B w V F) (one : V aOne = 1) (zero : V aZero = 0) :
    WP isa crtPart s fun t => Ws t B Z w nArr ∧
      (∃ V' F', KS t.mem B w V' F' ∧ (∀ k < nArr, k ∉ crtPartArrs → V' k = V k) ∧
        (∀ d, d ≠ X2 → F' d = F d) ∧ V' aDP = V aD % (if V aPm = 0 then 1 else V aPm) ∧
        V' aDQ = V aD % (if V aQm = 0 then 1 else V aQm)) ∧
      KK B w s.mem t.mem ∧ Keep bodyRegs s t := by
  change WP isa (.seq (crtOf aDP aPm) (crtOf aDQ aQm)) s _
  refine WP.seq (WP.mono (crtOf_ok h ks (o := aDP) (j := aPm) (one := one) (zero := zero))
    fun t1 ⟨h1, ⟨V1, F1, k1, o1, p1, e1⟩, f1, r1⟩ => ?_)
  have c1 : ∀ k < nArr, k ∉ crtArrs aDP → V1 k = V k := o1
  refine WP.mono (crtOf_ok h1 k1 (o := aDQ) (j := aQm) (one := by rw [c1 _ (by decide) (by decide), one])
    (zero := by rw [c1 _ (by decide) (by decide), zero])) fun t ⟨ht, ⟨V2, F2, k2, o2, p2, e2⟩, f2, r2⟩ => ?_
  refine ⟨ht, ⟨V2, F2, k2, fun k hk hn => ?_, fun d a => by rw [p2 d a, p1 d a], ?_, ?_⟩, f1.trans f2,
    r1.trans' r2⟩
  · simp only [crtPartArrs, crtArrs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn o1 o2
    obtain ⟨n1, n2, n3, n4, n5, n6⟩ := hn
    rw [o2 k hk ⟨n1, n2, n3, n4, n6⟩, o1 k hk ⟨n1, n2, n3, n4, n5⟩]
  · rw [o2 aDP (by decide) (by decide), e1]
  · rw [e2, o1 aD (by decide) (by decide), o1 aQm (by decide) (by decide)]

/-- `n = p q`, for `p, q < 2^(8 L)` and `2^(32 w) = 2^(16 L)`. -/
theorem nPart_ok (h : Ws s B Z w nArr) (ks : KS s.mem B w V F) {L : Nat}
    (h22 : s.gpr .r22 = BitVec.ofNat 64 L) (hL : 0 < L) (hL' : 8 * L < 2 ^ 64) (hw : 32 * w = 16 * L)
    (hp : V aP < 2 ^ (8 * L)) (hq : V aQ < 2 ^ (8 * L)) (zero : V aZero = 0) :
    WP isa nPart s fun t => Ws t B Z w nArr ∧
      (∃ V', KS t.mem B w V' F ∧ (∀ j < nArr, j ≠ aN → j ∉ mulArrs → V' j = V j) ∧ V' aN = V aP * V aQ) ∧
      KK B w s.mem t.mem ∧ Keep bodyRegs s t := by
  refine WP.mono (mulToE h ks (o := aN) (a := aP) (b := aQ) (K := 8 * L) (k := cnt8) (hK := by omega_arith)
    (hK' := hL') (hk := fun u hu => cnt8_ok hL' u (by rw [hu, h22])) (hZ := zero))
    fun t ⟨ht, ⟨V', kt, ot, et⟩, ft, rt⟩ => ⟨ht, ⟨V', kt, ot, ?_⟩, ft, rt⟩
  have hpq : V aP * V aQ < 2 ^ (32 * w) := by
    rw [hw, show 16 * L = 8 * L + 8 * L by omega_arith, Nat.pow_add]
    exact Nat.mul_lt_mul'' hp hq
  rw [et, Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt hpq]

theorem maskPart_eq : maskPart = seqs (ltS X2 aN aTop ++ (([.block (andNotS X8 X2 X6 ++ (andS X8 X8 X1 ++
    (andS X8 X8 X0 ++ (bitOf X2 aQ ++ (andS X8 X8 X2 ++ (andS X8 X8 X3 ++ ([] : List Instr)))))))] : List (Prog isa)) ++
    (ltS X2 aE aC33 ++ ([.block (andNotS X4 X5 X2 ++ (andS X8 X8 X4 ++ (andNotS X8 X7 X8 ++ ([] : List Instr))))] :
      List (Prog isa))))) := rfl

/-- `X8` := not small, and `n ≥ 2^(16 p_len - 1)`, `d` exists, `gcd(q, mL p) = 1`,
`p` and `q` odd, `e` odd, at least 3 and below `2^33`. -/
theorem maskPart_ok (h : Ws s B Z w nArr) (ks : KS s.mem B w V F) (b0 : F X0 ≤ 1) (b1 : F X1 ≤ 1)
    (b3 : F X3 ≤ 1) (b5 : F X5 ≤ 1) (b6 : F X6 ≤ 1) (b7 : F X7 ≤ 1) :
    WP isa maskPart s fun t => Ws t B Z w nArr ∧
      (∃ V' F', KS t.mem B w V' F' ∧ (∀ j, j ≠ aT → V' j = V j) ∧
        (∀ d, d ≠ X2 → d ≠ X4 → d ≠ X8 → F' d = F d) ∧
        F' X8 = (if F X7 = 0 ∧ ¬ V aN < V aTop ∧ F X6 = 1 ∧ F X1 = 1 ∧ F X0 = 1 ∧ V aQ % 2 = 1 ∧
          F X3 = 1 ∧ F X5 = 0 ∧ V aE < V aC33 then 1 else 0)) ∧
      KK B w s.mem t.mem ∧ Keep bodyRegs s t := by
  rw [maskPart_eq, wp_seqs_append (by simp [ltS]) (by simp)]
  refine WP.mono (ltSE h ks (d := X2) (a := aN) (b := aTop)) fun t1 ⟨h1, k1, f1, r1⟩ => ?_
  obtain ⟨V1, k1, e1, o1⟩ := k1.vx
  obtain ⟨F1, k1, g1, p1⟩ := k1.fx
  rw [wp_seqs_append (by simp) (by simp [ltS])]
  change WP isa (.block _) t1 _
  refine andNotSE h1 k1 (d := X8) (a := X2) (b := X6) (ba := by rw [g1]; exact flag01 _)
    (bb := by rw [p1 X6 (by decide)]; exact b6) (k := fun t2 h2 k2 f2 r2 => ?_)
  obtain ⟨F2, k2, g2, p2⟩ := k2.fx
  refine andSE h2 k2 (d := X8) (a := X8) (b := X1) (ba := by rw [g2]; exact flag01 _)
    (bb := by rw [p2 X1 (by decide), p1 X1 (by decide)]; exact b1) (k := fun t3 h3 k3 f3 r3 => ?_)
  obtain ⟨F3, k3, g3, p3⟩ := k3.fx
  refine andSE h3 k3 (d := X8) (a := X8) (b := X0) (ba := by rw [g3]; exact flag01 _)
    (bb := by rw [p3 X0 (by decide), p2 X0 (by decide), p1 X0 (by decide)]; exact b0)
    (k := fun t4 h4 k4 f4 r4 => ?_)
  obtain ⟨F4, k4, g4, p4⟩ := k4.fx
  refine bitOfE h4 k4 (d := X2) (j := aQ) (k := fun t5 h5 k5 f5 r5 => ?_)
  obtain ⟨F5, k5, g5, p5⟩ := k5.fx
  refine andSE h5 k5 (d := X8) (a := X8) (b := X2) (ba := by rw [p5 X8 (by decide), g4]; exact flag01 _)
    (bb := by rw [g5]; omega_arith) (k := fun t6 h6 k6 f6 r6 => ?_)
  obtain ⟨F6, k6, g6, p6⟩ := k6.fx
  refine andSE h6 k6 (d := X8) (a := X8) (b := X3) (ba := by rw [g6]; exact flag01 _)
    (bb := by rw [p6 X3 (by decide), p5 X3 (by decide), p4 X3 (by decide), p3 X3 (by decide), p2 X3 (by decide),
      p1 X3 (by decide)]; exact b3) (k := fun t7 h7 k7 f7 r7 => WP.block_nil ?_)
  obtain ⟨F7, k7, g7, p7⟩ := k7.fx
  rw [wp_seqs_append (by simp [ltS]) (by simp)]
  refine WP.mono (ltSE h7 k7 (d := X2) (a := aE) (b := aC33)) fun t8 ⟨h8, k8, f8, r8⟩ => ?_
  obtain ⟨V8, k8, e8, o8⟩ := k8.vx
  obtain ⟨F8, k8, g8, p8⟩ := k8.fx
  change WP isa (.block _) t8 _
  have c5 : F8 X5 = F X5 := by vsimp [p8, p7, p6, p5, p4, p3, p2, p1]
  have c7 : F8 X7 = F X7 := by vsimp [p8, p7, p6, p5, p4, p3, p2, p1]
  refine andNotSE h8 k8 (d := X4) (a := X5) (b := X2) (ba := by rw [c5]; exact b5)
    (bb := by rw [g8]; exact flag01 _) (k := fun t9 h9 k9 f9 r9 => ?_)
  obtain ⟨F9, k9, g9, p9⟩ := k9.fx
  refine andSE h9 k9 (d := X8) (a := X8) (b := X4) (ba := by rw [p9 X8 (by decide), p8 X8 (by decide), g7]; exact flag01 _)
    (bb := by rw [g9]; exact flag01 _) (k := fun t10 h10 k10 f10 r10 => ?_)
  obtain ⟨F10, k10, g10, p10⟩ := k10.fx
  refine andNotSE h10 k10 (d := X8) (a := X7) (b := X8)
    (ba := by rw [p10 X7 (by decide), p9 X7 (by decide), c7]; exact b7)
    (bb := by rw [g10]; exact flag01 _) (k := fun t h11 k11 f11 r11 => WP.block_nil ?_)
  obtain ⟨F11, k11, g11, p11⟩ := k11.fx
  refine ⟨h11, ⟨V8, F11, k11, fun j a => by rw [o8 j a, o1 j a], fun d a b c => ?_, ?_⟩,
    (((((((((f1.trans f2).trans f3).trans f4).trans f5).trans f6).trans f7).trans f8).trans f9).trans f10).trans
      f11,
    ((((((((((r1.trans' r2).trans' r3).trans' r4).trans' r5).trans' r6).trans' r7).trans' r8).trans' r9).trans'
      r10).trans' r11).mono⟩
  · rw [p11 d c, p10 d c, p9 d b, p8 d a, p7 d c, p6 d c, p5 d a, p4 d c, p3 d c, p2 d c, p1 d a]
  · vsimp [g11, p11, g10, p10, g9, p9, g8, p8, g7, p7, g6, p6, g5, p5, g4, p4, g3, p3, g2, p2, g1, p1, o1,
      flag_one, flag_zero, and_assoc]

end

end VG.Proof.RsaKeyGen.PPC64LE.Key

end

end


/-!
# `vg_rsa_keygen_key` on PPC64LE: the body

`body_ok`: from the entry's state, the phases in order (`Init.lean`,
`Primes.lean`, `Lcm.lean`, `DPart.lean`, `Tail.lean`, `Stores.lean`): the
status `2 small + mask` in `r3` and the seven outputs under the mask, with
the arrays they come from holding `n = p q`, `d`, `p`, `q`, `dP`, `dQ` and
`qInv` (`BodyPost`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Key

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Keys (seqs aZero)
open VG.Impl.RsaKeyGen.PPC64LE.Key (body setup loads consts primes lcmPart dPart smallPart qinvPart crtPart
  nPart maskPart stores nArr aOne aTwo aThree aTop aC aC33 aE aP0 aQ0 aP aQ aPm aQm aL aD aDP aDQ aQi aN
  X0 X1 X3 X5 X6 X7 X8)
open VG.Proof.Rsa.PPC64LE (InvLaw)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot)

/-- The primes, ordered, and `L = lcm(p - 1, q - 1)`. -/
abbrev kP (s0 : State) : Nat := if pIn s0 < qIn s0 then qIn s0 else pIn s0
abbrev kQ (s0 : State) : Nat := if pIn s0 < qIn s0 then pIn s0 else qIn s0
abbrev kLc (s0 : State) : Nat := Nat.lcm (kP s0 - 1) (kQ s0 - 1)

/-- `d` exists and is at most `2^(8 p_len)`: the status 2. -/
def kSmall (s0 : State) (D : Nat) : Prop := okv (eIn s0) (kLc s0) ∧ D < 2 ^ (8 * kL s0) + 1

/-- The mask under which the outputs are written. -/
def kMask (s0 : State) (D : Nat) : Prop :=
  ¬ kSmall s0 D ∧ ¬ kP s0 * kQ s0 < 2 ^ (16 * kL s0 - 1) ∧ okv (eIn s0) (kLc s0) ∧
    Nat.gcd (kQ s0) (mL (kP s0)) = 1 ∧ kP s0 % 2 = 1 ∧ kQ s0 % 2 = 1 ∧ eIn s0 % 2 = 1 ∧ ¬ eIn s0 < 3 ∧
    eIn s0 < 2 ^ 33

instance (s0 : State) (D : Nat) : Decidable (kSmall s0 D) := by unfold kSmall; infer_instance
instance (s0 : State) (D : Nat) : Decidable (kMask s0 D) := by unfold kMask; infer_instance

/-- The registers the body changes. -/
abbrev bodyAll : List Reg := [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .r29, .r30]

/-- What the body establishes. -/
def BodyPost (s0 t : State) : Prop :=
  ∃ m D x, Fr s0 m t ∧ D < 2 ^ (32 * kW s0) ∧ x < mL (kP s0) ∧
    ((mL (kP s0) : Nat) : Int) ∣ (x : Int) * kQ s0 - Nat.gcd (kQ s0) (mL (kP s0)) ∧
    (okv (eIn s0) (kLc s0) → Spec.Rsa.inverse (eIn s0) (kLc s0) = some D) ∧
    t.gpr .r3 = BitVec.ofNat 64 (2 * (if kSmall s0 D then 1 else 0) + (if kMask s0 D then 1 else 0)) ∧
    Outs s0 m (decide (kMask s0 D)) t.mem (outList s0) ∧
    num m (kB s0) (kW s0) aN = kP s0 * kQ s0 ∧ num m (kB s0) (kW s0) aD = D ∧
    num m (kB s0) (kW s0) aP = kP s0 ∧ num m (kB s0) (kW s0) aQ = kQ s0 ∧
    num m (kB s0) (kW s0) aDP = D % (if kP s0 - 1 = 0 then 1 else kP s0 - 1) ∧
    num m (kB s0) (kW s0) aDQ = D % (if kQ s0 - 1 = 0 then 1 else kQ s0 - 1) ∧
    num m (kB s0) (kW s0) aQi = x

theorem body_eq : body = seqs (setup :: loads :: (consts ++ [primes, lcmPart, dPart, smallPart, qinvPart,
    crtPart, nPart, maskPart, stores])) := rfl

theorem flag_le {c : Prop} [Decidable c] {x : Nat} (h : x = if c then 1 else 0) : x ≤ 1 := by
  rw [h]; exact flag01 _

theorem slot_flag {m : Mem} {B : Addr} {d x : Nat} {c : Prop} [Decidable c] (h : slot m B d = x)
    (hx : x = if c then 1 else 0) : slot m B d = if decide c then 1 else 0 := by
  rw [h, hx]; by_cases hc : c <;> simp [hc]

/-- The body up to `L` (`lcmPart`, which calls the inverse). -/
abbrev bodyL : List (Prog isa) := setup :: loads :: (consts ++ [primes, lcmPart])

/-- From `qInv` (`qinvPart`, which calls the inverse) on. -/
abbrev bodyT : List (Prog isa) := [crtPart, nPart, maskPart, stores]

/-- `w` and the stride in `r29` and `r30`. -/
def WReg (s0 t : State) : Prop :=
  t.gpr .r29 = BitVec.ofNat 64 (kW s0) ∧ t.gpr .r30 = BitVec.ofNat 64 (VG.Proof.Rsa.KeyWorkspace.S (kW s0))

/-- `body_ok` with the base, the arguments and `WReg` after each phase that calls the
inverse (`lcmPart`, `dPart`, `qinvPart`), which reloads the arguments'
registers from memory: where the constant-time proof (`CT.lean`) pins them
again. -/
theorem body_cut_ok [InvLaw] {s0 s : State} (h : Base s0 s) (ha : Args s0 s) :
    WP isa (seqs bodyL) s fun t5 => Base s0 t5 ∧ Args s0 t5 ∧ WReg s0 t5 ∧
      WP isa dPart t5 fun t6 => Base s0 t6 ∧ Args s0 t6 ∧ WReg s0 t6 ∧
      WP isa (seqs [smallPart, qinvPart]) t6 fun t8 => Base s0 t8 ∧ Args s0 t8 ∧ WReg s0 t8 ∧
      WP isa (seqs bodyT) t8 fun t => BodyPost s0 t ∧ Keep bodyAll s t := by
  have p := kpre h.pre
  obtain ⟨-, hw16, hw256, hlw, h4⟩ := pre_ws h.pre
  have l1 := p.l1
  have l2 := p.l2
  have el8 := p.el8
  have hpl : pIn s0 < 2 ^ (8 * kL s0) := by
    have := VG.Proof.Bignum.os2ip_lt (Spec.Rsa.bytesAt s0.mem (s0.gpr .r7) (kL s0))
    rw [show (Spec.Rsa.bytesAt s0.mem (s0.gpr .r7) (kL s0)).length = kL s0 by simp [Spec.Rsa.bytesAt]] at this
    rw [Nat.pow_mul]; exact this
  have hql : qIn s0 < 2 ^ (8 * kL s0) := by
    have := VG.Proof.Bignum.os2ip_lt (Spec.Rsa.bytesAt s0.mem (s0.gpr .r9) (kL s0))
    rw [show (Spec.Rsa.bytesAt s0.mem (s0.gpr .r9) (kL s0)).length = kL s0 by simp [Spec.Rsa.bytesAt]] at this
    rw [Nat.pow_mul]; exact this
  have hel : eIn s0 < 2 ^ 64 := by
    have := VG.Proof.Bignum.os2ip_lt (Spec.Rsa.bytesAt s0.mem (PPC64LE.stackArg s0 6) (PPC64LE.stackArg s0 7).toNat)
    simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range] at this
    exact Nat.lt_of_lt_of_le this (by
      rw [show (2 : Nat) ^ 64 = 256 ^ 8 by decide]; exact Nat.pow_le_pow_right (by decide) el8)
  have hW : 32 * kW s0 = 16 * kL s0 := by omega_arith
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (setup_ok h ha.r22) fun t1 ⟨b1, w1, k1, r1⟩ => ?_
  have a1 := ha.of_keep r1
  rw [wp_seqs_cons (by simp [consts])]
  refine WP.mono (loads_ok b1 a1 w1 k1 rfl rfl rfl) fun t2 ⟨b2, w2, ⟨V2, k2, o2, eP, eQ, eE⟩, r2⟩ => ?_
  have a2 := a1.of_keep r2
  rw [wp_seqs_append (by simp [consts]) (List.cons_ne_nil _ _)]
  refine WP.mono (consts_ok b2 a2 w2 k2 (by rw [o2 _ (by decide) (by decide) (by decide)])
    (by rw [o2 _ (by decide) (by decide) (by decide)]) (by rw [o2 _ (by decide) (by decide) (by decide)])
    (by rw [o2 _ (by decide) (by decide) (by decide)]) (by rw [o2 _ (by decide) (by decide) (by decide)])
    (by rw [o2 _ (by decide) (by decide) (by decide)]))
    fun t3 ⟨b3, w3, ⟨V3, k3, o3, one3, two3, three3, c3, c33, top3⟩, r3⟩ => ?_
  have a3 := a2.of_keep r3
  have zero3 : V3 aZero = 0 := by
    rw [o3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      o2 _ (by decide) (by decide) (by decide)]
  have p3 : V3 aP0 = pIn s0 := by
    rw [o3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), eP]
  have q3 : V3 aQ0 = qIn s0 := by
    rw [o3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), eQ]
  have e3 : V3 aE = eIn s0 := by
    rw [o3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), eE]
  -- The primes.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (primes_ok w3 k3 one3 zero3) fun t4 ⟨w4, ⟨V4, F4, k4, o4, p4, vP, vQ, vPm, vQm⟩, f4, r4⟩ => ?_
  have b4 := b3.of_phase f4 r4
  have a4 := a3.of_keep r4
  rw [p3, q3] at vP vQ
  rw [vP] at vPm
  rw [vQ] at vQm
  have hP : kP s0 < 2 ^ (8 * kL s0) := by simp only [kP]; split <;> with_reducible assumption
  have hQ : kQ s0 < 2 ^ (8 * kL s0) := by simp only [kQ]; split <;> with_reducible assumption
  -- `L`.
  have h22 : t4.gpr .r22 = BitVec.ofNat 64 (kL s0) := by
    rw [a4.r22]; exact VG.Proof.Rsa.PPC64LE.CrtValues.ofNat_toNat64 _
  refine WP.mono (lcmPart_ok w4 k4 h22 (by omega_arith) (by omega_arith) hW (by omega_arith) h4 (by rw [vPm]; exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) hP)
    (by rw [vQm]; exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) hQ)
    (by vsimp [o4, one3]) (by vsimp [o4, o3, two3]) (by vsimp [o4, three3]) (by vsimp [o4, zero3]))
    fun t5 ⟨w5, ⟨V5, F5, k5, o5, p5, vL⟩, f5, r5⟩ => ?_
  have b5 := b4.of_phase f5 r5
  have a5 := a4.of_keep r5
  rw [vPm, vQm] at vL
  refine ⟨b5, a5, ⟨w5.r29, w5.r30⟩, ?_⟩
  -- `d`.
  refine WP.mono (dPart_ok w5 k5 (by omega_arith) (by omega_arith) (by vsimp [o5, o4, e3]; exact hel) (by vsimp [o5, o4, one3])
    (by vsimp [o5, o4, two3]) (by vsimp [o5, o4, three3]) (by vsimp [o5, o4, zero3]))
    fun t6 ⟨w6, ⟨V6, F6, k6, o6, p6, x3, x5, x6, vD⟩, f6, r6⟩ => ?_
  have b6 := b5.of_phase f6 r6
  have a6 := a5.of_keep r6
  have eE5 : V5 aE = eIn s0 := by vsimp [o5, o4, e3]
  simp only [eE5, vL] at x3 x5 x6 vD
  refine ⟨b6, a6, ⟨w6.r29, w6.r30⟩, ?_⟩
  -- Small.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (smallPart_ok w6 k6 (flag_le x6)) fun t7 ⟨w7, ⟨V7, F7, k7, o7, p7, x7⟩, f7, r7⟩ => ?_
  have b7 := b6.of_phase f7 r7
  have a7 := a6.of_keep r7
  have vC6 : V6 aC = 2 ^ (8 * kL s0) + 1 := by vsimp [o6, o5, o4, c3]
  simp only [x6, vC6] at x7
  -- `qInv`.
  have vP7 : V7 aP = kP s0 := by vsimp [o7, o6, o5, vP]
  have vQ7 : V7 aQ = kQ s0 := by vsimp [o7, o6, o5, vQ]
  refine WP.mono (qinvPart_ok w7 k7 (by vsimp [o7, o6, o5, o4, one3]) (by vsimp [o7, o6, o5, o4, three3])
    (by vsimp [o7, o6, o5, o4, zero3]) (by omega_arith) (by omega_arith) (by rw [a7.r22, ← a4.r22]; exact h22)
    (by omega_arith) h4
    (by omega_arith) (by omega_arith) (by rw [vP7]; exact hP) (by rw [vQ7]; exact hQ)) fun t8 ⟨w8, ⟨V8, F8, k8, o8, p8, y0, y1, xl, xd⟩, f8, r8⟩ => ?_
  have b8 := b7.of_phase f8 r8
  have a8 := a7.of_keep r8
  simp only [vP7, vQ7] at y0 y1 xl xd
  refine ⟨b8, a8, ⟨w8.r29, w8.r30⟩, ?_⟩
  -- `dP`, `dQ`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (crtPart_ok w8 k8 (by vsimp [o8, o7, o6, o5, o4, one3]) (by vsimp [o8, o7, o6, o5, o4, zero3]))
    fun t9 ⟨w9, ⟨V9, F9, k9, o9, p9, vDP, vDQ⟩, f9, r9⟩ => ?_
  have b9 := b8.of_phase f9 r9
  have a9 := a8.of_keep r9
  -- `n`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have vP9 : V9 aP = kP s0 := by vsimp [o9, o8, vP7]
  have vQ9 : V9 aQ = kQ s0 := by vsimp [o9, o8, vQ7]
  refine WP.mono (nPart_ok w9 k9 (by rw [a9.r22, ← a4.r22]; exact h22) (by omega_arith) (by omega_arith) hW
    (by rw [vP9]; exact hP) (by rw [vQ9]; exact hQ) (by vsimp [o9, o8, o7, o6, o5, o4, zero3]))
    fun t10 ⟨w10, ⟨V10, k10, o10, vN⟩, f10, r10⟩ => ?_
  have b10 := b9.of_phase f10 r10
  have a10 := a9.of_keep r10
  simp only [vP9, vQ9] at vN
  -- The mask.
  have g0 : F9 X0 = kP s0 % 2 := by vsimp [p9, y0]
  have g1 : F9 X1 = if Nat.gcd (kQ s0) (mL (kP s0)) = 1 then 1 else 0 := by vsimp [p9, y1]
  have g3 : F9 X3 = eIn s0 % 2 := by vsimp [p9, p8, p7, x3]
  have g5 : F9 X5 = if eIn s0 < 3 then 1 else 0 := by vsimp [p9, p8, p7, x5]
  have g6 : F9 X6 = if okv (eIn s0) (kLc s0) then 1 else 0 := by vsimp [p9, p8, p7, x6]
  have g7 : F9 X7 = if (if okv (eIn s0) (kLc s0) then 1 else 0) = 1 ∧ V6 aD < 2 ^ (8 * kL s0) + 1 then 1 else 0 := by
    vsimp [p9, p8, x7]
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (maskPart_ok w10 k10 (by rw [g0]; omega_arith) (flag_le g1) (by rw [g3]; omega_arith) (flag_le g5)
    (flag_le g6) (flag_le g7)) fun t11 ⟨w11, ⟨V11, F11, k11, o11, p11, x8⟩, f11, r11⟩ => ?_
  have b11 := b10.of_phase f11 r11
  have a11 := a10.of_keep r11
  have vD9 : V9 aD = V6 aD := by vsimp [o9, o8, o7]
  have vN10 : V10 aN = kP s0 * kQ s0 := vN
  have vTop : V10 aTop = 2 ^ (16 * kL s0 - 1) := by vsimp [o10, o9, o8, o7, o6, o5, o4, top3]; rw [hW]
  have vE : V10 aE = eIn s0 := by vsimp [o10, o9, o8, o7, o6, eE5]
  have vC33 : V10 aC33 = 2 ^ 33 := by vsimp [o10, o9, o8, o7, o6, o5, o4, c33]
  have vQ10 : V10 aQ = kQ s0 := by vsimp [o10, vQ9]
  simp only [vN10, vTop, vE, vC33, vQ10, g0, g1, g3, g5, g6, g7] at x8
  have sm : (if (if okv (eIn s0) (kLc s0) then 1 else 0) = 1 ∧ V6 aD < 2 ^ (8 * kL s0) + 1 then 1 else 0) =
      if kSmall s0 (V6 aD) then 1 else 0 := by
    unfold kSmall; by_cases o : okv (eIn s0) (kLc s0) <;> simp [o]
  have mk : F11 X8 = if kMask s0 (V6 aD) then 1 else 0 := by
    rw [x8, sm]; unfold kMask
    simp only [flag_one, flag_zero]
  have s7 : F11 X7 = if kSmall s0 (V6 aD) then 1 else 0 := by vsimp [p11]; rw [g7, sm]
  -- The stores.
  refine WP.mono (stores_ok b11 a11 w11 (a := decide (kSmall s0 (V6 aD))) (b := decide (kMask s0 (V6 aD)))
    (slot_flag (k11.flg X7 (by decide)) s7) (slot_flag (k11.flg X8 (by decide)) mk))
    fun t ⟨ft, t3, outs, kt⟩ => ⟨⟨t11.mem, V6 aD, V8 aQi, ft, ?_, xl, xd, vD, ?_, outs, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
      ?_⟩
  · exact k6.lt (by decide)
  · rw [t3]; simp only [decide_eq_true_eq]
  · rw [k11.arrs _ (by decide)]; vsimp [o11, vN10]
  · rw [k11.arrs _ (by decide)]; vsimp [o11, o10, vD9]
  · rw [k11.arrs _ (by decide)]; vsimp [o11, o10, vP9]
  · rw [k11.arrs _ (by decide)]; vsimp [o11, vQ10]
  · rw [k11.arrs _ (by decide)]; vsimp [o11, o10, vDP, o8, o7, o6, o5, vPm]
  · rw [k11.arrs _ (by decide)]; vsimp [o11, o10, vDQ, o8, o7, o6, o5, vQm]
  · rw [k11.arrs _ (by decide)]; vsimp [o11, o10, o9]
  · exact (((((((((((r1.trans r2).trans r3).trans r4).trans r5).trans r6).trans r7).trans r8).trans r9).trans
      r10).trans r11).trans kt).mono

theorem body_ok [InvLaw] {s0 s : State} (h : Base s0 s) (ha : Args s0 s) :
    WP isa body s fun t => BodyPost s0 t ∧ Keep bodyAll s t := by
  rw [body_eq, show setup :: loads :: (consts ++ [primes, lcmPart, dPart, smallPart, qinvPart, crtPart, nPart,
      maskPart, stores]) = bodyL ++ ([dPart] ++ ([smallPart, qinvPart] ++ bodyT)) by simp,
    wp_seqs_append (by simp) (by simp)]
  refine WP.mono (body_cut_ok h ha) fun _ ⟨_, _, _, w⟩ => ?_
  rw [wp_seqs_append (by simp) (by simp)]
  refine WP.mono w fun _ ⟨_, _, _, w'⟩ => ?_
  rw [wp_seqs_append (by simp) (by simp)]
  exact WP.mono w' fun _ ⟨_, _, _, w''⟩ => w''

end VG.Proof.RsaKeyGen.PPC64LE.Key
