module

public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Key.Lcm
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Key.DMath
import VerifiedGarbage.Proof.Rsa.PPC64LE.InvParts
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Key.Env2
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Key.Env3

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
    (zero : V aZero = 0) (hw10 : 10 ≤ w) {L : Nat} (h22 : s.gpr .r22 = BitVec.ofNat 64 L) (hL' : 8 * L < 2 ^ 64)
    (hL4 : L % 4 = 0) (hL1 : 4 ≤ L) (hLw : L ≤ 4 * w) (hp : V aP < 2 ^ (8 * L)) (hq : V aQ < 2 ^ (8 * L)) :
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
    (hnw := by omega_arith) (han := by rw [vQ4, e32]; exact hq)
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
