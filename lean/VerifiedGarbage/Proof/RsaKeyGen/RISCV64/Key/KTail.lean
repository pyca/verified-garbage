module

public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Key.DPart
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_keygen_key` on RISC-V: from `d` to the mask

`qinvPart_ok` (`qInv` modulo `mL p`, `X0` `p` odd, `X1` `gcd(q, mL p) = 1`),
`crtPart_ok` (`dP`, `dQ`), `nPart_ok` (`n = p q`) and `maskPart_ok` (`X8`,
the mask of the checks).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.RISCV64.Key

open VG VG.RISCV64 VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Keys VG.Proof.RsaKeyGen
open VG.Impl.Rsa.RISCV64.Keys (seqs copy sub3 sel eqS bitOf andS aZero)
open VG.Impl.Rsa.RISCV64.Div (div)
open VG.Impl.RsaKeyGen.RISCV64.Key (nArr aDv aT aS aOne aThree aE aP aQ aPm aQm aD aC33 aTop aN aQi aMq
  aDP aDQ aQd aDt X0 X1 X2 X3 X4 X5 X6 X7 X8 ltS andNotS invOf qinvPart crtOf crtPart nPart maskPart nP)

/-- A flag is 1 exactly when its condition holds. -/
theorem flag_one (c : Prop) [Decidable c] : ((if c then 1 else 0 : Nat) = 1) ↔ c := by
  by_cases h : c <;> simp [h]

/-- A flag is 0 exactly when its condition fails. -/
theorem flag_zero (c : Prop) [Decidable c] : ((if c then 1 else 0 : Nat) = 0) ↔ ¬ c := by
  by_cases h : c <;> simp [h]

/-- A selection under a flag of a condition. -/
theorem sel_flag (c : Prop) [Decidable c] (a b : Nat) :
    (if (if c then 1 else 0 : Nat) = 0 then a else b) = if c then b else a := by
  by_cases h : c <;> simp [h]

/-- A product of flags, as a flag. -/
theorem mul01 {x y : Nat} (hx : x ≤ 1) (hy : y ≤ 1) : x * y = if x = 1 ∧ y = 1 then 1 else 0 := by
  rcases (show x = 0 ∨ x = 1 by omega) with rfl | rfl <;> rcases (show y = 0 ∨ y = 1 by omega) with rfl | rfl <;>
    decide

/-- The negation of a flag, as a flag. -/
theorem sub01 {x : Nat} (hx : x ≤ 1) : 1 - x = if x = 0 then 1 else 0 := by
  rcases (show x = 0 ∨ x = 1 by omega) with rfl | rfl <;> decide

section
variable {s0 s : State} {V F : Nat → Nat}

/-- The arrays `qinvPart` writes. -/
abbrev qinvArrs : List Nat := [aT, aMq, aQi] ++ invOfArrs

theorem qinvPart_eq : qinvPart = seqs (([.block (bitOf X0 aP ++ ([] : List Instr))] : List (Prog isa)) ++
    (ltS X1 aP aThree ++ ([.block (andNotS X2 X1 X0 ++ ([] : List Instr)), sel aMq aThree aP X2, invOf aQ aMq nP,
      eqS X1 1 aOne, copy aQi 3] : List (Prog isa)))) := rfl

/-- `qInv` modulo `mL p`, `X0` `p` odd, `X1` `gcd(q, mL p) = 1`. -/
theorem qinvPart_ok (hp : PreC s0) (e : KE s0 V F s) (one : V aOne = 1) (three : V aThree = 3)
    (zero : V aZero = 0) (hpl : V aP < 2 ^ (8 * pLen s0)) (hql : V aQ < 2 ^ (8 * pLen s0)) :
    WP isa qinvPart s fun t => ∃ V' F', KE s0 V' F' t ∧ (∀ j < nArr, j ∉ qinvArrs → V' j = V j) ∧
      (∀ d, d ≠ X0 → d ≠ X1 → d ≠ X2 → F' d = F d) ∧
      F' X0 = V aP % 2 ∧ F' X1 = (if Nat.gcd (V aQ) (mL (V aP)) = 1 then 1 else 0) ∧
      V' aQi < mL (V aP) ∧
      ((mL (V aP) : Nat) : Int) ∣ (V' aQi : Int) * V aQ - Nat.gcd (V aQ) (mL (V aP)) := by
  have mo := mL_odd (V aP)
  have w8 := hp.fits.2.1
  have w128 := hp.fits.2.2
  have wl := hp.wOf_eq
  rw [qinvPart_eq, wp_seqs_append (by simp) (by simp [ltS])]
  change WP isa (.block (bitOf X0 aP ++ [])) s _
  refine bitOfE e (d := X0) (j := aP) (k := fun t1 e1 => WP.block_nil ?_)
  obtain ⟨F1, e1, g1, p1⟩ := e1.fx
  rw [wp_seqs_append (by simp [ltS]) (by simp)]
  refine WP.mono (ltSE e1 (d := X1) (a := aP) (b := aThree)) fun t2 e2 => ?_
  obtain ⟨V2, e2, v2, o2⟩ := e2.vx
  obtain ⟨F2, e2, g2, p2⟩ := e2.fx
  rw [wp_seqs_cons (by simp)]
  refine andNotSE e2 (d := X2) (a := X1) (b := X0) (ba := by rw [g2]; exact flag01 _)
    (bb := by rw [p2 X0 (by decide), g1]; omega_arith) (k := fun t3 e3 => WP.block_nil ?_)
  obtain ⟨F3, e3, g3, p3⟩ := e3.fx
  have vG : F3 X2 = if good (V aP) then 1 else 0 := by
    rw [g3, g2, p2 X0 (by decide), g1, three]
    unfold good
    rcases Nat.mod_two_eq_zero_or_one (V aP) with b | b <;> by_cases a : V aP < 3 <;> simp [a, b]
  rw [wp_seqs_cons (by simp)]
  refine WP.mono (selE e3 (o := aMq) (a := aThree) (b := aP) (sl := X2) (bit := by rw [vG]; exact flag01 _))
    fun t4 e4 => ?_
  obtain ⟨V4, e4, v4, o4⟩ := e4.vx
  have vMq : V4 aMq = mL (V aP) := by
    rw [v4, vG, o2 aThree (by decide), o2 aP (by decide), three, mL]
    by_cases a : good (V aP) <;> simp [a]
  have one4 : V4 aOne = 1 := by rw [o4 aOne (by decide), o2 aOne (by decide), one]
  have zero4 : V4 aZero = 0 := by rw [o4 aZero (by decide), o2 aZero (by decide), zero]
  have vQ4 : V4 aQ = V aQ := by rw [o4 aQ (by decide), o2 aQ (by decide)]
  have mlt : mL (V aP) < 2 ^ (8 * pLen s0) := by
    unfold mL; split
    · exact hpl
    · exact Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by decide) (by omega_arith : 2 ≤ 8 * pLen s0))
  rw [wp_seqs_cons (by simp)]
  refine WP.mono (invOfE e4 (a := aQ) (m := aMq) (K := 8 * pLen s0) (hK := by omega_arith)
    (hK' := by omega_arith)
    (hk := fun u hu => nP_ok u (by rw [hu .a1 (by decide), pLen_ofNat e4.st.cb])) (zero := zero4)
    (odd := by rw [vMq]; exact mo.1) (gt := by rw [vMq]; exact mo.2)
    (fit := by
      rw [vQ4, vMq]
      calc V aQ * mL (V aP) < 2 ^ (8 * pLen s0) * 2 ^ (8 * pLen s0) := Nat.mul_lt_mul'' hql mlt
        _ = 2 ^ (2 * (8 * pLen s0)) := by rw [← Nat.pow_add]; exact congrArg (2 ^ ·) (by omega_arith)))
    fun t5 ⟨V5, e5, o5, g5, d5, l5⟩ => ?_
  simp only [vMq, vQ4] at g5 d5 l5
  have one5 : V5 aOne = 1 := by rw [o5 aOne (by decide) (by decide), one4]
  refine WP.seq (WP.mono (eqSE e5 (d := X1) (a := 1) (b := aOne)) fun t6 e6 => ?_)
  obtain ⟨F6, e6, g6, p6⟩ := e6.fx
  refine WP.mono (copyE e6 (o := aQi) (a := 3)) fun t e7 => ?_
  obtain ⟨V7, e7, v7, o7⟩ := e7.vx
  refine ⟨V7, F6, e7, fun j hj hn => ?_, fun d a b c => ?_, ?_, by rw [g6, g5, one5], by rw [v7]; exact l5,
    by rw [v7, ← g5]; exact d5⟩
  · have hi : j ∉ invOfArrs := fun m => hn (List.mem_append_right _ m)
    rw [o7 j (ne_of_nm hn), o5 j hj hi, o4 j (ne_of_nm hn), o2 j (ne_of_nm hn)]
  · rw [p6 d b, p3 d c, p2 d b, p1 d a]
  · rw [p6 X0 (by decide), p3 X0 (by decide), p2 X0 (by decide), g1]

/-- The arrays `crtOf o` writes. -/
abbrev crtArrs (o : Nat) : List Nat := [aS, aQd, aDv, aDt, o]

/-- `[o] := d mod [j]`, by 1 for `[j] = 0`. -/
theorem crtOf_ok (e : KE s0 V F s) {o j : Nat} (ho : o < nArr := by decide)
    (hj : j < nArr := by decide) (hjS : aS ≠ j := by decide) (hoQ : aQd ≠ o := by decide)
    (hoT : o ≠ aDt := by decide) (hoD : o ≠ aDv := by decide) (one : V aOne = 1) (zero : V aZero = 0) :
    WP isa (crtOf o j) s fun t => ∃ V' F', KE s0 V' F' t ∧ (∀ k < nArr, k ∉ crtArrs o → V' k = V k) ∧
      (∀ d, d ≠ X2 → F' d = F d) ∧ V' o = V aD % (if V j = 0 then 1 else V j) := by
  change WP isa (.seq (eqS X2 j aZero) (.seq (sel aS j aOne X2) (.seq (copy aQd aD)
    (.seq (copy aDv aS) (div aQd o aDv aDt))))) s _
  refine WP.seq (WP.mono (eqSE e (d := X2) (a := j) (b := aZero) (ha := hj)) fun t1 e1 => ?_)
  obtain ⟨F1, e1, g1, p1⟩ := e1.fx
  refine WP.seq (WP.mono (selE e1 (o := aS) (a := j) (b := aOne) (sl := X2) (ha := hj) (hoa := hjS)
    (bit := by rw [g1]; exact flag01 _)) fun t2 e2 => ?_)
  obtain ⟨V2, e2, v2, o2⟩ := e2.vx
  refine WP.seq (WP.mono (copyE e2 (o := aQd) (a := aD)) fun t3 e3 => ?_)
  obtain ⟨V3, e3, v3, o3⟩ := e3.vx
  refine WP.seq (WP.mono (copyE e3 (o := aDv) (a := aS)) fun t4 e4 => ?_)
  obtain ⟨V4, e4, v4, o4⟩ := e4.vx
  refine WP.mono (divE e4 (q := aQd) (r := o) (t := aDt) (hr := ho) (hqr := hoQ) (hrt := hoT) (hrd := hoD))
    fun t ⟨V5, e5, o5, v5⟩ => ?_
  have vS : V2 aS = if V j = 0 then 1 else V j := by
    rw [v2, g1, zero, sel_flag, one]
  have vDv : V4 aDv = if V j = 0 then 1 else V j := by
    rw [v4, o3 aS (by decide), vS]
  have pos : 0 < V4 aDv := by rw [vDv]; split <;> omega_arith
  refine ⟨V5, F1, e5, fun k hk hn => ?_, p1, ?_⟩
  · simp only [crtArrs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    obtain ⟨n1, n2, n3, n4, n5⟩ := hn
    rw [o5 k hk n2 n5 n4, o4 k n3, o3 k n2, o2 k n1]
  · rw [(v5 pos).2, vDv, o4 aQd (by decide), v3, o2 aD (by decide)]

/-- The arrays `crtPart` writes. -/
abbrev crtPartArrs : List Nat := [aS, aQd, aDv, aDt, aDP, aDQ]

/-- `dP` and `dQ`. -/
theorem crtPart_ok (e : KE s0 V F s) (one : V aOne = 1) (zero : V aZero = 0) :
    WP isa crtPart s fun t => ∃ V' F', KE s0 V' F' t ∧ (∀ k < nArr, k ∉ crtPartArrs → V' k = V k) ∧
      (∀ d, d ≠ X2 → F' d = F d) ∧ V' aDP = V aD % (if V aPm = 0 then 1 else V aPm) ∧
      V' aDQ = V aD % (if V aQm = 0 then 1 else V aQm) := by
  change WP isa (.seq (crtOf aDP aPm) (crtOf aDQ aQm)) s _
  refine WP.seq (WP.mono (crtOf_ok e (o := aDP) (j := aPm) (one := one) (zero := zero))
    fun t1 ⟨V1, F1, e1, o1, p1, v1⟩ => ?_)
  refine WP.mono (crtOf_ok e1 (o := aDQ) (j := aQm) (one := by rw [o1 _ (by decide) (by decide), one])
    (zero := by rw [o1 _ (by decide) (by decide), zero])) fun t ⟨V2, F2, e2, o2, p2, v2⟩ => ?_
  refine ⟨V2, F2, e2, fun k hk hn => ?_, fun d a => by rw [p2 d a, p1 d a], ?_, ?_⟩
  · rw [o2 k hk (fun m => hn (by simp only [crtArrs] at m; simp only [crtPartArrs]; simp_all)),
      o1 k hk (fun m => hn (by simp only [crtArrs] at m; simp only [crtPartArrs]; simp_all))]
  · rw [o2 aDP (by decide) (by decide), v1]
  · rw [v2, o1 aD (by decide) (by decide), o1 aQm (by decide) (by decide)]

/-- `n = p q`, for `p, q < 2^(8 p_len)`. -/
theorem nPart_ok (hp : PreC s0) (e : KE s0 V F s) (hpl : V aP < 2 ^ (8 * pLen s0))
    (hql : V aQ < 2 ^ (8 * pLen s0)) (zero : V aZero = 0) :
    WP isa nPart s fun t => ∃ V', KE s0 V' F t ∧ (∀ j < nArr, j ≠ aN → V' j = V j) ∧ V' aN = V aP * V aQ := by
  have wl := hp.wOf_eq
  refine WP.mono (mulToE e (o := aN) (a := aP) (b := aQ) (zero := zero)) fun t et => ?_
  obtain ⟨V', et, v', o'⟩ := et.vx
  refine ⟨V', et, fun j _ hj => o' j hj, ?_⟩
  have hpq : V aP * V aQ < 2 ^ (64 * wOf s0) := by
    rw [show 64 * wOf s0 = 8 * pLen s0 + 8 * pLen s0 by omega_arith, Nat.pow_add]
    exact Nat.mul_lt_mul'' hpl hql
  rw [v', Nat.mod_eq_of_lt hpq]

theorem maskPart_eq : maskPart = seqs (ltS X2 aN aTop ++ (([.block (andNotS X8 X2 X6 ++ (andS X8 X8 X1 ++
    (andS X8 X8 X0 ++ (bitOf X2 aQ ++ (andS X8 X8 X2 ++ (andS X8 X8 X3 ++ ([] : List Instr)))))))] : List (Prog isa)) ++
    (ltS X2 aE aC33 ++ ([.block (andNotS X4 X5 X2 ++ (andS X8 X8 X4 ++ (andNotS X8 X7 X8 ++ ([] : List Instr))))] :
      List (Prog isa))))) := rfl

/-- `X8` := not small, and `n ≥ [aTop]`, `d` exists, `gcd(q, mL p) = 1`,
`p` and `q` odd, `e` odd, at least 3 and below `[aC33]`. -/
theorem maskPart_ok (e : KE s0 V F s) (b0 : F X0 ≤ 1) (b1 : F X1 ≤ 1) (b3 : F X3 ≤ 1) (b5 : F X5 ≤ 1)
    (b6 : F X6 ≤ 1) (b7 : F X7 ≤ 1) :
    WP isa maskPart s fun t => ∃ V' F', KE s0 V' F' t ∧ (∀ j, j ≠ aT → V' j = V j) ∧
      (∀ d, d ≠ X2 → d ≠ X4 → d ≠ X8 → F' d = F d) ∧
      F' X8 = (if F X7 = 0 ∧ ¬ V aN < V aTop ∧ F X6 = 1 ∧ F X1 = 1 ∧ F X0 = 1 ∧ V aQ % 2 = 1 ∧
        F X3 = 1 ∧ F X5 = 0 ∧ V aE < V aC33 then 1 else 0) := by
  rw [maskPart_eq, wp_seqs_append (by simp [ltS]) (by simp)]
  refine WP.mono (ltSE e (d := X2) (a := aN) (b := aTop)) fun t1 e1 => ?_
  obtain ⟨V1, e1, _, o1⟩ := e1.vx
  obtain ⟨F1, e1, g1, p1⟩ := e1.fx
  rw [wp_seqs_append (by simp) (by simp [ltS])]
  change WP isa (.block _) t1 _
  refine andNotSE e1 (d := X8) (a := X2) (b := X6) (ba := by rw [g1]; exact flag01 _)
    (bb := by rw [p1 X6 (by decide)]; exact b6) (k := fun t2 e2 => ?_)
  obtain ⟨F2, e2, g2, p2⟩ := e2.fx
  have c8 : ∀ {x y : Nat}, x ≤ 1 → y ≤ 1 → x * y ≤ 1 := fun hx hy => Nat.mul_le_mul hx hy
  refine andSE e2 (d := X8) (a := X8) (b := X1) (ba := by rw [g2, g1, p1 X6 (by decide)]; exact c8 (by omega) b6)
    (bb := by rw [p2 X1 (by decide), p1 X1 (by decide)]; exact b1) (k := fun t3 e3 => ?_)
  obtain ⟨F3, e3, g3, p3⟩ := e3.fx
  refine andSE e3 (d := X8) (a := X8) (b := X0) (ba := ?_)
    (bb := by rw [p3 X0 (by decide), p2 X0 (by decide), p1 X0 (by decide)]; exact b0)
    (k := fun t4 e4 => ?_)
  · rw [g3, g2, p2 X1 (by decide), p1 X1 (by decide), p1 X6 (by decide)]
    exact c8 (c8 (by omega) b6) b1
  obtain ⟨F4, e4, g4, p4⟩ := e4.fx
  refine bitOfE e4 (d := X2) (j := aQ) (k := fun t5 e5 => ?_)
  obtain ⟨F5, e5, g5, p5⟩ := e5.fx
  have h8 : F4 X8 ≤ 1 := by
    rw [g4, g3, g2, p3 X0 (by decide), p2 X0 (by decide), p2 X1 (by decide), p1 X0 (by decide),
      p1 X1 (by decide), p1 X6 (by decide)]
    exact c8 (c8 (c8 (by omega) b6) b1) b0
  refine andSE e5 (d := X8) (a := X8) (b := X2) (ba := by rw [p5 X8 (by decide)]; exact h8)
    (bb := by rw [g5]; omega_arith) (k := fun t6 e6 => ?_)
  obtain ⟨F6, e6, g6, p6⟩ := e6.fx
  refine andSE e6 (d := X8) (a := X8) (b := X3) (ba := by rw [g6, p5 X8 (by decide), g5]; exact c8 h8 (by omega))
    (bb := by vsimp [p6, p5, p4, p3, p2, p1]; exact b3) (k := fun t7 e7 => WP.block_nil ?_)
  obtain ⟨F7, e7, g7, p7⟩ := e7.fx
  rw [wp_seqs_append (by simp [ltS]) (by simp)]
  refine WP.mono (ltSE e7 (d := X2) (a := aE) (b := aC33)) fun t8 e8 => ?_
  obtain ⟨V8, e8, _, o8⟩ := e8.vx
  obtain ⟨F8, e8, g8, p8⟩ := e8.fx
  change WP isa (.block _) t8 _
  have c5 : F8 X5 = F X5 := by vsimp [p8, p7, p6, p5, p4, p3, p2, p1]
  have c7 : F8 X7 = F X7 := by vsimp [p8, p7, p6, p5, p4, p3, p2, p1]
  have h87 : F7 X8 ≤ 1 := by
    rw [g7, g6, p5 X8 (by decide), g5]
    exact c8 (c8 h8 (by omega)) (by vsimp [p6, p5, p4, p3, p2, p1]; exact b3)
  refine andNotSE e8 (d := X4) (a := X5) (b := X2) (ba := by rw [c5]; exact b5)
    (bb := by rw [g8]; exact flag01 _) (k := fun t9 e9 => ?_)
  obtain ⟨F9, e9, g9, p9⟩ := e9.fx
  refine andSE e9 (d := X8) (a := X8) (b := X4) (ba := by rw [p9 X8 (by decide), p8 X8 (by decide)]; exact h87)
    (bb := by rw [g9, c5, g8]; exact c8 (by omega) (flag01 _)) (k := fun t10 e10 => ?_)
  obtain ⟨F10, e10, g10, p10⟩ := e10.fx
  refine andNotSE e10 (d := X8) (a := X7) (b := X8)
    (ba := by rw [p10 X7 (by decide), p9 X7 (by decide), c7]; exact b7)
    (bb := by
      rw [g10, p9 X8 (by decide), p8 X8 (by decide), g9, c5, g8]; exact c8 h87 (c8 (by omega) (flag01 _)))
    (k := fun t e11 => WP.block_nil ?_)
  obtain ⟨F11, e11, g11, p11⟩ := e11.fx
  refine ⟨V8, F11, e11, fun j a => by rw [o8 j a, o1 j a], fun d a b c => ?_, ?_⟩
  · rw [p11 d c, p10 d c, p9 d b, p8 d a, p7 d c, p6 d c, p5 d a, p4 d c, p3 d c, p2 d c, p1 d a]
  · rw [g11, p10 X7 (by decide), p9 X7 (by decide), c7, g10, p9 X8 (by decide), p8 X8 (by decide), g9, c5, g8,
      g7, g6, p5 X8 (by decide), g5, g4, g3, g2, g1]
    vsimp [p6, p5, p4, p3, p2, p1, o1]
    have hq1 : V aQ % 2 ≤ 1 := by omega
    simp (disch := first | with_reducible assumption | exact flag01 _) only [mul01, sub01, flag_one, flag_zero, and_assoc]

end

end VG.Proof.RsaKeyGen.RISCV64.Key
