module

public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Key.DOdd
import VerifiedGarbage.Proof.Rsa.PPC64LE.InvParts
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Key.Env2
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Key.Env3

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
theorem dEven_ok [InvLaw] (h : Ws s B Z w nArr) (ks : KS s.mem B w V F) (hw : 10 ≤ w) (he : V aE < 2 ^ 64)
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
    (hnw := Nat.le_refl _)
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
theorem dPart_ok [InvLaw] (h : Ws s B Z w nArr) (ks : KS s.mem B w V F) (hw : 10 ≤ w) (he : V aE < 2 ^ 64)
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
  refine WP.mono (dEven_ok h3 k3 hw (by rw [e3]; exact he) one3 three3 zero3 (by rw [w3, e3]) (by rw [z6, x6]; split <;> split <;> omega_arith))
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
