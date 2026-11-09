module

public import VerifiedGarbage.Impl.Mont.PPC64LE.P256
public import VerifiedGarbage.Proof.Mont.PPC64LE.Words
import VerifiedGarbage.Proof.Mont.PPC64LE.Carry
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Carry
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd

-- separate module: one file per prime whose row has its own code (P-224 will add its own beside it),
-- so that the Montgomery proofs of `Ops.lean`, imported by every curve, need not hold every prime's row.

/-!
# P-256's reduction row, on PPC64LE

`qrowP_ok`: the row `qrowP` (`Impl/Mont/PPC64LE/P256.lean`) leaves in
`r15`–`r19` the accumulator `T` (`r15`–`r19`, its top word in `r12`) plus
`q p`, for `q = t₀`, divided by `2⁶⁴`, when that sum is below `2³⁸⁴`: the
words of each carrying instruction (`d + 2⁶⁴ c = a + b + c'`), whose sum
modulo `2³⁸⁴` is `T + q p`.
-/

@[expose] public section

namespace VG.Proof.Mont.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont.PPC64LE

/-- The accumulator: `r15`–`r19` and the top word `r12`. -/
def accP (s : State) : Nat :=
  (s.gpr .r15).toNat + 2 ^ 64 * (s.gpr .r16).toNat + 2 ^ 128 * (s.gpr .r17).toNat +
    2 ^ 192 * (s.gpr .r18).toNat + 2 ^ 256 * (s.gpr .r19).toNat + 2 ^ 320 * (s.gpr .r12).toNat

/-- The five words `r15`–`r19`. -/
def accP5 (s : State) : Nat :=
  (s.gpr .r15).toNat + 2 ^ 64 * (s.gpr .r16).toNat + 2 ^ 128 * (s.gpr .r17).toNat +
    2 ^ 192 * (s.gpr .r18).toNat + 2 ^ 256 * (s.gpr .r19).toNat

theorem p256p_eq : p256p = 115792089210356248762697446949407573530086143415290314195533631308867097853951 := by decide

theorem carry_toNat {v : Nat} (h : v < 2 ^ 65) : (decide (2 ^ 64 ≤ v)).toNat = v / 2 ^ 64 := by
  by_cases hv : 2 ^ 64 ≤ v
  · simp only [hv, decide_true, Bool.toNat_true]; omega
  · simp only [hv, decide_false, Bool.toNat_false]; omega

/-! ## The arithmetic of the row -/

theorem rowP_L {w1 w2 w3 w4 : Nat} (h1 : w1 < 2 ^ 64) (h2 : w2 < 2 ^ 64) (h3 : w3 < 2 ^ 64)
    (h4 : w4 < 2 ^ 64) : w1 + 2 ^ 64 * w2 + 2 ^ 128 * w3 + 2 ^ 192 * w4 < 2 ^ 256 := by
  omega

theorem rowP_lt0 {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) : x + y < 2 ^ 65 := by
  omega

theorem rowP_lt {x y d : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (hd : d ≤ 1) : x + y + d < 2 ^ 65 := by
  omega

theorem rowP_not {A : Nat} (h : A < 2 ^ 64) : 2 ^ 64 - 1 - A < 2 ^ 64 := by
  omega

theorem rowP_d {w d a : Nat} (h : w + 2 ^ 64 * d = a) (ha : a < 2 ^ 65) : d ≤ 1 := by
  omega

theorem rowP_sub {x0 A B u1 v1 u2 v2 : Nat} (hx : x0 < 2 ^ 64) (hA : A + 2 ^ 64 * B = x0 * 2 ^ 32)
    (hAl : A < 2 ^ 64) (hBl : B < 2 ^ 32) (hu1 : u1 < 2 ^ 64) (hu2 : u2 < 2 ^ 64)
    (e1 : u1 + 2 ^ 64 * v1 = x0 + (2 ^ 64 - 1 - A) + 1)
    (e2 : u2 + 2 ^ 64 * v2 = x0 + (2 ^ 64 - 1 - B) + v1) :
    u1 + 2 ^ 64 * u2 = x0 + 2 ^ 64 * x0 - x0 * 2 ^ 32 := by
  omega

theorem rowP_add {x1 x2 x3 x4 A B u1 u2 w1 d1 w2 d2 w3 d3 w4 d4 : Nat}
    (e1 : w1 + 2 ^ 64 * d1 = x1 + A) (e2 : w2 + 2 ^ 64 * d2 = x2 + B + d1)
    (e3 : w3 + 2 ^ 64 * d3 = x3 + u1 + d2) (e4 : w4 + 2 ^ 64 * d4 = x4 + u2 + d3) :
    w1 + 2 ^ 64 * w2 + 2 ^ 128 * w3 + 2 ^ 192 * w4 + 2 ^ 256 * d4 =
      x1 + A + 2 ^ 64 * (x2 + B) + 2 ^ 128 * (x3 + u1) + 2 ^ 192 * (x4 + u2) := by
  omega

theorem rowP_key {x0 x1 x2 x3 x4 c A B u1 u2 w1 w2 w3 w4 d4 : Nat} (hx : x0 < 2 ^ 64)
    (hA : A + 2 ^ 64 * B = x0 * 2 ^ 32) (hD : u1 + 2 ^ 64 * u2 = x0 + 2 ^ 64 * x0 - x0 * 2 ^ 32)
    (eA : w1 + 2 ^ 64 * w2 + 2 ^ 128 * w3 + 2 ^ 192 * w4 + 2 ^ 256 * d4 =
      x1 + A + 2 ^ 64 * (x2 + B) + 2 ^ 128 * (x3 + u1) + 2 ^ 192 * (x4 + u2)) :
    x0 + 2 ^ 64 * x1 + 2 ^ 128 * x2 + 2 ^ 192 * x3 + 2 ^ 256 * x4 + 2 ^ 320 * c + x0 * 115792089210356248762697446949407573530086143415290314195533631308867097853951 =
      2 ^ 64 * (w1 + 2 ^ 64 * w2 + 2 ^ 128 * w3 + 2 ^ 192 * w4 + 2 ^ 256 * (c + d4)) := by
  omega

theorem rowP_top {c d4 L E : Nat} (hL : L < 2 ^ 256) (hE : E < 2 ^ 384)
    (key : E = 2 ^ 64 * (L + 2 ^ 256 * (c + d4))) : (c + d4) % 2 ^ 64 = c + d4 := by
  omega

theorem rowP_arith (x0 x1 x2 x3 x4 c : Nat) (b0 : x0 < 2 ^ 64) (b1 : x1 < 2 ^ 64) (b2 : x2 < 2 ^ 64)
    (b3 : x3 < 2 ^ 64) (b4 : x4 < 2 ^ 64)
    (hb : x0 + 2 ^ 64 * x1 + 2 ^ 128 * x2 + 2 ^ 192 * x3 + 2 ^ 256 * x4 + 2 ^ 320 * c + x0 * 115792089210356248762697446949407573530086143415290314195533631308867097853951 < 2 ^ 384) :
    2 ^ 64 *
      ((x1 + x0 * 2 ^ 32 % 2 ^ 64) % 2 ^ 64 +
              2 ^ 64 * ((x2 + x0 / 2 ^ 32 + (decide (2 ^ 64 ≤ x1 + x0 * 2 ^ 32 % 2 ^ 64)).toNat) % 2 ^ 64) +
            2 ^ 128 *
              ((x3 + (x0 + (2 ^ 64 - 1 - x0 * 2 ^ 32 % 2 ^ 64) + 1) % 2 ^ 64 +
                  (decide (2 ^ 64 ≤ x2 + x0 / 2 ^ 32 + (decide (2 ^ 64 ≤ x1 + x0 * 2 ^ 32 % 2 ^ 64)).toNat)).toNat) %
                2 ^ 64) +
          2 ^ 192 *
            ((x4 +
                  (x0 + (2 ^ 64 - 1 - x0 / 2 ^ 32) +
                      (decide (2 ^ 64 ≤ x0 + (2 ^ 64 - 1 - x0 * 2 ^ 32 % 2 ^ 64) + 1)).toNat) %
                    2 ^ 64 +
                (decide
                    (2 ^ 64 ≤
                      x3 + (x0 + (2 ^ 64 - 1 - x0 * 2 ^ 32 % 2 ^ 64) + 1) % 2 ^ 64 +
                        (decide
                            (2 ^ 64 ≤
                              x2 + x0 / 2 ^ 32 + (decide (2 ^ 64 ≤ x1 + x0 * 2 ^ 32 % 2 ^ 64)).toNat)).toNat)).toNat) %
              2 ^ 64) +
        2 ^ 256 *
          ((c +
              (decide
                  (2 ^ 64 ≤
                    x4 +
                        (x0 + (2 ^ 64 - 1 - x0 / 2 ^ 32) +
                            (decide (2 ^ 64 ≤ x0 + (2 ^ 64 - 1 - x0 * 2 ^ 32 % 2 ^ 64) + 1)).toNat) %
                          2 ^ 64 +
                      (decide
                          (2 ^ 64 ≤
                            x3 + (x0 + (2 ^ 64 - 1 - x0 * 2 ^ 32 % 2 ^ 64) + 1) % 2 ^ 64 +
                              (decide
                                  (2 ^ 64 ≤
                                    x2 + x0 / 2 ^ 32 +
                                      (decide (2 ^ 64 ≤ x1 + x0 * 2 ^ 32 % 2 ^ 64)).toNat)).toNat)).toNat)).toNat) %
            2 ^ 64)) =
    x0 + 2 ^ 64 * x1 + 2 ^ 128 * x2 + 2 ^ 192 * x3 + 2 ^ 256 * x4 + 2 ^ 320 * c + x0 * 115792089210356248762697446949407573530086143415290314195533631308867097853951 := by
  have hA : x0 * 2 ^ 32 % 2 ^ 64 + 2 ^ 64 * (x0 / 2 ^ 32) = x0 * 2 ^ 32 := by omega
  have hAl : x0 * 2 ^ 32 % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by decide)
  have hBl : x0 / 2 ^ 32 < 2 ^ 32 := by omega
  generalize x0 * 2 ^ 32 % 2 ^ 64 = A at *
  generalize x0 / 2 ^ 32 = B at *
  -- t₁ + A
  generalize ha1 : x1 + A = a1
  have h1 : a1 < 2 ^ 65 := by rw [← ha1]; exact rowP_lt0 b1 hAl
  have ea1 := Nat.mod_add_div a1 (2 ^ 64)
  have ma1 := Nat.mod_lt a1 (show 0 < 2 ^ 64 by decide)
  rw [carry_toNat h1]
  generalize a1 % 2 ^ 64 = w1 at *
  generalize a1 / 2 ^ 64 = d1 at *
  -- q - A
  generalize hs1 : x0 + (2 ^ 64 - 1 - A) + 1 = s1
  have hs1b : s1 < 2 ^ 65 := by rw [← hs1]; exact rowP_lt b0 (rowP_not hAl) (Nat.le_refl 1)
  have es1 := Nat.mod_add_div s1 (2 ^ 64)
  have ms1 := Nat.mod_lt s1 (show 0 < 2 ^ 64 by decide)
  rw [carry_toNat hs1b]
  generalize s1 % 2 ^ 64 = u1 at *
  generalize s1 / 2 ^ 64 = v1 at *
  -- t₂ + B
  generalize ha2 : x2 + B + d1 = a2
  have h2 : a2 < 2 ^ 65 := by rw [← ha2]; exact rowP_lt b2 (Nat.lt_trans hBl (by decide)) (rowP_d ea1 h1)
  have ea2 := Nat.mod_add_div a2 (2 ^ 64)
  have ma2 := Nat.mod_lt a2 (show 0 < 2 ^ 64 by decide)
  rw [carry_toNat h2]
  generalize a2 % 2 ^ 64 = w2 at *
  generalize a2 / 2 ^ 64 = d2 at *
  -- q - B
  generalize hs2 : x0 + (2 ^ 64 - 1 - B) + v1 = s2
  have es2 := Nat.mod_add_div s2 (2 ^ 64)
  have ms2 := Nat.mod_lt s2 (show 0 < 2 ^ 64 by decide)
  generalize s2 % 2 ^ 64 = u2 at *
  generalize s2 / 2 ^ 64 = v2 at *
  -- t₃ + D's low word
  generalize ha3 : x3 + u1 + d2 = a3
  have h3 : a3 < 2 ^ 65 := by rw [← ha3]; exact rowP_lt b3 ms1 (rowP_d ea2 h2)
  have ea3 := Nat.mod_add_div a3 (2 ^ 64)
  have ma3 := Nat.mod_lt a3 (show 0 < 2 ^ 64 by decide)
  rw [carry_toNat h3]
  generalize a3 % 2 ^ 64 = w3 at *
  generalize a3 / 2 ^ 64 = d3 at *
  -- t₄ + D's high word
  generalize ha4 : x4 + u2 + d3 = a4
  have h4 : a4 < 2 ^ 65 := by rw [← ha4]; exact rowP_lt b4 ms2 (rowP_d ea3 h3)
  have ea4 := Nat.mod_add_div a4 (2 ^ 64)
  have ma4 := Nat.mod_lt a4 (show 0 < 2 ^ 64 by decide)
  rw [carry_toNat h4]
  have hD := rowP_sub b0 hA hAl hBl ms1 ms2 (es1.trans hs1.symm) (es2.trans hs2.symm)
  have eA := rowP_add (ea1.trans ha1.symm) (ea2.trans ha2.symm) (ea3.trans ha3.symm) (ea4.trans ha4.symm)
  have key := rowP_key (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (c := c) b0 hA hD eA
  rw [rowP_top (rowP_L ma1 ma2 ma3 ma4) hb key, key]

/-- P-256's row: `2⁶⁴ T' = T + q p` for `q = t₀`, when `T + q p < 2³⁸⁴`. -/
theorem qrowP_ok {t : State} (hb : accP t + (t.gpr .r15).toNat * p256p < 2 ^ 384) :
    WP isa (.block qrowP) t fun u =>
      2 ^ 64 * accP5 u = accP t + (t.gpr .r15).toNat * p256p ∧ u.mem = t.mem ∧
      Kp [.r8, .r9, .r11, .r12, .r15, .r16, .r17, .r18, .r19] t u := by
  unfold qrowP
  refine wp_step (exec_lsl (by decide)) ?_
  refine wp_step (exec_lsr_d (by decide)) ?_
  refine wp_step exec_subc ?_
  refine wp_step exec_sube ?_
  refine wp_step exec_addc ?_
  refine wp_step exec_adde ?_
  refine wp_step exec_adde ?_
  refine wp_step exec_adde ?_
  refine wp_step exec_addze ?_
  refine wp_step exec_ori (WP.block_nil ?_)
  refine ⟨?_, rfl, ?_⟩
  · simp only [accP, accP5] at hb ⊢
    simp only [write_gpr, RegUpd.gpr_writeCarry, RegUpd.ca_writeCarry, reduceCtorEq,
      ite_true, ite_false, BitVec.toNat_ofNat, BitVec.toNat_or, BitVec.toNat_shiftLeft,
      BitVec.toNat_ushiftRight]
    have b15 := (t.gpr .r15).isLt
    have b16 := (t.gpr .r16).isLt
    have b17 := (t.gpr .r17).isLt
    have b18 := (t.gpr .r18).isLt
    have b19 := (t.gpr .r19).isLt
    have b12 := (t.gpr .r12).isLt
    generalize (t.gpr .r15).toNat = x0 at *
    generalize (t.gpr .r16).toNat = x1 at *
    generalize (t.gpr .r17).toNat = x2 at *
    generalize (t.gpr .r18).toNat = x3 at *
    generalize (t.gpr .r19).toNat = x4 at *
    generalize (t.gpr .r12).toNat = c at *
    simp only [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, BitVec.toNat_setWidth,
      show (0 : BitVec 16).toNat = 0 from rfl, Nat.zero_mod, Nat.or_zero] at *
    rw [p256p_eq] at hb ⊢
    exact rowP_arith x0 x1 x2 x3 x4 c b15 b16 b17 b18 b19 hb
  · exact (((((((((Kp.write _ _ (by decide)).trans (Kp.write _ _ (by decide))).trans
      (Kp.writeCarry _ _ (by decide))).trans (Kp.writeCarry _ _ (by decide))).trans
      (Kp.writeCarry _ _ (by decide))).trans (Kp.writeCarry _ _ (by decide))).trans
      (Kp.writeCarry _ _ (by decide))).trans (Kp.writeCarry _ _ (by decide))).trans
      (Kp.writeCarry _ _ (by decide))).trans (Kp.write _ _ (by decide))

end VG.Proof.Mont.PPC64LE
