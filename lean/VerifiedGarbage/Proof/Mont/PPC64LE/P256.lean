module

public import VerifiedGarbage.Impl.Mont.PPC64LE.P256
public import VerifiedGarbage.Proof.Mont.PPC64LE.Words
import VerifiedGarbage.Proof.Mont.PPC64LE.Carry
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Carry
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd

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

theorem rowP_final {E L Q : Nat} (key : E + 2 ^ 320 = 2 ^ 64 * (L + 2 ^ 256 * Q)) (q1 : 1 ≤ Q) :
    2 ^ 64 * (L + 2 ^ 256 * (Q - 1)) = E := by
  omega

theorem rowP_chainB {x3 x4 A B s1 u1 v1 s2 u2 v2 : Nat} (hAl : A < 2 ^ 64) (hBl : B < 2 ^ 32)
    (hs1 : x3 + (2 ^ 64 - 1 - A) + 1 = s1) (es1 : u1 + 2 ^ 64 * v1 = s1)
    (hs2 : x4 + (2 ^ 64 - 1 - B) + v1 = s2) (es2 : u2 + 2 ^ 64 * v2 = s2) :
    u1 + 2 ^ 64 * u2 + 2 ^ 128 * v2 + A + 2 ^ 64 * B = x3 + 2 ^ 64 * x4 + 2 ^ 128 := by
  omega

theorem rowP_chainA {x0 x1 x2 A B u1 u2 a1 w1 d1 a2 w2 d2 a3 w3 d3 a4 w4 d4 : Nat}
    (ha1 : x1 + A = a1) (ea1 : w1 + 2 ^ 64 * d1 = a1) (ha2 : x2 + B + d1 = a2) (ea2 : w2 + 2 ^ 64 * d2 = a2)
    (ha3 : u1 + x0 + d2 = a3) (ea3 : w3 + 2 ^ 64 * d3 = a3) (ha4 : u2 + x0 + d3 = a4)
    (ea4 : w4 + 2 ^ 64 * d4 = a4) :
    w1 + 2 ^ 64 * w2 + 2 ^ 128 * w3 + 2 ^ 192 * w4 + 2 ^ 256 * d4 =
      x1 + A + 2 ^ 64 * (x2 + B) + 2 ^ 128 * (u1 + x0) + 2 ^ 192 * (u2 + x0) := by
  omega

theorem rowP_key {x0 x1 x2 x3 x4 c A B u1 u2 v2 w1 w2 w3 w4 d4 : Nat} (hA : A + 2 ^ 64 * B = x0 * 2 ^ 32)
    (eB : u1 + 2 ^ 64 * u2 + 2 ^ 128 * v2 + A + 2 ^ 64 * B = x3 + 2 ^ 64 * x4 + 2 ^ 128)
    (eA : w1 + 2 ^ 64 * w2 + 2 ^ 128 * w3 + 2 ^ 192 * w4 + 2 ^ 256 * d4 =
      x1 + A + 2 ^ 64 * (x2 + B) + 2 ^ 128 * (u1 + x0) + 2 ^ 192 * (u2 + x0)) :
    x0 + 2 ^ 64 * x1 + 2 ^ 128 * x2 + 2 ^ 192 * x3 + 2 ^ 256 * x4 + 2 ^ 320 * c +
      x0 * 115792089210356248762697446949407573530086143415290314195533631308867097853951 + 2 ^ 320 =
      2 ^ 64 * (w1 + 2 ^ 64 * w2 + 2 ^ 128 * w3 + 2 ^ 192 * w4 + 2 ^ 256 * (c + v2 + d4)) := by
  omega

theorem rowP_top {c v2 d4 L E : Nat} (hL : L < 2 ^ 256)
    (hE : E < 2 ^ 384) (key : E + 2 ^ 320 = 2 ^ 64 * (L + 2 ^ 256 * (c + v2 + d4))) :
    ((2 ^ 64 - 1 % 2 ^ 64 + (c + v2) % 2 ^ 64) % 2 ^ 64 + d4) % 2 ^ 64 = c + v2 + d4 - 1 ∧
      1 ≤ c + v2 + d4 := by
  omega

/-- The row's words, as the code computes them, are `(T + q p) / 2⁶⁴`. -/
theorem rowP_arith (x0 x1 x2 x3 x4 c : Nat) (b0 : x0 < 2 ^ 64) (b3 : x3 < 2 ^ 64)
    (hb : x0 + 2 ^ 64 * x1 + 2 ^ 128 * x2 + 2 ^ 192 * x3 + 2 ^ 256 * x4 + 2 ^ 320 * c +
      x0 * 115792089210356248762697446949407573530086143415290314195533631308867097853951 < 2 ^ 384) :
    2 ^ 64 *
      ((x1 + x0 * 2 ^ 32 % 2 ^ 64) % 2 ^ 64 +
              2 ^ 64 * ((x2 + x0 / 2 ^ 32 + (x1 + x0 * 2 ^ 32 % 2 ^ 64) / 2 ^ 64) % 2 ^ 64) +
            2 ^ 128 *
              (((x3 + (2 ^ 64 - 1 - x0 * 2 ^ 32 % 2 ^ 64) + 1) % 2 ^ 64 + x0 +
                  (x2 + x0 / 2 ^ 32 + (x1 + x0 * 2 ^ 32 % 2 ^ 64) / 2 ^ 64) / 2 ^ 64) %
                2 ^ 64) +
          2 ^ 192 *
            (((x4 + (2 ^ 64 - 1 - x0 / 2 ^ 32) + (x3 + (2 ^ 64 - 1 - x0 * 2 ^ 32 % 2 ^ 64) + 1) / 2 ^ 64) % 2 ^ 64 +
                  x0 +
                ((x3 + (2 ^ 64 - 1 - x0 * 2 ^ 32 % 2 ^ 64) + 1) % 2 ^ 64 + x0 +
                    (x2 + x0 / 2 ^ 32 + (x1 + x0 * 2 ^ 32 % 2 ^ 64) / 2 ^ 64) / 2 ^ 64) /
                  2 ^ 64) %
              2 ^ 64) +
        2 ^ 256 *
          (((2 ^ 64 - 1 % 2 ^ 64 +
                  (c +
                      (x4 + (2 ^ 64 - 1 - x0 / 2 ^ 32) + (x3 + (2 ^ 64 - 1 - x0 * 2 ^ 32 % 2 ^ 64) + 1) / 2 ^ 64) /
                        2 ^ 64) %
                    2 ^ 64) %
                2 ^ 64 +
              ((x4 + (2 ^ 64 - 1 - x0 / 2 ^ 32) + (x3 + (2 ^ 64 - 1 - x0 * 2 ^ 32 % 2 ^ 64) + 1) / 2 ^ 64) % 2 ^ 64 +
                    x0 +
                  ((x3 + (2 ^ 64 - 1 - x0 * 2 ^ 32 % 2 ^ 64) + 1) % 2 ^ 64 + x0 +
                      (x2 + x0 / 2 ^ 32 + (x1 + x0 * 2 ^ 32 % 2 ^ 64) / 2 ^ 64) / 2 ^ 64) /
                    2 ^ 64) /
                2 ^ 64) %
            2 ^ 64)) =
    x0 + 2 ^ 64 * x1 + 2 ^ 128 * x2 + 2 ^ 192 * x3 + 2 ^ 256 * x4 + 2 ^ 320 * c +
      x0 * 115792089210356248762697446949407573530086143415290314195533631308867097853951 := by
  have hA : x0 * 2 ^ 32 % 2 ^ 64 + 2 ^ 64 * (x0 / 2 ^ 32) = x0 * 2 ^ 32 := by omega
  have hAl : x0 * 2 ^ 32 % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by decide)
  have hBl : x0 / 2 ^ 32 < 2 ^ 32 := by omega
  generalize x0 * 2 ^ 32 % 2 ^ 64 = A at *
  generalize x0 / 2 ^ 32 = B at *
  generalize hs1 : x3 + (2 ^ 64 - 1 - A) + 1 = s1
  have ls1 : s1 < 2 ^ 65 := by omega
  have es1 := Nat.mod_add_div s1 (2 ^ 64)
  have ms1 := Nat.mod_lt s1 (show 0 < 2 ^ 64 by decide)
  generalize s1 % 2 ^ 64 = u1 at *
  generalize s1 / 2 ^ 64 = v1 at *
  generalize hs2 : x4 + (2 ^ 64 - 1 - B) + v1 = s2
  have es2 := Nat.mod_add_div s2 (2 ^ 64)
  have ms2 := Nat.mod_lt s2 (show 0 < 2 ^ 64 by decide)
  generalize s2 % 2 ^ 64 = u2 at *
  generalize s2 / 2 ^ 64 = v2 at *
  generalize ha1 : x1 + A = a1
  have ea1 := Nat.mod_add_div a1 (2 ^ 64)
  have ma1 := Nat.mod_lt a1 (show 0 < 2 ^ 64 by decide)
  generalize a1 % 2 ^ 64 = w1 at *
  generalize a1 / 2 ^ 64 = d1 at *
  generalize ha2 : x2 + B + d1 = a2
  have ea2 := Nat.mod_add_div a2 (2 ^ 64)
  have ma2 := Nat.mod_lt a2 (show 0 < 2 ^ 64 by decide)
  generalize a2 % 2 ^ 64 = w2 at *
  generalize a2 / 2 ^ 64 = d2 at *
  generalize ha3 : u1 + x0 + d2 = a3
  have ea3 := Nat.mod_add_div a3 (2 ^ 64)
  have ma3 := Nat.mod_lt a3 (show 0 < 2 ^ 64 by decide)
  generalize a3 % 2 ^ 64 = w3 at *
  generalize a3 / 2 ^ 64 = d3 at *
  generalize ha4 : u2 + x0 + d3 = a4
  have ea4 := Nat.mod_add_div a4 (2 ^ 64)
  have ma4 := Nat.mod_lt a4 (show 0 < 2 ^ 64 by decide)
  generalize a4 % 2 ^ 64 = w4 at *
  generalize a4 / 2 ^ 64 = d4 at *
  have eB := rowP_chainB hAl hBl hs1 es1 hs2 es2
  have eA := rowP_chainA ha1 ea1 ha2 ea2 ha3 ea3 ha4 ea4
  have key := rowP_key (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (c := c) hA eB eA
  obtain ⟨top, q1⟩ := rowP_top (rowP_L ma1 ma2 ma3 ma4) hb key
  rw [top]
  exact rowP_final key q1

/-- P-256's row: `2⁶⁴ T' = T + q p` for `q = t₀`, when `T + q p < 2³⁸⁴`. -/
theorem qrowP_ok {t : State} (hb : accP t + (t.gpr .r15).toNat * p256p < 2 ^ 384) :
    WP isa (.block qrowP) t fun u =>
      2 ^ 64 * accP5 u = accP t + (t.gpr .r15).toNat * p256p ∧ u.mem = t.mem ∧
      Kp [.r9, .r11, .r12, .r15, .r16, .r17, .r18, .r19] t u := by
  unfold qrowP
  refine wp_step (exec_lsl (by decide)) ?_
  refine wp_step (exec_lsr_d (by decide)) ?_
  refine wp_step exec_subc ?_
  refine wp_step exec_sube ?_
  refine wp_step exec_addze ?_
  refine wp_step (exec_subi (by decide) (by decide)) ?_
  refine wp_step exec_addc ?_
  refine wp_step exec_adde ?_
  refine wp_step exec_adde ?_
  refine wp_step exec_adde ?_
  refine wp_step exec_addze ?_
  refine wp_step exec_ori ?_
  refine wp_step exec_ori ?_
  refine wp_step exec_ori ?_
  refine wp_step exec_ori ?_
  refine wp_step exec_ori (WP.block_nil ?_)
  refine ⟨?_, rfl, ?_⟩
  · simp only [accP, accP5] at hb ⊢
    simp only [write_gpr, RegUpd.gpr_writeCarry, RegUpd.ca_writeCarry, reduceCtorEq,
      ite_true, ite_false, BitVec.toNat_ofNat, BitVec.toNat_or, BitVec.toNat_shiftLeft,
      BitVec.toNat_ushiftRight, BitVec.toNat_sub]
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
    simp (disch := omega) only [carry_toNat]
    rw [p256p_eq] at hb ⊢
    exact rowP_arith x0 x1 x2 x3 x4 c b15 b18 hb
  · exact ((((((((((((((((Kp.write _ _ (by decide)).trans (Kp.write _ _ (by decide))).trans
      (Kp.writeCarry _ _ (by decide))).trans (Kp.writeCarry _ _ (by decide))).trans
      (Kp.writeCarry _ _ (by decide))).trans (Kp.write _ _ (by decide))).trans
      (Kp.writeCarry _ _ (by decide))).trans (Kp.writeCarry _ _ (by decide))).trans
      (Kp.writeCarry _ _ (by decide))).trans (Kp.writeCarry _ _ (by decide))).trans
      (Kp.writeCarry _ _ (by decide))).trans (Kp.write _ _ (by decide))).trans
      (Kp.write _ _ (by decide))).trans (Kp.write _ _ (by decide))).trans
      (Kp.write _ _ (by decide))).trans (Kp.write _ _ (by decide)))

end VG.Proof.Mont.PPC64LE
