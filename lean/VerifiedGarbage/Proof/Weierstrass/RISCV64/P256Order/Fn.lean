module

public import VerifiedGarbage.Impl.Weierstrass.RISCV64.P256Order
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.P256Field.Fn
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad64
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.X448.RISCV64.R64.Product

/-!
# Arithmetic modulo P-256's order on RISC-V: the operations

The operations of `Impl/Weierstrass/RISCV64/P256Order.lean` meet `CoreOk`
(`mulCore_core`, `addCore_core`, `subCore_core`) by the lemmas of P-256's
field (`mulWith_ok`, `addWith_ok`, `subWith_ok`), from the reduction
(`reduce_ok`), the sum `x + (2²⁵⁶ - n)` (`sumN_ok`) and the words of `n`
under a mask (`kN0`–`kN3`).

The reduction is P-256's (`RedInv`), with `q n` added in a round
(`round_ok`): the quotient word and the low product words (`qprod_ok`; the
carry out of `w + q n₀` is `q ≠ 0`, `mont_carry`), the words of
`q (n₂ + 2⁶⁴ n₃)` (`quot_ok`, `qk_ok`), and the sums, whose numbers add up
(`round_arith`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.RISCV64.P256Order

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide
open VG.Impl.Weierstrass.RISCV64.P256Field
open VG.Impl.Weierstrass.RISCV64.P256Order (qprod qk sumN NINV N0 N1 C0 C1)
open VG.Proof.Weierstrass.RISCV64.P256Field
open VG.Proof.X25519.RISCV64 (Ctx Rest wp_mul)
open VG.Proof.X448.RISCV64.R64 (dw dw_lt ld_ok clob64 Keeps.rest)
open VG.Impl.Words.RISCV64 (li64)

/-- P-256's order. -/
abbrev N : Nat := 0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551

/-! ## Arithmetic -/

theorem mont_mod (w : Nat) :
    (w + (w * 0xccd1c8aaee00bc4f % 2 ^ 64) * 0xf3b9cac2fc632551) % 2 ^ 64 = 0 := by
  rw [Nat.add_mod, Nat.mod_mul_mod, ← Nat.add_mod,
    show w + w * 0xccd1c8aaee00bc4f * 0xf3b9cac2fc632551 = 2 ^ 64 * (w * 0xc2ffc74dccaf7720) by omega,
    Nat.mul_mod_right]

/-- The carry out of `w + q n₀`, for the quotient word `q = w n' mod 2⁶⁴`, is `q ≠ 0`. -/
theorem mont_carry (w : Nat) (hw : w < 2 ^ 64) :
    w + (w * 0xccd1c8aaee00bc4f % 2 ^ 64) * 0xf3b9cac2fc632551 =
      2 ^ 64 * ((w * 0xccd1c8aaee00bc4f % 2 ^ 64) * 0xf3b9cac2fc632551 / 2 ^ 64 +
        if 0 < w * 0xccd1c8aaee00bc4f % 2 ^ 64 then 1 else 0) := by
  have h0 := mont_mod w
  have hz : w = 0 → w * 0xccd1c8aaee00bc4f % 2 ^ 64 = 0 := by rintro rfl; rfl
  generalize w * 0xccd1c8aaee00bc4f % 2 ^ 64 = q at *
  have hd := Nat.div_add_mod (q * 0xf3b9cac2fc632551) (2 ^ 64)
  have hl := Nat.mod_lt (q * 0xf3b9cac2fc632551) (show 0 < 2 ^ 64 by decide)
  have hq0 : q = 0 → q * 0xf3b9cac2fc632551 = 0 := by rintro rfl; rfl
  generalize q * 0xf3b9cac2fc632551 / 2 ^ 64 = H at *
  generalize q * 0xf3b9cac2fc632551 % 2 ^ 64 = L at *
  generalize q * 0xf3b9cac2fc632551 = X at *
  split <;> omega

/-- The numbers of a round. -/
theorem round_arith {w0 w1 w2 w3 w4 cy U q y0 y1 w1' c1 w2m c2 x0 x1 k0 k1 k2 w2' c3 t w3m d1 w3' d2 e
      w4' cy' : Nat}
    (F1 : w0 + q * 0xf3b9cac2fc632551 + 2 ^ 64 * (q * 0xbce6faada7179e84) = 2 ^ 64 * (y0 + 2 ^ 64 * y1))
    (F3 : w1' + 2 ^ 64 * c1 = w1 + y0)
    (F4 : w2m + 2 ^ 64 * c2 = w2 + y1 + c1)
    (F5 : x0 + 2 ^ 64 * x1 = q * (2 ^ 64 - 2 ^ 32 + 1))
    (F6 : k0 + 2 ^ 64 * k1 + 2 ^ 128 * k2 + q = 2 ^ 64 * (x0 + 2 ^ 64 * x1))
    (F7 : w2' + 2 ^ 64 * c3 = w2m + k0) (F7b : t = c3 + c2)
    (F8 : w3m + 2 ^ 64 * d1 = w3 + t) (F9 : w3' + 2 ^ 64 * d2 = w3m + k1) (F9b : e = d1 + d2)
    (F10 : w4' + 2 ^ 64 * cy' = w4 + k2 + e + cy) :
    2 ^ 64 * (w1' + 2 ^ 64 * w2' + 2 ^ 128 * w3' + 2 ^ 192 * w4' + 2 ^ 256 * (cy' + U)) =
      w0 + 2 ^ 64 * w1 + 2 ^ 128 * w2 + 2 ^ 192 * w3 + 2 ^ 256 * (cy + (w4 + 2 ^ 64 * U)) + q * N := by
  simp only [N]
  omega

/-! ## Steps -/

section
variable {s : State} {is : List Instr} {Q : State → Prop}

/-- `li64 d tmp v`. -/
theorem wp_li64 {d tmp : Reg} (hdt : d ≠ tmp) (v : BitVec 64)
    (k : ∀ s', s'.gpr d = v → Keeps [d, tmp] s s' → WP isa (.block is) s' Q) :
    WP isa (.block (li64 d tmp v ++ is)) s Q :=
  WP.block_append (WP.mono (ByteLoad.li64_ok hdt v) fun s' h => by
    subst h
    exact k _ (RegUpd.gpr_write_self _ _ _)
      (((Keeps.refl [d, tmp] s).write _ (by simp)).write _ (by simp)))

theorem wp_mulhu {d n m : Reg}
    (k : ∀ s', Upd s s' d (BitVec.ofNat 64 ((s.gpr n).toNat * (s.gpr m).toNat / 2 ^ 64)) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.mulhu d n m :: is)) s Q :=
  WP.cons exec_mulhu (k _ (Upd.write _ _ _))

end

/-- The registers of the rounds are none of the temporaries. -/
theorem rw_ne (j : Nat) : rw j ≠ .t0 ∧ rw j ≠ .a0 ∧ rw j ≠ .a2 ∧ rw j ≠ .a3 ∧ rw j ≠ .a4 ∧
    rw j ≠ .a5 ∧ rw j ≠ .a6 ∧ rw j ≠ .a7 ∧ rw j ∈ clob64 := by
  have : j % 5 < 5 := Nat.mod_lt _ (by decide)
  obtain h | h | h | h | h : j % 5 = 0 ∨ j % 5 = 1 ∨ j % 5 = 2 ∨ j % 5 = 3 ∨ j % 5 = 4 := by omega
  all_goals simp only [rw, RW, h]; decide

theorem ofNat_lt {x : Nat} (h : x < 2 ^ 64) : (BitVec.ofNat 64 x).toNat = x := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem qprod_arith {w q a4 b h a5 a6 sm c y1 : Nat}
    (hmc : w + q * 0xf3b9cac2fc632551 = 2 ^ 64 * (a4 + b)) (hh : h = a4 + b)
    (hmw : a5 + 2 ^ 64 * a6 = q * 0xbce6faada7179e84) (hc : sm + 2 ^ 64 * c = a5 + h) (hy : y1 = a6 + c) :
    w + q * 0xf3b9cac2fc632551 + 2 ^ 64 * (q * 0xbce6faada7179e84) = 2 ^ 64 * (sm + 2 ^ 64 * y1) := by
  omega

/-- A sum of words that does not wrap around. -/
theorem add_toNat {x y : BitVec 64} (h : x.toNat + y.toNat < 2 ^ 64) : (x + y).toNat = x.toNat + y.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

/-- `qprod i`: the quotient word `q = w n' mod 2⁶⁴` of `w` in `rw i`, in place, and
`a5 + 2⁶⁴ a6 = (w + q n₀) / 2⁶⁴ + q n₁`. -/
theorem qprod_ok {s : State} (i : Nat) :
    WP isa (.block (qprod i)) s fun s' =>
      (s'.gpr (rw i)).toNat = (s.gpr (rw i)).toNat * 0xccd1c8aaee00bc4f % 2 ^ 64 ∧
      (s.gpr (rw i)).toNat + (s'.gpr (rw i)).toNat * 0xf3b9cac2fc632551 +
          2 ^ 64 * ((s'.gpr (rw i)).toNat * 0xbce6faada7179e84) =
        2 ^ 64 * ((s'.gpr .a5).toNat + 2 ^ 64 * (s'.gpr .a6).toNat) ∧
      Keeps [rw i, .t0, .a0, .a4, .a5, .a6, .a7] s s' := by
  obtain ⟨n0, na0, -, -, n4, n5, n6, n7, -⟩ := rw_ne i
  unfold qprod
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_li64 (by decide) NINV fun s1 e1 k1 => wp_mul fun s2 u2 => ?_
  refine wp_li64 (by decide) N0 fun s3 e3 k3 => wp_mulhu fun s4 u4 => ?_
  refine wp_li64 (by decide) N1 fun s5 e5 k5 => wp_mulhu fun s6 u6 => wp_mul fun s7 u7 => ?_
  refine wp_li (imm := 0) (by decide) fun s8 u8 => wp_sltu fun s9 u9 => wp_add fun s10 u10 => ?_
  refine wp_add fun s11 u11 => wp_sltu fun s12 u12 => wp_add fun s13 u13 => WP.block_nil ?_
  -- The quotient word, through the steps.
  have hq2 : s2.gpr (rw i) = s.gpr (rw i) * NINV := by
    rw [u2.gpr, e1, k1.1 _ (by simp [n0, na0])]
  have q3 : s3.gpr (rw i) = s2.gpr (rw i) := k3.1 _ (by simp [n4, na0])
  have q5 : s5.gpr (rw i) = s2.gpr (rw i) := by rw [k5.1 _ (by simp [n5, na0]), u4.other _ n4, q3]
  have q8 : s8.gpr (rw i) = s2.gpr (rw i) := by
    rw [u8.other _ na0, u7.other _ n5, u6.other _ n6, q5]
  have q13 : s13.gpr (rw i) = s2.gpr (rw i) := by
    rw [u13.other _ n6, u12.other _ n7, u11.other _ n5, u10.other _ n4,
      u9.other _ na0, q8]
  have hqn : (s2.gpr (rw i)).toNat = (s.gpr (rw i)).toNat * 0xccd1c8aaee00bc4f % 2 ^ 64 := by
    rw [hq2, BitVec.toNat_mul]; rfl
  -- The words.
  have a4_9 : s9.gpr .a4 = s4.gpr .a4 := by
    rw [u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide), u6.other _ (by decide),
      k5.1 _ (by decide)]
  have hA4 : s4.gpr .a4 = BitVec.ofNat 64 ((s2.gpr (rw i)).toNat * 0xf3b9cac2fc632551 / 2 ^ 64) := by
    rw [u4.gpr, q3, e3]; rfl
  have hA6 : s6.gpr .a6 = BitVec.ofNat 64 ((s2.gpr (rw i)).toNat * N1.toNat / 2 ^ 64) := by
    rw [u6.gpr, q5, e5]
  have hA5 : s7.gpr .a5 = s2.gpr (rw i) * N1 := by
    rw [u7.gpr, u6.other _ n6, q5, u6.other .a5 (by decide), e5]
  have hB : s9.gpr .a0 = if (0 : BitVec 64) < s2.gpr (rw i) then 1 else 0 := by
    rw [u9.gpr, u8.gpr, q8]; rfl
  have hH : s10.gpr .a4 = s4.gpr .a4 + s9.gpr .a0 := by rw [u10.gpr, a4_9]
  have a5_10 : s10.gpr .a5 = s7.gpr .a5 := by
    rw [u10.other _ (by decide), u9.other _ (by decide), u8.other _ (by decide)]
  have a6_12 : s12.gpr .a6 = s6.gpr .a6 := by
    rw [u12.other _ (by decide), u11.other _ (by decide), u10.other _ (by decide), u9.other _ (by decide),
      u8.other _ (by decide), u7.other _ (by decide)]
  have hS : s11.gpr .a5 = s7.gpr .a5 + s10.gpr .a4 := by rw [u11.gpr, a5_10]
  have hC : s12.gpr .a7 = if s11.gpr .a5 < s10.gpr .a4 then 1 else 0 := by
    rw [u12.gpr, u11.other .a4 (by decide)]
  have hY : s13.gpr .a6 = s6.gpr .a6 + s12.gpr .a7 := by rw [u13.gpr, a6_12]
  have hS13 : s13.gpr .a5 = s11.gpr .a5 := by rw [u13.other _ (by decide), u12.other _ (by decide)]
  -- Their numbers.
  have bq := (s2.gpr (rw i)).isLt
  have bA4 : (s4.gpr .a4).toNat + 1 < 2 ^ 64 := by
    rw [hA4, ofNat_lt (Nat.div_lt_of_lt_mul (by omega))]; omega
  have bB : (s9.gpr .a0).toNat ≤ 1 := by rw [hB]; exact carry_le _
  have eH : (s10.gpr .a4).toNat = (s4.gpr .a4).toNat + (s9.gpr .a0).toNat := by
    rw [hH]; exact add_toNat (by omega)
  have mw := mul_words (s2.gpr (rw i)) N1
  rw [← hA5, ← hA6] at mw
  have bA6 : (s6.gpr .a6).toNat + 1 < 2 ^ 64 := by
    have := (s7.gpr .a5).isLt
    have : (s2.gpr (rw i)).toNat * N1.toNat < 2 ^ 64 * (2 ^ 64 - 2) := by
      rw [show N1.toNat = 0xbce6faada7179e84 from rfl]; omega
    omega
  have cc := carry (s7.gpr .a5) (s10.gpr .a4)
  rw [← hS, ← hC] at cc
  have eY : (s13.gpr .a6).toNat = (s6.gpr .a6).toNat + (s12.gpr .a7).toNat := by
    rw [hY]; exact add_toNat (by have := carry_le (s11.gpr .a5 < s10.gpr .a4); rw [← hC] at this; omega)
  have mc := mont_carry (s.gpr (rw i)).toNat (BitVec.isLt _)
  rw [← hqn] at mc
  have eB : (s9.gpr .a0).toNat = if 0 < (s2.gpr (rw i)).toNat then 1 else 0 := by
    rw [hB, sltu_toNat]; rfl
  have eA4 : (s4.gpr .a4).toNat = (s2.gpr (rw i)).toNat * 0xf3b9cac2fc632551 / 2 ^ 64 := by
    rw [hA4]; exact ofNat_lt (Nat.div_lt_of_lt_mul (by omega))
  rw [← eB, ← eA4] at mc
  refine ⟨by rw [q13, hqn], ?_, ?_⟩
  · rw [q13, hS13]
    exact qprod_arith mc eH (by rw [show N1.toNat = 0xbce6faada7179e84 from rfl] at mw; exact mw) cc eY
  · refine ⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hr
      rw [u13.other _ h5, u12.other _ h6, u11.other _ h4, u10.other _ h3, u9.other _ h2, u8.other _ h2,
        u7.other _ h4, u6.other _ h5, k5.1 _ (by simp [h4, h2]), u4.other _ h3, k3.1 _ (by simp [h3, h2]),
        u2.other _ h0, k1.1 _ (by simp [h1, h2])]
    · rw [u13.mem, u12.mem, u11.mem, u10.mem, u9.mem, u8.mem, u7.mem, u6.mem, k5.2.1, u4.mem, k3.2.1,
        u2.mem, k1.2.1]
    · rw [u13.rd, u12.rd, u11.rd, u10.rd, u9.rd, u8.rd, u7.rd, u6.rd, k5.2.2.1, u4.rd, k3.2.2.1,
        u2.rd, k1.2.2.1]
    · rw [u13.wr, u12.wr, u11.wr, u10.wr, u9.wr, u8.wr, u7.wr, u6.wr, k5.2.2.2.1, u4.wr, k3.2.2.2.1,
        u2.wr, k1.2.2.2.1]
    · rw [u13.sp, u12.sp, u11.sp, u10.sp, u9.sp, u8.sp, u7.sp, u6.sp, k5.2.2.2.2, u4.sp, k3.2.2.2.2,
        u2.sp, k1.2.2.2.2]

/-- `qk i`: from `X = a6 + 2⁶⁴ a7 = q (2⁶⁴ - 2³² + 1)` for `q` in `rw i`, the words
`a4`, `a6`, `a7` of `2⁶⁴ X - q`. -/
theorem qk_ok {s : State} (i : Nat)
    (hX : (s.gpr .a6).toNat + 2 ^ 64 * (s.gpr .a7).toNat = (s.gpr (rw i)).toNat * (2 ^ 64 - 2 ^ 32 + 1)) :
    WP isa (.block (qk i)) s fun s' =>
      (s'.gpr .a4).toNat + 2 ^ 64 * (s'.gpr .a6).toNat + 2 ^ 128 * (s'.gpr .a7).toNat + (s.gpr (rw i)).toNat =
        2 ^ 64 * ((s.gpr .a6).toNat + 2 ^ 64 * (s.gpr .a7).toNat) ∧
      (s'.gpr .a7).toNat ≤ (s.gpr .a7).toNat ∧ Keeps [.t0, .a4, .a5, .a6, .a7] s s' := by
  obtain ⟨n0, -, -, -, n4, n5, n6, n7, -⟩ := rw_ne i
  unfold qk
  refine wp_li (imm := 0) (by decide) fun s1 u1 => wp_sub fun s2 u2 => wp_sltu fun s3 u3 => ?_
  refine wp_sltu fun s4 u4 => wp_sub fun s5 u5 => wp_sub fun s6 u6 => WP.block_nil ?_
  have r1 : s1.gpr (rw i) = s.gpr (rw i) := u1.other _ n0
  have r2 : s2.gpr (rw i) = s.gpr (rw i) := by rw [u2.other _ n4, r1]
  have z1 : (s1.gpr .t0).toNat = 0 := by rw [u1.gpr]; rfl
  have z2 : s2.gpr .t0 = s1.gpr .t0 := u2.other _ (by decide)
  -- The words.
  have hA4 := sub_borrow (s1.gpr .t0) (s1.gpr (rw i))
  rw [← u2.gpr, z1, r1] at hA4
  have hb : (s3.gpr .t0).toNat = if 0 < (s.gpr (rw i)).toNat then 1 else 0 := by
    rw [u3.gpr, sltu_toNat, z2, z1, r2]
  have a6_3 : s3.gpr .a6 = s.gpr .a6 := by
    rw [u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide)]
  have a7_5 : s5.gpr .a7 = s.gpr .a7 := by
    rw [u5.other _ (by decide), u4.other _ (by decide), u3.other .a7 (by decide),
      u2.other _ (by decide), u1.other _ (by decide)]
  have hc : (s4.gpr .a5).toNat = if (s.gpr .a6).toNat < (s3.gpr .t0).toNat then 1 else 0 := by
    rw [u4.gpr, sltu_toNat, a6_3]
  have hA6 := sub_borrow (s4.gpr .a6) (s4.gpr .t0)
  rw [← u5.gpr, u4.other .a6 (by decide), a6_3, u4.other .t0 (by decide)] at hA6
  have hA7 := sub_borrow (s5.gpr .a7) (s5.gpr .a5)
  rw [← u6.gpr, a7_5, u5.other .a5 (by decide)] at hA7
  have e4 : s6.gpr .a4 = s2.gpr .a4 := by
    rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide)]
  have e6 : s6.gpr .a6 = s5.gpr .a6 := u6.other _ (by decide)
  rw [e4, e6]
  have := (s.gpr (rw i)).isLt
  have := (s.gpr .a6).isLt
  have := (s.gpr .a7).isLt
  have := (s2.gpr .a4).isLt
  have := (s5.gpr .a6).isLt
  have := (s6.gpr .a7).isLt
  generalize (s.gpr (rw i)).toNat = q at *
  generalize (s.gpr .a6).toNat = A6 at *
  generalize (s.gpr .a7).toNat = A7 at *
  generalize (s3.gpr .t0).toNat = b at *
  generalize (s4.gpr .a5).toNat = c at *
  refine ⟨?_, ?_, ?_⟩
  · split at hb <;> split at hc <;> split at hA4 <;> split at hA6 <;> split at hA7 <;> omega
  · split at hb <;> split at hc <;> split at hA7 <;> omega
  · refine ⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      obtain ⟨h0, h4, h5, h6, h7⟩ := hr
      rw [u6.other _ h7, u5.other _ h6, u4.other _ h5, u3.other _ h0, u2.other _ h4, u1.other _ h0]
    · rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
    · rw [u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd]
    · rw [u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr]
    · rw [u6.sp, u5.sp, u4.sp, u3.sp, u2.sp, u1.sp]

/-! ## The reduction -/

/-- Facts of a round's indices and bounds, apart from the round's large context. -/
theorem idx (i : Nat) : i + 1 + 1 = i + 2 ∧ i + 1 + 2 = i + 3 ∧ i + 1 + 3 = i + 4 ∧ i + 1 + 4 = i + 5 ∧
    (i < 4 → 4 - (i + 1) = 3 - i) ∧ (i < 4 → 4 - i = (3 - i) + 1) := by omega

theorem pow64_succ (i : Nat) : 2 ^ (64 * (i + 1)) = 2 ^ (64 * i) * 2 ^ 64 := by
  rw [Nat.mul_succ, Nat.pow_add]

theorem carry1 {x c a p q r : Nat} (hx : x + 2 ^ 64 * c = a + p + q + r) (ha : a < 2 ^ 64)
    (hb : p + q + r < 2 ^ 64) : c ≤ 1 := by
  omega

theorem round_val {Q q E W W' Pr : Nat} (hQ : Q < E) (hq : q < 2 ^ 64) (hv : W * E = Pr + Q * N)
    (key : 2 ^ 64 * W' = W + q * N) : Q + q * E < E * 2 ^ 64 ∧ W' * (E * 2 ^ 64) = Pr + (Q + q * E) * N := by
  constructor
  · have : (q + 1) * E ≤ 2 ^ 64 * E := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, Nat.one_mul] at this
    rw [Nat.mul_comm E]
    omega
  · have : W' * (E * 2 ^ 64) = (2 ^ 64 * W') * E := by
      rw [Nat.mul_comm E, ← Nat.mul_assoc, Nat.mul_comm W']
    rw [this, key, Nat.add_mul, hv]
    grind


/-- After `i` rounds, from `s0`: P-256's invariant (`RedInv`) with `n`. -/
structure RedInv (b : Addr) (s0 : State) (i : Nat) (s : State) : Prop where
  ctx : Ctx b s
  rest : Rest clobM s0 s
  mem : s.mem = s0.mem
  cy : (s.gpr .a2).toNat ≤ 1
  val : ∃ Q, Q < 2 ^ (64 * i) ∧ wv s0.mem b i s * 2 ^ (64 * i) = prodV s0.mem b + Q * N

/-- A register outside `rs` is kept by `Keeps rs`, as the lists are short. -/
theorem kp {rs : List Reg} {s s' : State} (h : Keeps rs s s') {r : Reg} (hr : r ∉ rs) :
    s'.gpr r = s.gpr r := h.1 r hr

/-- Round `i`. -/
theorem round_ok {b : Addr} {s0 : State} {i : Nat} (hi : i < 4) {s : State} (h : RedInv b s0 i s) :
    WP isa (.block (Impl.Weierstrass.RISCV64.P256Order.round i)) s (RedInv b s0 (i + 1)) := by
  obtain ⟨d01, d02, d03, d04, d12, d13, d14, d23, d24, d34, dk⟩ := rw_facts i hi
  obtain ⟨n02, n04, n05, n06, n07, n0t, n03, c0⟩ := dk 0 (by decide)
  obtain ⟨n12, n14, n15, n16, n17, n1t, n13, c1⟩ := dk 1 (by decide)
  obtain ⟨n22, n24, n25, n26, n27, n2t, n23, c2⟩ := dk 2 (by decide)
  obtain ⟨n32, n34, n35, n36, n37, n3t, n33, c3⟩ := dk 3 (by decide)
  obtain ⟨n42, n44, n45, n46, n47, n4t, n43, c4⟩ := dk 4 (by decide)
  simp only [Nat.add_zero] at n02 n04 n05 n06 n07 n0t n03 c0
  have a0 := fun k => (rw_ne (i + k)).2.1
  have n0a := (rw_ne i).2.1
  have n1a := a0 1
  have n2a := a0 2
  have n3a := a0 3
  have n4a := a0 4
  have hc := h.ctx
  have hd : ACC + 8 * (i + 4) + 8 ≤ 2048 := by simp only [ACC]; omega
  unfold Impl.Weierstrass.RISCV64.P256Order.round
  simp only [List.append_assoc]
  refine ld_ok hc hd (by simp only [ACC]; omega) fun s1 u1 => ?_
  have hT4 : (s1.gpr (rw (i + 4))).toNat = T s0.mem b (i + 4) := by
    rw [u1.gpr, ← h.mem]; rfl
  show WP isa (.block (qprod i ++ _)) s1 _
  refine WP.block_append (WP.mono (qprod_ok i) fun s2 ⟨q1, q2, k2⟩ => ?_)
  refine WP.block_append (WP.mono (add1_ok (d := rw (i + 1)) (y := .a5) (c := .a0) n15 n1a)
    fun s3 ⟨e3, k3⟩ => ?_)
  refine WP.block_append (WP.mono (adc_ok (d := rw (i + 2)) (x := rw (i + 2)) (y := .a6) (c := .a0) (u := .a7)
    n26 n2a (Ne.symm n27) (by decide)) fun s4 ⟨e4, k4⟩ => ?_)
  refine WP.block_append (WP.mono (quot_ok (r := rw i) n04 n05 n06 n07) fun s5 ⟨x1, x2, x3, x4, k5⟩ => ?_)
  -- The quotient word, kept.
  have g1 : ∀ r, r ≠ rw (i + 4) → s1.gpr r = s.gpr r := u1.other
  have q4 : s4.gpr (rw i) = s2.gpr (rw i) := by
    rw [kp k4 (by simp [d02, n07, n0a]), kp k3 (by simp [d01, n0a])]
  have q5 : s5.gpr (rw i) = s2.gpr (rw i) := by rw [kp k5 (by simp [n04, n05, n06, n07, n0t]), q4]
  rw [q4] at x2
  refine WP.block_append (WP.mono (qk_ok i (by rw [q5]; exact x2)) fun s6 ⟨f6, b6, k6⟩ => ?_)
  rw [q5] at f6
  show WP isa (.block ([.add (rw (i + 2)) (rw (i + 2)) .a4, .sltu .t0 (rw (i + 2)) .a4] ++
    (.add .t0 .t0 .a0 :: _))) s6 _
  refine WP.block_append (WP.mono (add1_ok (d := rw (i + 2)) (y := .a4) (c := .t0) n24 n2t)
    fun s7 ⟨e7, k7⟩ => wp_add fun s8 u8 => ?_)
  show WP isa (.block ([.add (rw (i + 3)) (rw (i + 3)) .t0, .sltu .a0 (rw (i + 3)) .t0] ++ _)) s8 _
  refine WP.block_append (WP.mono (add1_ok (d := rw (i + 3)) (y := .t0) (c := .a0) n3t n3a)
    fun s9 ⟨e9, k9⟩ => ?_)
  show WP isa (.block ([.add (rw (i + 3)) (rw (i + 3)) .a6, .sltu .a5 (rw (i + 3)) .a6] ++
    (.add .a0 .a0 .a5 :: _))) s9 _
  refine WP.block_append (WP.mono (add1_ok (d := rw (i + 3)) (y := .a6) (c := .a5) n36 n35)
    fun s10 ⟨e10, k10⟩ => wp_add fun s11 u11 => ?_)
  show WP isa (.block [.add .a7 .a7 .a0, .add .a7 .a7 .a2, .add (rw (i + 4)) (rw (i + 4)) .a7,
    .sltu .a2 (rw (i + 4)) .a7]) s11 _
  refine WP.mono (addTop_ok (d := rw (i + 4)) (h := .a7) (c := .a0) (k := .a2) n47 n42 (by decide))
    fun s12 ⟨e12, k12⟩ => ?_
  -- What each step read, through the steps before it.
  have w1_2 : s2.gpr (rw (i + 1)) = s.gpr (rw (i + 1)) := by
    rw [kp k2 (by simp [Ne.symm d01, n1t, n1a, n14, n15, n16, n17]), g1 _ d14]
  have w2_3 : s3.gpr (rw (i + 2)) = s.gpr (rw (i + 2)) := by
    rw [kp k3 (by simp [Ne.symm d12, n2a]), kp k2 (by simp [Ne.symm d02, n2t, n2a, n24, n25, n26, n27]),
      g1 _ d24]
  have a6_3 : s3.gpr .a6 = s2.gpr .a6 := kp k3 (by simp [Ne.symm n16])
  have a0_3 : (s3.gpr .a0).toNat ≤ 1 := by
    have := (s3.gpr (rw (i + 1))).isLt; have := (s2.gpr (rw (i + 1))).isLt; have := (s2.gpr .a5).isLt
    omega
  have e4' := e4 a0_3
  rw [w2_3, a6_3] at e4'
  rw [w1_2] at e3
  have w2_6 : s6.gpr (rw (i + 2)) = s4.gpr (rw (i + 2)) := by
    rw [kp k6 (by simp [n2t, n24, n25, n26, n27]), kp k5 (by simp [n2t, n24, n25, n26, n27])]
  rw [w2_6] at e7
  have a0_7 : s7.gpr .a0 = s4.gpr .a0 := by
    rw [kp k7 (by simp [Ne.symm n2a]), kp k6 (by decide), kp k5 (by decide)]
  have t0_8 : (s8.gpr .t0).toNat = (s7.gpr .t0).toNat + (s4.gpr .a0).toNat := by
    rw [u8.gpr, ← a0_7]
    refine add_toNat ?_
    have := (s7.gpr (rw (i + 2))).isLt; have := (s6.gpr (rw (i + 2))).isLt; have := (s6.gpr .a4).isLt
    have := (s4.gpr (rw (i + 2))).isLt; have := (s.gpr (rw (i + 2))).isLt; have := (s2.gpr .a6).isLt
    rw [a0_7]; omega
  have w3_8 : s8.gpr (rw (i + 3)) = s.gpr (rw (i + 3)) := by
    rw [u8.other _ n3t, kp k7 (by simp [Ne.symm d23, n3t]),
      kp k6 (by simp [n3t, n34, n35, n36, n37]), kp k5 (by simp [n3t, n34, n35, n36, n37]),
      kp k4 (by simp [Ne.symm d23, n37, n3a]), kp k3 (by simp [Ne.symm d13, n3a]),
      kp k2 (by simp [Ne.symm d03, n3t, n3a, n34, n35, n36, n37]), g1 _ d34]
  rw [w3_8] at e9
  have a6_9 : s9.gpr .a6 = s6.gpr .a6 := by
    rw [kp k9 (by simp [Ne.symm n36]), u8.other _ (by decide), kp k7 (by simp [Ne.symm n26])]
  rw [a6_9] at e10
  have a0_10 : s10.gpr .a0 = s9.gpr .a0 := kp k10 (by simp [Ne.symm n3a])
  have a0_11 : (s11.gpr .a0).toNat = (s9.gpr .a0).toNat + (s10.gpr .a5).toNat := by
    rw [u11.gpr, a0_10]
    refine add_toNat ?_
    have := (s9.gpr (rw (i + 3))).isLt; have := (s10.gpr (rw (i + 3))).isLt; have := (s6.gpr .a6).isLt
    have := (s8.gpr (rw (i + 3))).isLt; have := (s.gpr (rw (i + 3))).isLt
    have := (s7.gpr .t0).isLt; have := (s4.gpr .a0).isLt
    omega
  have w4_11 : s11.gpr (rw (i + 4)) = s1.gpr (rw (i + 4)) := by
    rw [u11.other _ n4a, kp k10 (by simp [Ne.symm d34, n45]), kp k9 (by simp [Ne.symm d34, n4a]),
      u8.other _ n4t, kp k7 (by simp [Ne.symm d24, n4t]),
      kp k6 (by simp [n4t, n44, n45, n46, n47]), kp k5 (by simp [n4t, n44, n45, n46, n47]),
      kp k4 (by simp [Ne.symm d24, n47, n4a]), kp k3 (by simp [Ne.symm d14, n4a]),
      kp k2 (by simp [Ne.symm d04, n4t, n4a, n44, n45, n46, n47])]
  have a7_11 : s11.gpr .a7 = s6.gpr .a7 := by
    rw [u11.other _ (by decide), kp k10 (by simp [Ne.symm n37]), kp k9 (by simp [Ne.symm n37]),
      u8.other _ (by decide), kp k7 (by simp [Ne.symm n27])]
  have a2_11 : s11.gpr .a2 = s.gpr .a2 := by
    rw [u11.other _ (by decide), kp k10 (by simp [Ne.symm n32]), kp k9 (by simp [Ne.symm n32]),
      u8.other _ (by decide), kp k7 (by simp [Ne.symm n22]), kp k6 (by decide), kp k5 (by decide),
      kp k4 (by simp [Ne.symm n22]), kp k3 (by simp [Ne.symm n12]),
      kp k2 (by simp [Ne.symm n02]), g1 _ (Ne.symm n42)]
  have hcy := h.cy
  have hcond : (s6.gpr .a7).toNat + (s11.gpr .a0).toNat + (s.gpr .a2).toNat < 2 ^ 64 := by
    rw [a0_11]
    have := (s9.gpr (rw (i + 3))).isLt; have := (s10.gpr (rw (i + 3))).isLt; have := (s6.gpr .a6).isLt
    have := (s8.gpr (rw (i + 3))).isLt; have := (s.gpr (rw (i + 3))).isLt
    rw [t0_8] at e9
    have := (s7.gpr (rw (i + 2))).isLt; have := (s6.gpr .a4).isLt; have := (s4.gpr (rw (i + 2))).isLt
    have := (s.gpr (rw (i + 2))).isLt; have := (s2.gpr .a6).isLt
    omega
  have e12' := e12 (by rw [a7_11, a2_11]; exact hcond)
  rw [w4_11, hT4, a7_11, a2_11] at e12'
  rw [t0_8] at e9
  -- The new registers, read from the last state.
  have o1 : s12.gpr (rw (i + 1)) = s3.gpr (rw (i + 1)) := by
    rw [kp k12 (by simp [d14, n17, n12]), u11.other _ n1a, kp k10 (by simp [d13, n15]),
      kp k9 (by simp [d13, n1a]), u8.other _ n1t, kp k7 (by simp [d12, n1t]),
      kp k6 (by simp [n1t, n14, n15, n16, n17]), kp k5 (by simp [n1t, n14, n15, n16, n17]),
      kp k4 (by simp [d12, n17, n1a])]
  have o2 : s12.gpr (rw (i + 2)) = s7.gpr (rw (i + 2)) := by
    rw [kp k12 (by simp [d24, n27, n22]), u11.other _ n2a, kp k10 (by simp [d23, n25]),
      kp k9 (by simp [d23, n2a]), u8.other _ n2t]
  have o3 : s12.gpr (rw (i + 3)) = s10.gpr (rw (i + 3)) := by
    rw [kp k12 (by simp [d34, n37, n32]), u11.other _ n3a]
  -- The frame.
  have sub : ∀ r ∈ clob64, r ∈ clobM := by decide
  have cons : ∀ {r : Reg} {l : List Reg}, r ∈ clob64 → (∀ x ∈ l, x ∈ clobM) → ∀ x ∈ r :: l, x ∈ clobM :=
    fun hr hl x hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact sub _ hr
      · exact hl x hx
  have hrest : Rest clobM s s12 :=
    (u1.rest (sub _ c4)).trans <| ((Keeps.rest k2).mono (cons c0 (by decide))).trans <|
      ((Keeps.rest k3).mono (cons c1 (by decide))).trans <| ((Keeps.rest k4).mono (cons c2 (by decide))).trans <|
      ((Keeps.rest k5).mono (by decide)).trans <| ((Keeps.rest k6).mono (by decide)).trans <|
      ((Keeps.rest k7).mono (cons c2 (by decide))).trans <| (u8.rest (by decide)).trans <|
      ((Keeps.rest k9).mono (cons c3 (by decide))).trans <| ((Keeps.rest k10).mono (cons c3 (by decide))).trans <|
      (u11.rest (by decide)).trans ((Keeps.rest k12).mono (cons c4 (by decide)))
  have hm : s12.mem = s0.mem := by
    rw [k12.2.1, u11.mem, k10.2.1, k9.2.1, u8.mem, k7.2.1, k6.2.1, k5.2.1, k4.2.1, k3.2.1, k2.2.1,
      u1.mem, h.mem]
  obtain ⟨i1, i2, i3, i4, i5, i6⟩ := idx i
  have hup : upW s0.mem b (i + 4) (4 - i) = T s0.mem b (i + 4) + 2 ^ 64 * upW s0.mem b (i + 5) (3 - i) := by
    rw [i6 hi]; rfl
  rw [g1 _ d04] at q2
  have key : 2 ^ 64 * wv s0.mem b (i + 1) s12 = wv s0.mem b i s + (s2.gpr (rw i)).toNat * N := by
    simp only [wv, i1, i2, i3, i4, i5 hi, hup, o1, o2, o3]
    exact round_arith q2 e3 e4' x2 f6 e7 rfl e9 e10 a0_11 e12'
  obtain ⟨Q, hQ, hv⟩ := h.val
  have cy := carry1 e12' (dw_lt _ _ _) hcond
  obtain ⟨v1, v2⟩ := round_val hQ (BitVec.isLt _) hv key
  refine ⟨hc.of_rest hrest (by decide), h.rest.trans hrest, hm, cy,
    ⟨Q + (s2.gpr (rw i)).toNat * 2 ^ (64 * i), by rw [pow64_succ]; exact v1, by rw [pow64_succ]; exact v2⟩⟩

/-- The rounds, by induction. -/
theorem rounds_ok {b : Addr} {s0 : State} : ∀ n ≤ 4, ∀ s, RedInv b s0 0 s →
    WP isa (.block ((List.range n).flatMap Impl.Weierstrass.RISCV64.P256Order.round)) s (RedInv b s0 n)
  | 0, _, s, h => WP.block_nil h
  | n + 1, hn, s, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.block_append (WP.mono (rounds_ok n (by omega) s h) fun s1 h1 => round_ok (by omega) h1)

/-- The initial loads, as P-256's. -/
theorem loads_ok {b : Addr} {s : State} (hc : Ctx b s) :
    WP isa (.block ((List.range 4).map (fun j => .load .d (rw j) .a3 (ACC + 8 * j)) ++ ([.li .a2 0] : List Instr))) s
      (RedInv b s 0) :=
  WP.mono (P256Field.loads_ok hc) fun _ h =>
    ⟨h.ctx, h.rest.mono (by decide), h.mem, h.cy, ⟨0, by decide, by
      obtain ⟨Q, hQ, hv⟩ := h.val
      have : Q = 0 := by simpa using hQ
      subst this
      simpa using hv⟩⟩

/-- `reduce`: `X + 2²⁵⁶ c` with `(X + 2²⁵⁶ c) 2²⁵⁶ = T + Q n` for some `Q < 2²⁵⁶`. -/
theorem reduce_ok {b : Addr} {s : State} (hc : Ctx b s) :
    WP isa (.block Impl.Weierstrass.RISCV64.P256Order.reduce) s fun s' =>
      Ctx b s' ∧ Rest clobM s s' ∧ s'.mem = s.mem ∧ (s'.gpr XC).toNat ≤ 1 ∧
      ∃ Q, Q < 2 ^ 256 ∧
        ((s'.gpr X0).toNat + 2 ^ 64 * (s'.gpr X1).toNat + 2 ^ 128 * (s'.gpr X2).toNat +
          2 ^ 192 * (s'.gpr X3).toNat + 2 ^ 256 * (s'.gpr XC).toNat) * 2 ^ 256 = prodV s.mem b + Q * N := by
  unfold Impl.Weierstrass.RISCV64.P256Order.reduce
  refine WP.block_append (WP.mono (loads_ok hc) fun s1 h1 => WP.mono (rounds_ok 4 (Nat.le_refl _) s1 h1)
    fun s2 h2 => ?_)
  obtain ⟨Q, hQ, hv⟩ := h2.val
  refine ⟨h2.ctx, h2.rest, h2.mem, h2.cy, Q, by simpa using hQ, ?_⟩
  simpa [wv, upW, X0, X1, X2, X3, XC, rw, RW] using hv

/-! ## The final subtraction -/

theorem sum_arith {x0 x1 x2 x3 y0 y1 y2 y3 c0 c1 c2 c3 : Nat}
    (e0 : y0 + 2 ^ 64 * c0 = x0 + 0x0c46353d039cdaaf)
    (e1 : y1 + 2 ^ 64 * c1 = x1 + 0x4319055258e8617b + c0)
    (e2 : y2 + 2 ^ 64 * c2 = x2 + c1)
    (e3 : y3 + 2 ^ 64 * c3 = x3 + (2 ^ 32 - 1) + c2) :
    y0 + 2 ^ 64 * y1 + 2 ^ 128 * y2 + 2 ^ 192 * y3 + 2 ^ 256 * c3 =
      x0 + 2 ^ 64 * x1 + 2 ^ 128 * x2 + 2 ^ 192 * x3 + (2 ^ 256 - N) := by
  simp only [N]
  omega

/-- `x + (2²⁵⁶ - n)` into `t6`, `a4`–`a6`, its carry into `a7`. -/
theorem sumN_ok {s : State} :
    WP isa (.block sumN) s fun s' =>
      v4 s' .t6 .a4 .a5 .a6 + 2 ^ 256 * (s'.gpr .a7).toNat = v4 s X0 X1 X2 X3 + (2 ^ 256 - N) ∧
      (s'.gpr .a7).toNat ≤ 1 ∧ Keeps clobC s s' := by
  unfold sumN csubWord
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_li64 (by decide) C0 fun s1 e1 k1 => wp_add fun s2 u2 => wp_sltu fun s3 u3 => ?_
  refine wp_li64 (by decide) C1 fun s4 e4 k4 => ?_
  refine WP.block_append (WP.mono (adc_ok (d := .a4) (x := X1) (y := .t0) (c := .a7) (u := .a0))
    fun s5 ⟨f5, k5⟩ => ?_)
  refine wp_add fun s6 u6 => wp_sltu fun s7 u7 => wp_lim1 fun s8 u8 => wp_srl (by decide) fun s9 u9 => ?_
  refine WP.mono (adc_ok (d := .a6) (x := X3) (y := .t0) (c := .a7) (u := .a0)) fun s10 ⟨f10, k10⟩ => ?_
  -- Word 0.
  have x0_1 : s1.gpr X0 = s.gpr X0 := kp k1 (by decide)
  have hs3 : s3.gpr .a7 = if s2.gpr .t6 < s1.gpr .t0 then 1 else 0 := by rw [u3.gpr, u2.other .t0 (by decide)]
  have c0 := carry (s1.gpr X0) (s1.gpr .t0)
  rw [← u2.gpr, ← hs3, x0_1, e1] at c0
  have t6_3 : s3.gpr .t6 = s2.gpr .t6 := u3.other _ (by decide)
  rw [← t6_3] at c0
  -- Word 1.
  have hc0 : (s4.gpr .a7).toNat ≤ 1 := by rw [kp k4 (by decide), u3.gpr]; exact sltu_le _
  have f5' := f5 hc0
  have x1_4 : s4.gpr X1 = s.gpr X1 := by
    rw [kp k4 (by decide), u3.other X1 (by decide), u2.other X1 (by decide), kp k1 (by decide)]
  have a7_4 : s4.gpr .a7 = s3.gpr .a7 := kp k4 (by decide)
  rw [e4, x1_4, a7_4] at f5'
  -- Word 2.
  have b5 := (s5.gpr .a4).isLt
  have x2_5 : s5.gpr X2 = s.gpr X2 := by
    rw [kp k5 (by decide), kp k4 (by decide), u3.other X2 (by decide), u2.other X2 (by decide),
      kp k1 (by decide)]
  have hs7 : s7.gpr .a7 = if s6.gpr .a5 < s5.gpr .a7 then 1 else 0 := by rw [u7.gpr, u6.other .a7 (by decide)]
  have c2 := carry (s5.gpr X2) (s5.gpr .a7)
  rw [← u6.gpr, ← hs7, x2_5] at c2
  -- Word 3.
  have ht0 : (s9.gpr .t0).toNat = 2 ^ 32 - 1 := by rw [u9.gpr, u8.gpr]; decide
  have a7_9 : s9.gpr .a7 = s7.gpr .a7 := by rw [u9.other _ (by decide), u8.other _ (by decide)]
  have hc2 : (s9.gpr .a7).toNat ≤ 1 := by rw [a7_9, u7.gpr]; exact sltu_le _
  have f10' := f10 hc2
  have x3_9 : s9.gpr X3 = s.gpr X3 := by
    rw [u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide), u6.other _ (by decide),
      kp k5 (by decide), kp k4 (by decide), u3.other X3 (by decide), u2.other X3 (by decide),
      kp k1 (by decide)]
  rw [ht0, x3_9, a7_9] at f10'
  -- The registers at the end.
  have o0 : s10.gpr .t6 = s3.gpr .t6 := by
    rw [kp k10 (by decide), u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide),
      u6.other _ (by decide), kp k5 (by decide), kp k4 (by decide)]
  have o1 : s10.gpr .a4 = s5.gpr .a4 := by
    rw [kp k10 (by decide), u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide),
      u6.other _ (by decide)]
  have o2 : s10.gpr .a5 = s6.gpr .a5 := by
    rw [kp k10 (by decide), u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide)]
  refine ⟨?_, ?_, ?_⟩
  · simp only [v4, o0, o1, o2]
    exact sum_arith c0 f5' c2 f10'
  · have := (s10.gpr .a6).isLt; have := (s.gpr X3).isLt; omega
  · refine ⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      obtain ⟨h0, h6, ha0, h4, h5, ha6, h7⟩ := hr
      rw [kp k10 (by simp [ha6, ha0, h7]), u9.other _ h0, u8.other _ h0, u7.other _ h7, u6.other _ h5,
        kp k5 (by simp [h4, ha0, h7]), kp k4 (by simp [h0, ha0]), u3.other _ h7, u2.other _ h6,
        kp k1 (by simp [h0, ha0])]
    · rw [k10.2.1, u9.mem, u8.mem, u7.mem, u6.mem, k5.2.1, k4.2.1, u3.mem, u2.mem, k1.2.1]
    · rw [k10.2.2.1, u9.rd, u8.rd, u7.rd, u6.rd, k5.2.2.1, k4.2.2.1, u3.rd, u2.rd, k1.2.2.1]
    · rw [k10.2.2.2.1, u9.wr, u8.wr, u7.wr, u6.wr, k5.2.2.2.1, k4.2.2.2.1, u3.wr, u2.wr, k1.2.2.2.1]
    · rw [k10.2.2.2.2, u9.sp, u8.sp, u7.sp, u6.sp, k5.2.2.2.2, k4.2.2.2.2, u3.sp, u2.sp, k1.2.2.2.2]

/-! ## `n`'s words under the mask -/

theorem mask_cases {β : BitVec 64} (hb : β.toNat ≤ 1) : β = 0 ∨ β = 1 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with h | h
  · exact .inl (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
  · exact .inr (BitVec.eq_of_toNat_eq (by rw [h]; rfl))

/-- `li64 t6 a0 w` and `t6 ∧ t0`. -/
theorem kW (w : BitVec 64) : KOk (li64 .t6 .a0 w ++ ([.logic .and .t6 .t6 .t0] : List Instr)) w.toNat := fun s β hb ht => by
  refine wp_li64 (by decide) w fun s1 e1 k1 => VG.Proof.X25519.RISCV64.wp_and fun s2 u2 => WP.block_nil
    ⟨?_, ⟨fun r hr => ?_, by rw [u2.rd, k1.2.2.1], by rw [u2.wr, k1.2.2.2.1], by rw [u2.sp, k1.2.2.2.2]⟩,
      by rw [u2.mem, k1.2.1]⟩
  · rw [u2.gpr, e1, kp k1 (by decide), ht]
    rcases mask_cases hb with rfl | rfl
    · simp
    · simp only [show (0 : BitVec 64) - 1 = BitVec.allOnes 64 by decide, BitVec.and_allOnes]; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u2.other _ hr.1, kp k1 (by simp [hr.1, hr.2.1])]

theorem kN3 : KOk [.shift .sll .d .t6 .t0 32] (2 ^ 64 - 2 ^ 32) := fun s β hb ht => by
  refine wp_sll (by decide) fun s1 u1 => WP.block_nil ⟨?_, ⟨fun r hr => u1.other _ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; exact hr.1), u1.rd, u1.wr, u1.sp⟩,
    u1.mem⟩
  rw [u1.gpr, ht]
  rcases mask_cases hb with rfl | rfl <;> decide

/-! ## The operations -/

theorem N_pos : 0 < N := by decide

/-- Montgomery's product modulo `n`. -/
abbrev mulRes (A B r : Nat) : Prop := r < N ∧ r * 2 ^ 256 % N = A * B % N

theorem mulCore_core : CoreOk Impl.Weierstrass.RISCV64.P256Order.mulCore (fun _ B => B < N) mulRes :=
  fun hw h4 h5 h2 ha8 hb8 ho8 ha hb ho hdb hB =>
    WP.mono (mulWith_ok N_pos (by decide) reduce_ok (fun _ => sumN_ok) hw h4 h5 h2 ha8 hb8 ho8 ha hb ho hdb hB)
      fun _ ⟨v1, v2, f, g, rd, wr, sp⟩ => ⟨⟨v1, v2⟩, f, g, rd, wr, sp⟩

theorem addCore_core : CoreOk (.block Impl.Weierstrass.RISCV64.P256Order.addCore) (fun A B => A + B < 2 * N)
    (fun A B r => r = (A + B) % N) :=
  fun hw h4 h5 h2 ha8 hb8 ho8 ha hb ho _ hAB =>
    WP.mono (addWith_ok (sum := sumN) (by decide) (fun _ => sumN_ok) hw h4 h5 h2 ha8 hb8 ho8 ha hb ho hAB)
      fun _ ⟨v, f, g, rd, wr, sp⟩ => ⟨v, f.mono (by simp), g, rd, wr, sp⟩

theorem subCore_core : CoreOk (.block Impl.Weierstrass.RISCV64.P256Order.subCore) (fun A B => A < N ∧ B < N)
    (fun A B r => r = (A + N - B) % N) :=
  fun hw h4 h5 h2 ha8 hb8 ho8 ha hb ho _ hAB =>
    WP.mono (subWith_ok (by decide) (BitVec.isLt _) (BitVec.isLt _) (by decide) (by decide) (kW N0) (kW N1) kP0
      kN3 hw h4 h5 h2 ha8 hb8 ho8 ha hb ho hAB.1 hAB.2) fun _ ⟨v, f, g, rd, wr, sp⟩ =>
      ⟨v, f.mono (by simp), g, rd, wr, sp⟩

end VG.Proof.Weierstrass.RISCV64.P256Order
