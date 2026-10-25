module

public import VerifiedGarbage.Impl.X25519.AArch64.AltOps
public import VerifiedGarbage.Proof.X25519.AArch64.Alt.Mem
public import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.X25519.AArch64.Alt.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! # `mul_4`

The product of the field elements at `a` and `b` into `o`, below `2·p`: the
eight-word product by rows, its high half folded back as 38 and the result
once more at bit 255 (as 19). All of its loads come before its stores, so
`o` may overlap `a` and `b` in any way. -/

@[expose] public section

namespace VG.Proof.X25519.AArch64.Alt
variable {large : Bool}

open VG VG.AArch64 VG.Proof.Ed25519.AArch64 VG.Proof.Ed25519.Word64

/-- One row of `mul_4`: `a · (x7 … x10)` added to `t0`–`t3`, into `t0`–`t4`:
the low halves of the products, then their high halves one word up. -/
abbrev mulRow (a t0 t1 t2 t3 t4 : Reg) : List Instr :=
  [.mul .x .x11 a .x7, .adds .x t0 t0 .x11, .mul .x .x11 a .x8, .adcs .x t1 t1 .x11,
    .mul .x .x11 a .x9, .adcs .x t2 t2 .x11, .mul .x .x11 a .x10, .adcs .x t3 t3 .x11,
    .umulh t4 a .x10, .adc .x t4 t4 .x17,
    .umulh .x11 a .x7, .adds .x t1 t1 .x11, .umulh .x11 a .x8, .adcs .x t2 t2 .x11,
    .umulh .x11 a .x9, .adcs .x t3 t3 .x11, .adc .x t4 t4 .x17]

/-- The carry chains of `mulRow`, on natural numbers: the low halves `L`
of the products `P` added to `T`, then the high halves `H` one word up. -/
theorem rowAlt_arith {T0 T1 T2 T3 L0 L1 L2 L3 H0 H1 H2 H3 P0 P1 P2 P3
    S0 S1 S2 S3 U R1 R2 R3 R4 C0 C1 C2 C3 C4 D1 D2 D3 D4 : Nat}
    (e0 : S0 + 2 ^ 64 * C0 = T0 + L0 + 0) (e1 : S1 + 2 ^ 64 * C1 = T1 + L1 + C0)
    (e2 : S2 + 2 ^ 64 * C2 = T2 + L2 + C1) (e3 : S3 + 2 ^ 64 * C3 = T3 + L3 + C2)
    (e4 : U + 2 ^ 64 * C4 = H3 + 0 + C3)
    (f1 : R1 + 2 ^ 64 * D1 = S1 + H0 + 0) (f2 : R2 + 2 ^ 64 * D2 = S2 + H1 + D1)
    (f3 : R3 + 2 ^ 64 * D3 = S3 + H2 + D2) (f4 : R4 + 2 ^ 64 * D4 = U + 0 + D3)
    (m0 : L0 + 2 ^ 64 * H0 = P0) (m1 : L1 + 2 ^ 64 * H1 = P1)
    (m2 : L2 + 2 ^ 64 * H2 = P2) (m3 : L3 + 2 ^ 64 * H3 = P3)
    (p0 : P0 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1)) (p1 : P1 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1))
    (p2 : P2 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1)) (p3 : P3 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1))
    (t0 : T0 < 2 ^ 64) (t1 : T1 < 2 ^ 64) (t2 : T2 < 2 ^ 64) (t3 : T3 < 2 ^ 64) :
    S0 + 2 ^ 64 * R1 + 2 ^ 128 * R2 + 2 ^ 192 * R3 + 2 ^ 256 * R4 =
      T0 + 2 ^ 64 * T1 + 2 ^ 128 * T2 + 2 ^ 192 * T3 +
        (P0 + 2 ^ 64 * P1 + 2 ^ 128 * P2 + 2 ^ 192 * P3) := by
  omega_arith

/-- What `mulRow` computes, word by word. -/
theorem rowAlt_value (a b0 b1 b2 b3 t0 t1 t2 t3 : Word) :
    let c0 := carryOut t0 (a * b0) false
    let c1 := carryOut t1 (a * b1) c0
    let c2 := carryOut t2 (a * b2) c1
    let c3 := carryOut t3 (a * b3) c2
    let s1 := addCarry t1 (a * b1) c0
    let s2 := addCarry t2 (a * b2) c1
    let s3 := addCarry t3 (a * b3) c2
    let u := addCarry (mulHi a b3) 0 c3
    let d1 := carryOut s1 (mulHi a b0) false
    let d2 := carryOut s2 (mulHi a b1) d1
    let d3 := carryOut s3 (mulHi a b2) d2
    val4 (addCarry t0 (a * b0) false) (addCarry s1 (mulHi a b0) false)
        (addCarry s2 (mulHi a b1) d1) (addCarry s3 (mulHi a b2) d2) +
        2 ^ 256 * (addCarry u 0 d3).toNat =
      val4 t0 t1 t2 t3 + a.toNat * val4 b0 b1 b2 b3 := by
  intro c0 c1 c2 c3 s1 s2 s3 u d1 d2 d3
  simp only [val4]
  rw [mul_val4]
  exact rowAlt_arith (addCarry_value t0 (a * b0) false) (addCarry_value t1 (a * b1) c0)
    (addCarry_value t2 (a * b2) c1) (addCarry_value t3 (a * b3) c2)
    (addCarry_value (mulHi a b3) 0 c3)
    (addCarry_value s1 (mulHi a b0) false) (addCarry_value s2 (mulHi a b1) d1)
    (addCarry_value s3 (mulHi a b2) d2) (addCarry_value u 0 d3)
    (mul_lo_hi a b0) (mul_lo_hi a b1) (mul_lo_hi a b2) (mul_lo_hi a b3)
    (mul_le a b0) (mul_le a b1) (mul_le a b2) (mul_le a b3) t0.isLt t1.isLt t2.isLt t3.isLt

theorem rowB_ok (s : State) (hz : s.gpr .x17 = 0) :
    WP isa (.block (mulRow .x4 .x13 .x14 .x15 .x16 .x3)) s fun t =>
      val4 (t.gpr .x13) (t.gpr .x14) (t.gpr .x15) (t.gpr .x16) + 2 ^ 256 * (t.gpr .x3).toNat =
        val4 (s.gpr .x13) (s.gpr .x14) (s.gpr .x15) (s.gpr .x16) +
          (s.gpr .x4).toNat * val4 (s.gpr .x7) (s.gpr .x8) (s.gpr .x9) (s.gpr .x10) ∧
      Keeps [.x11, .x13, .x14, .x15, .x16, .x3] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_mul_x, exec_umulh_x, exec_adds_x,
    exec_adcs_x, exec_adc_x, Option.some.injEq, exists_eq_left']
  simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, RegUpd.c_write,
    reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq, hz]
  refine ⟨?_, ⟨?_, by simp only [RegUpd.mem_write, RegUpd.mem_addWithCarry],
      by simp only [RegUpd.rd_write, RegUpd.rd_addWithCarry],
      by simp only [RegUpd.wr_write, RegUpd.wr_addWithCarry],
      by simp only [RegUpd.sp_write, RegUpd.sp_addWithCarry]⟩⟩
  · have h := rowAlt_value (s.gpr .x4) (s.gpr .x7) (s.gpr .x8) (s.gpr .x9) (s.gpr .x10)
      (s.gpr .x13) (s.gpr .x14) (s.gpr .x15) (s.gpr .x16)
    dsimp only [addCarry, carryOut, mulHi, Size.bits] at h ⊢
    exact h
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false]

theorem rowC_ok (s : State) (hz : s.gpr .x17 = 0) :
    WP isa (.block (mulRow .x5 .x14 .x15 .x16 .x3 .x4)) s fun t =>
      val4 (t.gpr .x14) (t.gpr .x15) (t.gpr .x16) (t.gpr .x3) + 2 ^ 256 * (t.gpr .x4).toNat =
        val4 (s.gpr .x14) (s.gpr .x15) (s.gpr .x16) (s.gpr .x3) +
          (s.gpr .x5).toNat * val4 (s.gpr .x7) (s.gpr .x8) (s.gpr .x9) (s.gpr .x10) ∧
      Keeps [.x11, .x14, .x15, .x16, .x3, .x4] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_mul_x, exec_umulh_x, exec_adds_x,
    exec_adcs_x, exec_adc_x, Option.some.injEq, exists_eq_left']
  simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, RegUpd.c_write,
    reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq, hz]
  refine ⟨?_, ⟨?_, by simp only [RegUpd.mem_write, RegUpd.mem_addWithCarry],
      by simp only [RegUpd.rd_write, RegUpd.rd_addWithCarry],
      by simp only [RegUpd.wr_write, RegUpd.wr_addWithCarry],
      by simp only [RegUpd.sp_write, RegUpd.sp_addWithCarry]⟩⟩
  · have h := rowAlt_value (s.gpr .x5) (s.gpr .x7) (s.gpr .x8) (s.gpr .x9) (s.gpr .x10)
      (s.gpr .x14) (s.gpr .x15) (s.gpr .x16) (s.gpr .x3)
    dsimp only [addCarry, carryOut, mulHi, Size.bits] at h ⊢
    exact h
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false]

theorem rowD_ok (s : State) (hz : s.gpr .x17 = 0) :
    WP isa (.block (mulRow .x6 .x15 .x16 .x3 .x4 .x5)) s fun t =>
      val4 (t.gpr .x15) (t.gpr .x16) (t.gpr .x3) (t.gpr .x4) + 2 ^ 256 * (t.gpr .x5).toNat =
        val4 (s.gpr .x15) (s.gpr .x16) (s.gpr .x3) (s.gpr .x4) +
          (s.gpr .x6).toNat * val4 (s.gpr .x7) (s.gpr .x8) (s.gpr .x9) (s.gpr .x10) ∧
      Keeps [.x11, .x15, .x16, .x3, .x4, .x5] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_mul_x, exec_umulh_x, exec_adds_x,
    exec_adcs_x, exec_adc_x, Option.some.injEq, exists_eq_left']
  simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, RegUpd.c_write,
    reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq, hz]
  refine ⟨?_, ⟨?_, by simp only [RegUpd.mem_write, RegUpd.mem_addWithCarry],
      by simp only [RegUpd.rd_write, RegUpd.rd_addWithCarry],
      by simp only [RegUpd.wr_write, RegUpd.wr_addWithCarry],
      by simp only [RegUpd.sp_write, RegUpd.sp_addWithCarry]⟩⟩
  · have h := rowAlt_value (s.gpr .x6) (s.gpr .x7) (s.gpr .x8) (s.gpr .x9) (s.gpr .x10)
      (s.gpr .x15) (s.gpr .x16) (s.gpr .x3) (s.gpr .x4)
    dsimp only [addCarry, carryOut, mulHi, Size.bits] at h ⊢
    exact h
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false]

/-- The loads and the first row of `mul_4`: `a₀ · b` into x12–x16, with the
other words of `a` in x4–x6 and `b` in x7–x10. -/
abbrev mulFirst (a b : Nat) : List Instr :=
  [.ldp .x3 .x4 .x0 a, .ldp .x7 .x8 .x0 b,
    .mul .x .x12 .x3 .x7, .umulh .x13 .x3 .x7, .mul .x .x11 .x3 .x8, .umulh .x14 .x3 .x8,
    .adds .x .x13 .x13 .x11, .ldp .x9 .x10 .x0 (b + 16),
    .mul .x .x11 .x3 .x9, .umulh .x15 .x3 .x9, .adcs .x .x14 .x14 .x11,
    .mul .x .x11 .x3 .x10, .umulh .x16 .x3 .x10, .adcs .x .x15 .x15 .x11,
    .adc .x .x16 .x16 .x17, .ldp .x5 .x6 .x0 (a + 16)]

/-- The carry chain of `mulFirst`, on natural numbers. -/
theorem firstAlt_arith {L0 L1 L2 L3 H0 H1 H2 H3 P0 P1 P2 P3 R1 R2 R3 R4 D1 D2 D3 D4 : Nat}
    (f1 : R1 + 2 ^ 64 * D1 = H0 + L1 + 0) (f2 : R2 + 2 ^ 64 * D2 = H1 + L2 + D1)
    (f3 : R3 + 2 ^ 64 * D3 = H2 + L3 + D2) (f4 : R4 + 2 ^ 64 * D4 = H3 + 0 + D3)
    (m0 : L0 + 2 ^ 64 * H0 = P0) (m1 : L1 + 2 ^ 64 * H1 = P1)
    (m2 : L2 + 2 ^ 64 * H2 = P2) (m3 : L3 + 2 ^ 64 * H3 = P3)
    (p0 : P0 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1)) (p1 : P1 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1))
    (p2 : P2 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1)) (p3 : P3 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1)) :
    L0 + 2 ^ 64 * R1 + 2 ^ 128 * R2 + 2 ^ 192 * R3 + 2 ^ 256 * R4 =
      P0 + 2 ^ 64 * P1 + 2 ^ 128 * P2 + 2 ^ 192 * P3 := by
  omega_arith

/-- What the row of `mulFirst` computes, word by word. -/
theorem firstAlt_value (a b0 b1 b2 b3 : Word) :
    let d1 := carryOut (mulHi a b0) (a * b1) false
    let d2 := carryOut (mulHi a b1) (a * b2) d1
    let d3 := carryOut (mulHi a b2) (a * b3) d2
    val4 (a * b0) (addCarry (mulHi a b0) (a * b1) false)
        (addCarry (mulHi a b1) (a * b2) d1) (addCarry (mulHi a b2) (a * b3) d2) +
        2 ^ 256 * (addCarry (mulHi a b3) 0 d3).toNat =
      a.toNat * val4 b0 b1 b2 b3 := by
  intro d1 d2 d3
  simp only [val4]
  rw [mul_val4]
  exact firstAlt_arith (addCarry_value (mulHi a b0) (a * b1) false)
    (addCarry_value (mulHi a b1) (a * b2) d1) (addCarry_value (mulHi a b2) (a * b3) d2)
    (addCarry_value (mulHi a b3) 0 d3)
    (mul_lo_hi a b0) (mul_lo_hi a b1) (mul_lo_hi a b2) (mul_lo_hi a b3)
    (mul_le a b0) (mul_le a b1) (mul_le a b2) (mul_le a b3)

theorem mulFirst_ok {s : State} {base : Addr} (hs : Scr s base large) {a b : Nat}
    (ha : AltRange a large) (hb : AltRange b large) (hz : s.gpr .x17 = 0) :
    WP isa (.block (mulFirst a b)) s fun t =>
      t.gpr .x4 = word s.mem base (a + 8) ∧ t.gpr .x5 = word s.mem base (a + 16) ∧
      t.gpr .x6 = word s.mem base (a + 24) ∧
      val4 (t.gpr .x7) (t.gpr .x8) (t.gpr .x9) (t.gpr .x10) = fe s.mem base b ∧
      val4 (t.gpr .x12) (t.gpr .x13) (t.gpr .x14) (t.gpr .x15) + 2 ^ 256 * (t.gpr .x16).toNat =
        (word s.mem base a).toNat * fe s.mem base b ∧
      Keeps [.x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16] s t := by
  have _hcap := workSize_le large
  obtain ⟨aa, ab, ac⟩ := ha
  obtain ⟨ba, bb, bc⟩ := hb
  have a16 : (a + 16) % 8 = 0 := by omega_arith
  have b16 : (b + 16) % 8 = 0 := by omega_arith
  have w3 : Reg.x3 ≠ .x0 := by decide
  have w4 : Reg.x4 ≠ .x0 := by decide
  have w7 : Reg.x7 ≠ .x0 := by decide
  have w8 : Reg.x8 ≠ .x0 := by decide
  have w9 : Reg.x9 ≠ .x0 := by decide
  have w10 : Reg.x10 ≠ .x0 := by decide
  have w11 : Reg.x11 ≠ .x0 := by decide
  have w12 : Reg.x12 ≠ .x0 := by decide
  have w13 : Reg.x13 ≠ .x0 := by decide
  have w14 : Reg.x14 ≠ .x0 := by decide
  have w15 : Reg.x15 ≠ .x0 := by decide
  have w16 : Reg.x16 ≠ .x0 := by decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    ldp_sc hs aa (by omega_arith) (by omega_arith) (by decide : Reg.x3 ≠ .x4),
    ldp_sc ((hs.write w3 _).write w4 _) ba (by omega_arith) (by omega_arith) (by decide : Reg.x7 ≠ .x8),
    ldp_sc ((((((((((hs).write w3 _).write w4 _).write w7 _).write w8 _).write w12 _)
      |>.write w13 _).write w11 _).write w14 _)
      |>.awc w13 _ _ _) b16 (by omega_arith) (by omega_arith) (by decide : Reg.x9 ≠ .x10),
    ldp_sc (((((((((((((((((((hs).write w3 _).write w4 _).write w7 _).write w8 _).write w12 _)
      |>.write w13 _).write w11 _).write w14 _).awc w13 _ _ _).write w9 _).write w10 _)
      |>.write w11 _).write w15 _).awc w14 _ _ _).write w11 _).write w16 _).awc w15 _ _ _)
      |>.write w16 _) a16 (by omega_arith) (by omega_arith) (by decide : Reg.x5 ≠ .x6),
    exec_mul_x, exec_umulh_x, exec_adds_x, exec_adcs_x, exec_adc_x,
    Option.some.injEq, exists_eq_left']
  simp only [RegUpd.mem_write, RegUpd.mem_addWithCarry, RegUpd.gpr_write, RegUpd.gpr_addWithCarry,
    RegUpd.c_addWithCarry, RegUpd.c_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq,
    hz]
  rw [show a + 16 + 8 = a + 24 by omega_arith, show b + 16 + 8 = b + 24 by omega_arith]
  refine ⟨trivial, trivial, trivial, trivial, ?_, ⟨?_, by simp only [RegUpd.mem_write,
      RegUpd.mem_addWithCarry],
      by simp only [RegUpd.rd_write, RegUpd.rd_addWithCarry],
      by simp only [RegUpd.wr_write, RegUpd.wr_addWithCarry],
      by simp only [RegUpd.sp_write, RegUpd.sp_addWithCarry]⟩⟩
  · have h := firstAlt_value (word s.mem base a) (word s.mem base b) (word s.mem base (b + 8))
      (word s.mem base (b + 16)) (word s.mem base (b + 24))
    dsimp only [fe, addCarry, carryOut, mulHi, Size.bits] at h ⊢
    exact h
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.2.2.2.2, ite_false]

/-- The high half x16, x3–x5 of the product folded back into x12–x15 as 38,
less the high words of `38 · x16` and `38 · x3`, left in x9 and x3. -/
abbrev mulFold38 : List Instr :=
  [.movz .w .x7 38 0, .mul .x .x11 .x7 .x16, .umulh .x9 .x7 .x16, .adds .x .x12 .x12 .x11,
    .mul .x .x11 .x7 .x3, .umulh .x3 .x7 .x3, .adcs .x .x13 .x13 .x11,
    .mul .x .x11 .x7 .x4, .umulh .x4 .x7 .x4, .adcs .x .x14 .x14 .x11,
    .mul .x .x11 .x7 .x5, .umulh .x5 .x7 .x5, .adcs .x .x15 .x15 .x11,
    .adc .x .x16 .x17 .x17, .adds .x .x15 .x15 .x4, .adc .x .x16 .x16 .x5]

/-- What `mulFold38` computes, word by word, for `k = 38`. -/
theorem fold38_value (k t0 t1 t2 t3 h0 h1 h2 h3 : Word) (hk : k.toNat = 38) :
    let c0 := carryOut t0 (k * h0) false
    let c1 := carryOut t1 (k * h1) c0
    let c2 := carryOut t2 (k * h2) c1
    let c3 := carryOut t3 (k * h3) c2
    let s3 := addCarry t3 (k * h3) c2
    let u := addCarry 0 0 c3
    let d := carryOut s3 (mulHi k h2) false
    val4 (addCarry t0 (k * h0) false) (addCarry t1 (k * h1) c0) (addCarry t2 (k * h2) c1)
          (addCarry s3 (mulHi k h2) false) + 2 ^ 256 * (addCarry u (mulHi k h3) d).toNat +
        2 ^ 64 * (mulHi k h0).toNat + 2 ^ 128 * (mulHi k h1).toNat =
      val4 t0 t1 t2 t3 + 38 * val4 h0 h1 h2 h3 ∧
    (mulHi k h0).toNat < 38 ∧ (mulHi k h1).toNat < 38 ∧ (addCarry u (mulHi k h3) d).toNat < 40 := by
  intro c0 c1 c2 c3 s3 u d
  have e0 := addCarry_value t0 (k * h0) false
  have e1 := addCarry_value t1 (k * h1) c0
  have e2 := addCarry_value t2 (k * h2) c1
  have e3 := addCarry_value t3 (k * h3) c2
  have e4 := addCarry_value 0 0 c3
  have f3 := addCarry_value s3 (mulHi k h2) false
  have f4 := addCarry_value u (mulHi k h3) d
  have m0 := mul_lo_hi k h0
  have m1 := mul_lo_hi k h1
  have m2 := mul_lo_hi k h2
  have m3 := mul_lo_hi k h3
  rw [hk] at m0 m1 m2 m3
  have := h0.isLt; have := h1.isLt; have := h2.isLt; have := h3.isLt
  have := t0.isLt; have := t1.isLt; have := t2.isLt; have := t3.isLt
  have z : (0 : Word).toNat = 0 := rfl
  have := Bool.toNat_le c0; have := Bool.toNat_le c1; have := Bool.toNat_le c2
  have := Bool.toNat_le c3; have := Bool.toNat_le d
  dsimp only [c0, c1, c2, c3, s3, u, d] at *
  simp only [val4, Bool.toNat_false, z] at *
  refine ⟨?_, ?_, ?_, ?_⟩
  · omega_arith
  · omega_arith
  · omega_arith
  · omega_arith

theorem mulFold38_ok (s : State) (hz : s.gpr .x17 = 0) :
    WP isa (.block mulFold38) s fun t =>
      val4 (t.gpr .x12) (t.gpr .x13) (t.gpr .x14) (t.gpr .x15) + 2 ^ 256 * (t.gpr .x16).toNat +
          2 ^ 64 * (t.gpr .x9).toNat + 2 ^ 128 * (t.gpr .x3).toNat =
        val4 (s.gpr .x12) (s.gpr .x13) (s.gpr .x14) (s.gpr .x15) +
          38 * val4 (s.gpr .x16) (s.gpr .x3) (s.gpr .x4) (s.gpr .x5) ∧
      (t.gpr .x9).toNat < 38 ∧ (t.gpr .x3).toNat < 38 ∧ (t.gpr .x16).toNat < 40 ∧
      Keeps [.x3, .x4, .x5, .x7, .x9, .x11, .x12, .x13, .x14, .x15, .x16] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_movz_w, exec_mul_x, exec_umulh_x,
    exec_adds_x, exec_adcs_x, exec_adc_x, Option.some.injEq, exists_eq_left']
  simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, RegUpd.c_write,
    reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq, hz]
  have h := fold38_value (BitVec.setWidth 64 (BitVec.setWidth 32 (38 : BitVec 16)))
    (s.gpr .x12) (s.gpr .x13) (s.gpr .x14) (s.gpr .x15)
    (s.gpr .x16) (s.gpr .x3) (s.gpr .x4) (s.gpr .x5) rfl
  dsimp only [addCarry, carryOut, mulHi, Size.bits] at h ⊢
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, h3, h4, ⟨?_, by simp only [RegUpd.mem_write, RegUpd.mem_addWithCarry],
      by simp only [RegUpd.rd_write, RegUpd.rd_addWithCarry],
      by simp only [RegUpd.wr_write, RegUpd.wr_addWithCarry],
      by simp only [RegUpd.sp_write, RegUpd.sp_addWithCarry]⟩⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
    hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.1,
    hr.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.2, ite_false]

/-- The five words x12–x15, x16 and the words x9 and x3 one and two words
up, folded at bit 255. -/
abbrev mulFold19 : List Instr :=
  [.adds .x .x11 .x15 .x15, .lsr .x .x15 .x11 1, .adc .x .x8 .x16 .x16, .movz .w .x7 19 0,
    .mul .x .x11 .x7 .x8, .adds .x .x12 .x12 .x11, .adcs .x .x13 .x13 .x9,
    .adcs .x .x14 .x14 .x3, .adc .x .x15 .x15 .x17]

theorem fold_hi19 (x15 x16 : Word) (h : x16.toNat < 2 ^ 58) :
    (BitVec.setWidth 64 (BitVec.setWidth 32 (19 : BitVec 16)) *
      (x16 + x16 + BitVec.ofNat 64 (decide (2 ^ 64 ≤ x15.toNat + x15.toNat + false.toNat)).toNat)).toNat =
      19 * (2 * x16.toNat + x15.toNat / 2 ^ 63) := by
  have := x15.isLt
  have e : BitVec.setWidth 64 (BitVec.setWidth 32 (19 : BitVec 16)) = 19 := rfl
  rw [e, fold_c]
  simp only [BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ofNat]
  have : x15.toNat / 2 ^ 63 ≤ 1 := by omega_arith
  have e19 : (19 : BitVec 64).toNat = 19 := rfl
  rw [e19]
  omega_arith

theorem mulFold19_ok (s : State) (hz : s.gpr .x17 = 0) (h16 : (s.gpr .x16).toNat < 40)
    (h9 : (s.gpr .x9).toNat < 38) (h3 : (s.gpr .x3).toNat < 38) :
    WP isa (.block mulFold19) s fun t => ∃ q,
      val4 (t.gpr .x12) (t.gpr .x13) (t.gpr .x14) (t.gpr .x15) + (2 ^ 255 - 19) * q =
        val4 (s.gpr .x12) (s.gpr .x13) (s.gpr .x14) (s.gpr .x15) + 2 ^ 256 * (s.gpr .x16).toNat +
          2 ^ 64 * (s.gpr .x9).toNat + 2 ^ 128 * (s.gpr .x3).toNat ∧
      val4 (t.gpr .x12) (t.gpr .x13) (t.gpr .x14) (t.gpr .x15) < 2 ^ 256 - 38 ∧
      Keeps [.x7, .x8, .x11, .x12, .x13, .x14, .x15] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_adds_x, exec_lsr1_x, exec_adc_x,
    exec_movz_w, exec_mul_x, exec_adcs_x, Option.some.injEq, exists_eq_left']
  simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, RegUpd.c_write,
    reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq, hz]
  dsimp only [Size.bits]
  have h := add4_value (s.gpr .x12) (s.gpr .x13) (s.gpr .x14)
    ((s.gpr .x15 + s.gpr .x15 + BitVec.ofNat 64 false.toNat) >>> 1)
    (BitVec.setWidth 64 (BitVec.setWidth 32 (19 : BitVec 16)) * (s.gpr .x16 + s.gpr .x16 +
      BitVec.ofNat 64 (decide (2 ^ 64 ≤ (s.gpr .x15).toNat + (s.gpr .x15).toNat + false.toNat)).toNat))
    (s.gpr .x9) (s.gpr .x3) 0 false
  dsimp only [addCarry, carryOut] at h
  have hU := fold_lo (s.gpr .x15)
  have hM := fold_hi19 (s.gpr .x15) (s.gpr .x16) (by omega_arith)
  have z : (0 : BitVec 64).toNat = 0 := rfl
  have := (s.gpr .x12).isLt
  have := (s.gpr .x13).isLt
  have := (s.gpr .x14).isLt
  have := (s.gpr .x15).isLt
  simp only [val4, z, Bool.toNat_false, Nat.add_zero, Nat.mul_zero] at h hU hM ⊢
  refine ⟨2 * (s.gpr .x16).toNat + (s.gpr .x15).toNat / 2 ^ 63, ?_, ?_,
    ⟨?_, by simp only [RegUpd.mem_write, RegUpd.mem_addWithCarry],
      by simp only [RegUpd.rd_write, RegUpd.rd_addWithCarry],
      by simp only [RegUpd.wr_write, RegUpd.wr_addWithCarry],
      by simp only [RegUpd.sp_write, RegUpd.sp_addWithCarry]⟩⟩
  · omega_arith
  · omega_arith
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2, ite_false]

theorem mul4_eq (o a b : Nat) :
    Impl.X25519.AArch64.Alt.mul4 o a b =
      mulFirst a b ++ (mulRow .x4 .x13 .x14 .x15 .x16 .x3 ++ (mulRow .x5 .x14 .x15 .x16 .x3 .x4 ++
        (mulRow .x6 .x15 .x16 .x3 .x4 .x5 ++ (mulFold38 ++ (mulFold19 ++
          ([.stp .x12 .x13 .x0 o, .stp .x14 .x15 .x0 (o + 16)] : List Instr)))))) := rfl

/-- `[o] := [a] · [b]`, modulo `p` and below `2·p`. -/
theorem mul4_ok {s : State} {base : Addr} (hs : Scr s base large) {o a b : Nat}
    (ho : AltRange o large) (ha : AltRange a large) (hb : AltRange b large)
    (hz : s.gpr .x17 = 0) :
    WP isa (.block (Impl.X25519.AArch64.Alt.mul4 o a b)) s fun t =>
      AltOp base o s t ∧ fe t.mem base o < 2 ^ 256 - 38 ∧ ∃ q, fe t.mem base o + (2 ^ 255 - 19) * q =
        fe s.mem base a * fe s.mem base b := by
  have _hcap := workSize_le large
  rw [mul4_eq, WP.block_append_iff]
  refine WP.mono (mulFirst_ok hs ha hb hz) fun s₁ ⟨x4, x5, x6, eb, e1, k1⟩ => ?_
  have hs₁ := hs.of_keeps k1 (by decide)
  have z1 : s₁.gpr .x17 = 0 := (k1.gpr _ (by decide)).trans hz
  rw [WP.block_append_iff]
  refine WP.mono (rowB_ok s₁ z1) fun s₂ ⟨e2, k2⟩ => ?_
  have z2 : s₂.gpr .x17 = 0 := (k2.gpr _ (by decide)).trans z1
  rw [WP.block_append_iff]
  refine WP.mono (rowC_ok s₂ z2) fun s₃ ⟨e3, k3⟩ => ?_
  have z3 : s₃.gpr .x17 = 0 := (k3.gpr _ (by decide)).trans z2
  rw [WP.block_append_iff]
  refine WP.mono (rowD_ok s₃ z3) fun s₄ ⟨e4, k4⟩ => ?_
  have z4 : s₄.gpr .x17 = 0 := (k4.gpr _ (by decide)).trans z3
  rw [WP.block_append_iff]
  refine WP.mono (mulFold38_ok s₄ z4) fun s₅ ⟨e5, b9, b3, b16, k5⟩ => ?_
  have z5 : s₅.gpr .x17 = 0 := (k5.gpr _ (by decide)).trans z4
  rw [WP.block_append_iff]
  refine WP.mono (mulFold19_ok s₅ z5 b16 b9 b3) fun s₆ ⟨q, e6, l6, k6⟩ => ?_
  have hs₆ := (((((hs₁.of_keeps k2 (by decide)).of_keeps k3 (by decide)).of_keeps k4
    (by decide)).of_keeps k5 (by decide)).of_keeps k6 (by decide))
  refine WP.mono (store4_ok hs₆ ho.1 ho.2.1 ho.2.2 .x12 .x13 .x14 .x15) fun t ht => ?_
  subst t
  have m6 : s₆.mem = s.mem := by rw [k6.mem, k5.mem, k4.mem, k3.mem, k2.mem, k1.mem]
  have _ho := ho.2.2
  have hf := fe_st4 s₆.mem base (o := o) (by omega_arith) (s₆.gpr .x12) (s₆.gpr .x13) (s₆.gpr .x14)
    (s₆.gpr .x15)
  -- the registers each step reads, through the steps that keep them
  rw [k2.gpr .x5 (by decide), k2.gpr .x7 (by decide), k2.gpr .x8 (by decide),
    k2.gpr .x9 (by decide), k2.gpr .x10 (by decide), x5, eb] at e3
  rw [k3.gpr .x6 (by decide), k3.gpr .x7 (by decide), k3.gpr .x8 (by decide),
    k3.gpr .x9 (by decide), k3.gpr .x10 (by decide), k2.gpr .x6 (by decide),
    k2.gpr .x7 (by decide), k2.gpr .x8 (by decide), k2.gpr .x9 (by decide),
    k2.gpr .x10 (by decide), x6, eb] at e4
  rw [x4, eb] at e2
  have r12 : (s₄.gpr .x12).toNat = (s₁.gpr .x12).toNat := by
    rw [k4.gpr _ (by decide), k3.gpr _ (by decide), k2.gpr _ (by decide)]
  have r13 : (s₄.gpr .x13).toNat = (s₂.gpr .x13).toNat := by
    rw [k4.gpr _ (by decide), k3.gpr _ (by decide)]
  have r14 : (s₄.gpr .x14).toNat = (s₃.gpr .x14).toNat := by rw [k4.gpr _ (by decide)]
  have hab : fe s.mem base a * fe s.mem base b =
      (word s.mem base a).toNat * fe s.mem base b +
        2 ^ 64 * ((word s.mem base (a + 8)).toNat * fe s.mem base b) +
        2 ^ 128 * ((word s.mem base (a + 16)).toNat * fe s.mem base b) +
        2 ^ 192 * ((word s.mem base (a + 24)).toNat * fe s.mem base b) := by
    simp only [fe, val4, Nat.add_mul, Nat.mul_assoc]
  refine ⟨⟨fun r hr => ?_, by rw [rd_withMem, k6.rd, k5.rd, k4.rd, k3.rd, k2.rd, k1.rd],
    by rw [wr_withMem, k6.wr, k5.wr, k4.wr, k3.wr, k2.wr, k1.wr],
    by rw [sp_withMem, k6.sp, k5.sp, k4.sp, k3.sp, k2.sp, k1.sp], ?_⟩,
    by rw [mem_withMem, hf]; exact l6, q + 2 * val4 (s₄.gpr .x16) (s₄.gpr .x3) (s₄.gpr .x4)
      (s₄.gpr .x5), ?_⟩
  · simp only [altClob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [gpr_withMem, k6.gpr _ (by simp only [List.mem_cons, List.not_mem_nil, or_false, hr,
      not_false_eq_true]), k5.gpr _ (by simp only [List.mem_cons, List.not_mem_nil, or_false, hr,
      not_false_eq_true]), k4.gpr _ (by simp only [List.mem_cons, List.not_mem_nil, or_false, hr,
      not_false_eq_true]), k3.gpr _ (by simp only [List.mem_cons, List.not_mem_nil, or_false, hr,
      not_false_eq_true]), k2.gpr _ (by simp only [List.mem_cons, List.not_mem_nil, or_false, hr,
      not_false_eq_true]), k1.gpr _ (by simp only [List.mem_cons, List.not_mem_nil, or_false, hr,
      not_false_eq_true])]
  · rw [mem_withMem, ← m6]
    exact st4_outside _ _ (by omega_arith) _ _ _ _
  · rw [mem_withMem, hf, hab]
    simp only [val4] at e1 e2 e3 e4 e5 e6 ⊢
    omega_arith

end VG.Proof.X25519.AArch64.Alt
