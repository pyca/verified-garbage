module

public import VerifiedGarbage.Impl.X25519.AArch64.AltOps
public import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
public import VerifiedGarbage.Proof.X25519.AArch64.Alt.Mem
import VerifiedGarbage.Proof.X25519.AArch64.Alt.Mul
import VerifiedGarbage.Proof.X25519.AArch64.Alt.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! # `sqr_4`

The square of the field element at `a` into `o`, below `2·p`: the products
`aᵢ aⱼ` (`i < j`), doubled, plus the squares `aᵢ²`, folded as in `mul_4`. All
of its loads come before its stores, so `o` may be `a`. -/

@[expose] public section

namespace VG.Proof.X25519.AArch64.Alt
variable {large : Bool}

open VG VG.AArch64 VG.Proof.Ed25519.AArch64 VG.Proof.Ed25519.Word64

/-- The loads and the products `aᵢ aⱼ` (`i < j`), at their word `i + j` of
x9–x14 less one. -/
abbrev sqrCross (a : Nat) : List Instr :=
  [.ldp .x2 .x3 .x0 a, .mul .x .x9 .x2 .x3, .umulh .x10 .x2 .x3, .ldp .x4 .x5 .x0 (a + 16),
    .mul .x .x11 .x2 .x5, .umulh .x12 .x2 .x5, .mul .x .x7 .x2 .x4, .umulh .x6 .x2 .x4,
    .adds .x .x10 .x10 .x7, .adcs .x .x11 .x11 .x6, .mul .x .x7 .x3 .x4, .umulh .x6 .x3 .x4,
    .adc .x .x6 .x6 .x17, .adds .x .x11 .x11 .x7, .mul .x .x13 .x4 .x5, .umulh .x14 .x4 .x5,
    .adcs .x .x12 .x12 .x6, .mul .x .x7 .x3 .x5, .umulh .x6 .x3 .x5, .adc .x .x6 .x6 .x17,
    .adds .x .x12 .x12 .x7, .adcs .x .x13 .x13 .x6, .adc .x .x14 .x14 .x17]

theorem hi_le {L H P : Nat} (m : L + 2 ^ 64 * H = P) (p : P ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1)) :
    H ≤ 2 ^ 64 - 2 := by
  omega

theorem carry_le {R C a b c : Nat} (f : R + 2 ^ 64 * C = a + b + c) (ha : a < 2 ^ 64)
    (hb : b < 2 ^ 64) (hc : c ≤ 1) : C ≤ 1 := by
  omega

theorem no_carry {R D H c : Nat} (f : R + 2 ^ 64 * D = H + 0 + c) (h : H ≤ 2 ^ 64 - 2)
    (hc : c ≤ 1) (hr : R < 2 ^ 64) : D = 0 := by
  omega

/-- The carry chains of `sqrCross`, on natural numbers: `L` and `H` the low
and high halves of the products `P`. -/
theorem cross_arith {L01 H01 L02 H02 L03 H03 L12 H12 L13 H13 L23 H23
    P01 P02 P03 P12 P13 P23 R1 R2 R3 R4 R5 Q Y X6a X6b C1 C2 C3 C4 C5 C6 D3 D6 D9 : Nat}
    (f1 : R1 + 2 ^ 64 * C1 = H01 + L02 + 0) (f2 : Q + 2 ^ 64 * C2 = L03 + H02 + C1)
    (f3 : X6a + 2 ^ 64 * D3 = H12 + 0 + C2) (f4 : R2 + 2 ^ 64 * C3 = Q + L12 + 0)
    (f5 : Y + 2 ^ 64 * C4 = H03 + X6a + C3) (f6 : X6b + 2 ^ 64 * D6 = H13 + 0 + C4)
    (f7 : R3 + 2 ^ 64 * C5 = Y + L13 + 0) (f8 : R4 + 2 ^ 64 * C6 = L23 + X6b + C5)
    (f9 : R5 + 2 ^ 64 * D9 = H23 + 0 + C6)
    (m01 : L01 + 2 ^ 64 * H01 = P01) (m02 : L02 + 2 ^ 64 * H02 = P02)
    (m03 : L03 + 2 ^ 64 * H03 = P03) (m12 : L12 + 2 ^ 64 * H12 = P12)
    (m13 : L13 + 2 ^ 64 * H13 = P13) (m23 : L23 + 2 ^ 64 * H23 = P23)
    (p02 : P02 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1)) (p03 : P03 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1))
    (p12 : P12 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1)) (p13 : P13 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1))
    (p23 : P23 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1))
    (l03 : L03 < 2 ^ 64) (l23 : L23 < 2 ^ 64) (c1 : C1 ≤ 1) (c3 : C3 ≤ 1) (c5 : C5 ≤ 1)
    (x6a : X6a < 2 ^ 64) (x6b : X6b < 2 ^ 64) (r5 : R5 < 2 ^ 64) :
    L01 + 2 ^ 64 * R1 + 2 ^ 128 * R2 + 2 ^ 192 * R3 + 2 ^ 256 * (R4 + 2 ^ 64 * R5) =
      P01 + 2 ^ 64 * P02 + 2 ^ 128 * (P03 + P12) + 2 ^ 192 * P13 + 2 ^ 256 * P23 := by
  have h02 := hi_le m02 p02
  have h03 := hi_le m03 p03
  have c2 := carry_le f2 l03 (by omega) c1
  have d3 := no_carry f3 (hi_le m12 p12) c2 x6a
  have c4 := carry_le f5 (by omega) x6a c3
  have d6 := no_carry f6 (hi_le m13 p13) c4 x6b
  have c6 := carry_le f8 l23 x6b c5
  have d9 := no_carry f9 (hi_le m23 p23) c6 r5
  subst d3 d6 d9
  clear h02 h03 c1 c2 c3 c4 c5 c6 p02 p03 p12 p13 p23 l03 l23 x6a x6b r5
  omega

/-- What `sqrCross` computes, word by word. -/
theorem cross_value (a0 a1 a2 a3 : Word) :
    let c1 := carryOut (mulHi a0 a1) (a0 * a2) false
    let x11a := addCarry (a0 * a3) (mulHi a0 a2) c1
    let c2 := carryOut (a0 * a3) (mulHi a0 a2) c1
    let x6a := addCarry (mulHi a1 a2) 0 c2
    let c3 := carryOut x11a (a1 * a2) false
    let x12a := addCarry (mulHi a0 a3) x6a c3
    let c4 := carryOut (mulHi a0 a3) x6a c3
    let x6b := addCarry (mulHi a1 a3) 0 c4
    let c5 := carryOut x12a (a1 * a3) false
    let c6 := carryOut (a2 * a3) x6b c5
    (a0 * a1).toNat + 2 ^ 64 * (addCarry (mulHi a0 a1) (a0 * a2) false).toNat +
        2 ^ 128 * (addCarry x11a (a1 * a2) false).toNat +
        2 ^ 192 * (addCarry x12a (a1 * a3) false).toNat +
        2 ^ 256 * ((addCarry (a2 * a3) x6b c5).toNat +
          2 ^ 64 * (addCarry (mulHi a2 a3) 0 c6).toNat) =
      a0.toNat * a1.toNat + 2 ^ 64 * (a0.toNat * a2.toNat) +
        2 ^ 128 * (a0.toNat * a3.toNat + a1.toNat * a2.toNat) + 2 ^ 192 * (a1.toNat * a3.toNat) +
        2 ^ 256 * (a2.toNat * a3.toNat) := by
  intro c1 x11a c2 x6a c3 x12a c4 x6b c5 c6
  exact cross_arith (addCarry_value (mulHi a0 a1) (a0 * a2) false)
    (addCarry_value (a0 * a3) (mulHi a0 a2) c1) (addCarry_value (mulHi a1 a2) 0 c2)
    (addCarry_value x11a (a1 * a2) false) (addCarry_value (mulHi a0 a3) x6a c3)
    (addCarry_value (mulHi a1 a3) 0 c4) (addCarry_value x12a (a1 * a3) false)
    (addCarry_value (a2 * a3) x6b c5) (addCarry_value (mulHi a2 a3) 0 c6)
    (mul_lo_hi a0 a1) (mul_lo_hi a0 a2) (mul_lo_hi a0 a3) (mul_lo_hi a1 a2) (mul_lo_hi a1 a3)
    (mul_lo_hi a2 a3) (mul_le a0 a2) (mul_le a0 a3)
    (mul_le a1 a2) (mul_le a1 a3) (mul_le a2 a3) (BitVec.isLt _) (BitVec.isLt _)
    (Bool.toNat_le _) (Bool.toNat_le _) (Bool.toNat_le _) x6a.isLt x6b.isLt (BitVec.isLt _)

theorem sqrCross_ok {s : State} {base : Addr} (hs : Scr s base large) {a : Nat}
    (ha : AltRange a large) (hz : s.gpr .x17 = 0) :
    WP isa (.block (sqrCross a)) s fun t =>
      t.gpr .x2 = word s.mem base a ∧ t.gpr .x3 = word s.mem base (a + 8) ∧
      t.gpr .x4 = word s.mem base (a + 16) ∧ t.gpr .x5 = word s.mem base (a + 24) ∧
      (t.gpr .x9).toNat + 2 ^ 64 * (t.gpr .x10).toNat + 2 ^ 128 * (t.gpr .x11).toNat +
          2 ^ 192 * (t.gpr .x12).toNat +
          2 ^ 256 * ((t.gpr .x13).toNat + 2 ^ 64 * (t.gpr .x14).toNat) =
        (word s.mem base a).toNat * (word s.mem base (a + 8)).toNat +
          2 ^ 64 * ((word s.mem base a).toNat * (word s.mem base (a + 16)).toNat) +
          2 ^ 128 * ((word s.mem base a).toNat * (word s.mem base (a + 24)).toNat +
            (word s.mem base (a + 8)).toNat * (word s.mem base (a + 16)).toNat) +
          2 ^ 192 * ((word s.mem base (a + 8)).toNat * (word s.mem base (a + 24)).toNat) +
          2 ^ 256 * ((word s.mem base (a + 16)).toNat * (word s.mem base (a + 24)).toNat) ∧
      Keeps [.x2, .x3, .x4, .x5, .x6, .x7, .x9, .x10, .x11, .x12, .x13, .x14] s t := by
  have _hcap := workSize_le large
  obtain ⟨aa, ab, ac⟩ := ha
  have a16 : (a + 16) % 8 = 0 := by omega
  have w2 : Reg.x2 ≠ .x0 := by decide
  have w3 : Reg.x3 ≠ .x0 := by decide
  have w9 : Reg.x9 ≠ .x0 := by decide
  have w10 : Reg.x10 ≠ .x0 := by decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    ldp_sc hs aa (by omega) (by omega) (by decide : Reg.x2 ≠ .x3),
    ldp_sc ((((hs.write w2 _).write w3 _).write w9 _).write w10 _) a16 (by omega) (by omega)
      (by decide : Reg.x4 ≠ .x5),
    exec_mul_x, exec_umulh_x, exec_adds_x, exec_adcs_x, exec_adc_x,
    Option.some.injEq, exists_eq_left']
  simp only [RegUpd.mem_write, RegUpd.gpr_write, RegUpd.gpr_addWithCarry,
    RegUpd.c_addWithCarry, RegUpd.c_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq,
    hz]
  rw [show a + 16 + 8 = a + 24 by omega]
  refine ⟨trivial, trivial, trivial, trivial, ?_, ⟨?_, by simp only [RegUpd.mem_write,
      RegUpd.mem_addWithCarry], by simp only [RegUpd.rd_write, RegUpd.rd_addWithCarry],
      by simp only [RegUpd.wr_write, RegUpd.wr_addWithCarry],
      by simp only [RegUpd.sp_write, RegUpd.sp_addWithCarry]⟩⟩
  · have h := cross_value (word s.mem base a) (word s.mem base (a + 8))
      (word s.mem base (a + 16)) (word s.mem base (a + 24))
    dsimp only [addCarry, carryOut, mulHi, Size.bits] at h ⊢
    exact h
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.2.2, ite_false]

/-- The products of `sqrCross` doubled, plus the squares `aᵢ²`: the
eight-word square in x8–x14, x6. -/
abbrev sqrDiag : List Instr :=
  [.adds .x .x9 .x9 .x9, .adcs .x .x10 .x10 .x10, .adcs .x .x11 .x11 .x11,
    .adcs .x .x12 .x12 .x12, .adcs .x .x13 .x13 .x13, .adcs .x .x14 .x14 .x14,
    .adc .x .x6 .x17 .x17,
    .umulh .x7 .x2 .x2, .mul .x .x8 .x2 .x2, .adds .x .x9 .x9 .x7, .mul .x .x7 .x3 .x3,
    .adcs .x .x10 .x10 .x7, .umulh .x7 .x3 .x3, .adcs .x .x11 .x11 .x7, .mul .x .x7 .x4 .x4,
    .adcs .x .x12 .x12 .x7, .umulh .x7 .x4 .x4, .adcs .x .x13 .x13 .x7, .mul .x .x7 .x5 .x5,
    .adcs .x .x14 .x14 .x7, .umulh .x7 .x5 .x5, .adc .x .x6 .x6 .x7]

/-- The doubling of `sqrDiag`, on natural numbers. -/
theorem dbl_arith {D9 D10 D11 D12 D13 D14 G9 G10 G11 G12 G13 G14 G6 K1 K2 K3 K4 K5 K6 K7 : Nat}
    (f1 : G9 + 2 ^ 64 * K1 = D9 + D9 + 0) (f2 : G10 + 2 ^ 64 * K2 = D10 + D10 + K1)
    (f3 : G11 + 2 ^ 64 * K3 = D11 + D11 + K2) (f4 : G12 + 2 ^ 64 * K4 = D12 + D12 + K3)
    (f5 : G13 + 2 ^ 64 * K5 = D13 + D13 + K4) (f6 : G14 + 2 ^ 64 * K6 = D14 + D14 + K5)
    (f7 : G6 + 2 ^ 64 * K7 = 0 + 0 + K6) (k6 : K6 ≤ 1) :
    G9 + 2 ^ 64 * G10 + 2 ^ 128 * G11 + 2 ^ 192 * G12 + 2 ^ 256 * (G13 + 2 ^ 64 * G14 + 2 ^ 128 * G6) =
      2 * (D9 + 2 ^ 64 * D10 + 2 ^ 128 * D11 + 2 ^ 192 * D12 + 2 ^ 256 * (D13 + 2 ^ 64 * D14)) := by
  have k7 : K7 = 0 := by omega
  subst k7
  clear k6
  omega

/-- The squares of `sqrDiag`, on natural numbers. -/
theorem sq_arith {G9 G10 G11 G12 G13 G14 G6 L0 H0 L1 H1 L2 H2 L3 H3 P0 P1 P2 P3
    Y9 Y10 Y11 Y12 Y13 Y14 Y6 E1 E2 E3 E4 E5 E6 E7 : Nat}
    (f1 : Y9 + 2 ^ 64 * E1 = G9 + H0 + 0) (f2 : Y10 + 2 ^ 64 * E2 = G10 + L1 + E1)
    (f3 : Y11 + 2 ^ 64 * E3 = G11 + H1 + E2) (f4 : Y12 + 2 ^ 64 * E4 = G12 + L2 + E3)
    (f5 : Y13 + 2 ^ 64 * E5 = G13 + H2 + E4) (f6 : Y14 + 2 ^ 64 * E6 = G14 + L3 + E5)
    (f7 : Y6 + 2 ^ 64 * E7 = G6 + H3 + E6)
    (m0 : L0 + 2 ^ 64 * H0 = P0) (m1 : L1 + 2 ^ 64 * H1 = P1)
    (m2 : L2 + 2 ^ 64 * H2 = P2) (m3 : L3 + 2 ^ 64 * H3 = P3) :
    L0 + 2 ^ 64 * Y9 + 2 ^ 128 * Y10 + 2 ^ 192 * Y11 +
        2 ^ 256 * (Y12 + 2 ^ 64 * Y13 + 2 ^ 128 * Y14 + 2 ^ 192 * Y6 + 2 ^ 256 * E7) =
      2 ^ 64 * (G9 + 2 ^ 64 * G10 + 2 ^ 128 * G11 + 2 ^ 192 * G12 +
          2 ^ 256 * (G13 + 2 ^ 64 * G14 + 2 ^ 128 * G6)) +
        P0 + 2 ^ 128 * P1 + 2 ^ 256 * (P2 + 2 ^ 128 * P3) := by
  omega

/-- What `sqrDiag` computes, word by word. -/
theorem diag_value (a0 a1 a2 a3 d9 d10 d11 d12 d13 d14 : Word) :
    let k1 := carryOut d9 d9 false
    let k2 := carryOut d10 d10 k1
    let k3 := carryOut d11 d11 k2
    let k4 := carryOut d12 d12 k3
    let k5 := carryOut d13 d13 k4
    let k6 := carryOut d14 d14 k5
    let g9 := addCarry d9 d9 false
    let g10 := addCarry d10 d10 k1
    let g11 := addCarry d11 d11 k2
    let g12 := addCarry d12 d12 k3
    let g13 := addCarry d13 d13 k4
    let g14 := addCarry d14 d14 k5
    let g6 := addCarry 0 0 k6
    let e1 := carryOut g9 (mulHi a0 a0) false
    let e2 := carryOut g10 (a1 * a1) e1
    let e3 := carryOut g11 (mulHi a1 a1) e2
    let e4 := carryOut g12 (a2 * a2) e3
    let e5 := carryOut g13 (mulHi a2 a2) e4
    let e6 := carryOut g14 (a3 * a3) e5
    ∃ e : Nat, (a0 * a0).toNat + 2 ^ 64 * (addCarry g9 (mulHi a0 a0) false).toNat +
        2 ^ 128 * (addCarry g10 (a1 * a1) e1).toNat +
        2 ^ 192 * (addCarry g11 (mulHi a1 a1) e2).toNat +
        2 ^ 256 * ((addCarry g12 (a2 * a2) e3).toNat + 2 ^ 64 * (addCarry g13 (mulHi a2 a2) e4).toNat +
          2 ^ 128 * (addCarry g14 (a3 * a3) e5).toNat +
          2 ^ 192 * (addCarry g6 (mulHi a3 a3) e6).toNat + 2 ^ 256 * e) =
      2 ^ 64 * (2 * (d9.toNat + 2 ^ 64 * d10.toNat + 2 ^ 128 * d11.toNat + 2 ^ 192 * d12.toNat +
          2 ^ 256 * (d13.toNat + 2 ^ 64 * d14.toNat))) +
        a0.toNat * a0.toNat + 2 ^ 128 * (a1.toNat * a1.toNat) +
        2 ^ 256 * (a2.toNat * a2.toNat + 2 ^ 128 * (a3.toNat * a3.toNat)) := by
  intro k1 k2 k3 k4 k5 k6 g9 g10 g11 g12 g13 g14 g6 e1 e2 e3 e4 e5 e6
  refine ⟨(carryOut g6 (mulHi a3 a3) e6).toNat, ?_⟩
  rw [← dbl_arith (addCarry_value d9 d9 false) (addCarry_value d10 d10 k1)
    (addCarry_value d11 d11 k2) (addCarry_value d12 d12 k3) (addCarry_value d13 d13 k4)
    (addCarry_value d14 d14 k5) (addCarry_value 0 0 k6) (Bool.toNat_le _)]
  exact sq_arith (addCarry_value g9 (mulHi a0 a0) false) (addCarry_value g10 (a1 * a1) e1)
    (addCarry_value g11 (mulHi a1 a1) e2) (addCarry_value g12 (a2 * a2) e3)
    (addCarry_value g13 (mulHi a2 a2) e4) (addCarry_value g14 (a3 * a3) e5)
    (addCarry_value g6 (mulHi a3 a3) e6)
    (mul_lo_hi a0 a0) (mul_lo_hi a1 a1) (mul_lo_hi a2 a2) (mul_lo_hi a3 a3)

theorem sqrDiag_ok (s : State) (hz : s.gpr .x17 = 0) :
    WP isa (.block sqrDiag) s fun t => ∃ e : Nat,
      (t.gpr .x8).toNat + 2 ^ 64 * (t.gpr .x9).toNat + 2 ^ 128 * (t.gpr .x10).toNat +
          2 ^ 192 * (t.gpr .x11).toNat +
          2 ^ 256 * ((t.gpr .x12).toNat + 2 ^ 64 * (t.gpr .x13).toNat +
            2 ^ 128 * (t.gpr .x14).toNat + 2 ^ 192 * (t.gpr .x6).toNat + 2 ^ 256 * e) =
        2 ^ 64 * (2 * ((s.gpr .x9).toNat + 2 ^ 64 * (s.gpr .x10).toNat +
            2 ^ 128 * (s.gpr .x11).toNat + 2 ^ 192 * (s.gpr .x12).toNat +
            2 ^ 256 * ((s.gpr .x13).toNat + 2 ^ 64 * (s.gpr .x14).toNat))) +
          (s.gpr .x2).toNat * (s.gpr .x2).toNat + 2 ^ 128 * ((s.gpr .x3).toNat * (s.gpr .x3).toNat) +
          2 ^ 256 * ((s.gpr .x4).toNat * (s.gpr .x4).toNat +
            2 ^ 128 * ((s.gpr .x5).toNat * (s.gpr .x5).toNat)) ∧
      Keeps [.x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_mul_x, exec_umulh_x, exec_adds_x,
    exec_adcs_x, exec_adc_x, Option.some.injEq, exists_eq_left']
  simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, RegUpd.c_write,
    reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq, hz]
  have h := diag_value (s.gpr .x2) (s.gpr .x3) (s.gpr .x4) (s.gpr .x5) (s.gpr .x9) (s.gpr .x10)
    (s.gpr .x11) (s.gpr .x12) (s.gpr .x13) (s.gpr .x14)
  dsimp only [addCarry, carryOut, mulHi, Size.bits] at h ⊢
  obtain ⟨e, h⟩ := h
  refine ⟨e, h, ⟨?_, by simp only [RegUpd.mem_write, RegUpd.mem_addWithCarry],
      by simp only [RegUpd.rd_write, RegUpd.rd_addWithCarry],
      by simp only [RegUpd.wr_write, RegUpd.wr_addWithCarry],
      by simp only [RegUpd.sp_write, RegUpd.sp_addWithCarry]⟩⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
    hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2,
    ite_false]

/-- The high half x12–x14, x6 of the square folded back into x8–x11 as 38,
less the high words of `38 · x12` and `38 · x13`, left in x4 and x13. -/
abbrev sqrFold38 : List Instr :=
  [.movz .w .x3 38 0, .mul .x .x7 .x3 .x12, .umulh .x4 .x3 .x12, .adds .x .x8 .x8 .x7,
    .mul .x .x7 .x3 .x13, .umulh .x13 .x3 .x13, .adcs .x .x9 .x9 .x7,
    .mul .x .x7 .x3 .x14, .umulh .x14 .x3 .x14, .adcs .x .x10 .x10 .x7,
    .mul .x .x7 .x3 .x6, .umulh .x6 .x3 .x6, .adcs .x .x11 .x11 .x7,
    .adc .x .x12 .x17 .x17, .adds .x .x11 .x11 .x14, .adc .x .x12 .x12 .x6]

theorem sqrFold38_ok (s : State) (hz : s.gpr .x17 = 0) :
    WP isa (.block sqrFold38) s fun t =>
      val4 (t.gpr .x8) (t.gpr .x9) (t.gpr .x10) (t.gpr .x11) + 2 ^ 256 * (t.gpr .x12).toNat +
          2 ^ 64 * (t.gpr .x4).toNat + 2 ^ 128 * (t.gpr .x13).toNat =
        val4 (s.gpr .x8) (s.gpr .x9) (s.gpr .x10) (s.gpr .x11) +
          38 * val4 (s.gpr .x12) (s.gpr .x13) (s.gpr .x14) (s.gpr .x6) ∧
      (t.gpr .x4).toNat < 38 ∧ (t.gpr .x13).toNat < 38 ∧ (t.gpr .x12).toNat < 40 ∧
      Keeps [.x13, .x14, .x6, .x3, .x4, .x7, .x8, .x9, .x10, .x11, .x12] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_movz_w, exec_mul_x, exec_umulh_x,
    exec_adds_x, exec_adcs_x, exec_adc_x, Option.some.injEq, exists_eq_left']
  simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, RegUpd.c_write,
    reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq, hz]
  have h := fold38_value (BitVec.setWidth 64 (BitVec.setWidth 32 (38 : BitVec 16)))
    (s.gpr .x8) (s.gpr .x9) (s.gpr .x10) (s.gpr .x11)
    (s.gpr .x12) (s.gpr .x13) (s.gpr .x14) (s.gpr .x6) rfl
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

/-- The five words x8–x11, x12 and the words x4 and x13 one and two words
up, folded at bit 255. -/
abbrev sqrFold19 : List Instr :=
  [.adds .x .x7 .x11 .x11, .lsr .x .x11 .x7 1, .adc .x .x2 .x12 .x12, .movz .w .x3 19 0,
    .mul .x .x7 .x3 .x2, .adds .x .x8 .x8 .x7, .adcs .x .x9 .x9 .x4,
    .adcs .x .x10 .x10 .x13, .adc .x .x11 .x11 .x17]

theorem sqrFold19_ok (s : State) (hz : s.gpr .x17 = 0) (h16 : (s.gpr .x12).toNat < 40)
    (h9 : (s.gpr .x4).toNat < 38) (h3 : (s.gpr .x13).toNat < 38) :
    WP isa (.block sqrFold19) s fun t => ∃ q,
      val4 (t.gpr .x8) (t.gpr .x9) (t.gpr .x10) (t.gpr .x11) + (2 ^ 255 - 19) * q =
        val4 (s.gpr .x8) (s.gpr .x9) (s.gpr .x10) (s.gpr .x11) + 2 ^ 256 * (s.gpr .x12).toNat +
          2 ^ 64 * (s.gpr .x4).toNat + 2 ^ 128 * (s.gpr .x13).toNat ∧
      val4 (t.gpr .x8) (t.gpr .x9) (t.gpr .x10) (t.gpr .x11) < 2 ^ 256 - 38 ∧
      Keeps [.x3, .x2, .x7, .x8, .x9, .x10, .x11] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_adds_x, exec_lsr1_x, exec_adc_x,
    exec_movz_w, exec_mul_x, exec_adcs_x, Option.some.injEq, exists_eq_left']
  simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, RegUpd.c_write,
    reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq, hz]
  dsimp only [Size.bits]
  have h := add4_value (s.gpr .x8) (s.gpr .x9) (s.gpr .x10)
    ((s.gpr .x11 + s.gpr .x11 + BitVec.ofNat 64 false.toNat) >>> 1)
    (BitVec.setWidth 64 (BitVec.setWidth 32 (19 : BitVec 16)) * (s.gpr .x12 + s.gpr .x12 +
      BitVec.ofNat 64 (decide (2 ^ 64 ≤ (s.gpr .x11).toNat + (s.gpr .x11).toNat + false.toNat)).toNat))
    (s.gpr .x4) (s.gpr .x13) 0 false
  dsimp only [addCarry, carryOut] at h
  have hU := fold_lo (s.gpr .x11)
  have hM := fold_hi19 (s.gpr .x11) (s.gpr .x12) (by omega)
  have z : (0 : BitVec 64).toNat = 0 := rfl
  have := (s.gpr .x8).isLt
  have := (s.gpr .x9).isLt
  have := (s.gpr .x10).isLt
  have := (s.gpr .x11).isLt
  simp only [val4, z, Bool.toNat_false, Nat.add_zero, Nat.mul_zero] at h hU hM ⊢
  refine ⟨2 * (s.gpr .x12).toNat + (s.gpr .x11).toNat / 2 ^ 63, ?_, ?_,
    ⟨?_, by simp only [RegUpd.mem_write, RegUpd.mem_addWithCarry],
      by simp only [RegUpd.rd_write, RegUpd.rd_addWithCarry],
      by simp only [RegUpd.wr_write, RegUpd.wr_addWithCarry],
      by simp only [RegUpd.sp_write, RegUpd.sp_addWithCarry]⟩⟩
  · omega
  · omega
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2, ite_false]

theorem sq_expand (x0 x1 x2 x3 : Nat) :
    (x0 + 2 ^ 64 * x1 + 2 ^ 128 * x2 + 2 ^ 192 * x3) * (x0 + 2 ^ 64 * x1 + 2 ^ 128 * x2 + 2 ^ 192 * x3) =
      2 ^ 64 * (2 * (x0 * x1 + 2 ^ 64 * (x0 * x2) + 2 ^ 128 * (x0 * x3 + x1 * x2) +
          2 ^ 192 * (x1 * x3) + 2 ^ 256 * (x2 * x3))) +
        x0 * x0 + 2 ^ 128 * (x1 * x1) + 2 ^ 256 * (x2 * x2 + 2 ^ 128 * (x3 * x3)) := by
  grind

theorem sqr4_eq (o a : Nat) :
    Impl.X25519.AArch64.Alt.sqr4 o a =
      sqrCross a ++ (sqrDiag ++ (sqrFold38 ++ (sqrFold19 ++
        ([.stp .x8 .x9 .x0 o, .stp .x10 .x11 .x0 (o + 16)] : List Instr)))) := rfl

/-- `[o] := [a]²`, modulo `p` and below `2·p`. -/
theorem sqr4_ok {s : State} {base : Addr} (hs : Scr s base large) {o a : Nat}
    (ho : AltRange o large) (ha : AltRange a large) (hz : s.gpr .x17 = 0) :
    WP isa (.block (Impl.X25519.AArch64.Alt.sqr4 o a)) s fun t =>
      AltOp base o s t ∧ fe t.mem base o < 2 ^ 256 - 38 ∧ ∃ q, fe t.mem base o + (2 ^ 255 - 19) * q =
        fe s.mem base a * fe s.mem base a := by
  have _hcap := workSize_le large
  rw [sqr4_eq, WP.block_append_iff]
  refine WP.mono (sqrCross_ok hs ha hz) fun s₁ ⟨x2, x3, x4, x5, e1, k1⟩ => ?_
  have hs₁ := hs.of_keeps k1 (by decide)
  have z1 : s₁.gpr .x17 = 0 := (k1.gpr _ (by decide)).trans hz
  rw [WP.block_append_iff]
  refine WP.mono (sqrDiag_ok s₁ z1) fun s₂ ⟨e, e2, k2⟩ => ?_
  have z2 : s₂.gpr .x17 = 0 := (k2.gpr _ (by decide)).trans z1
  rw [WP.block_append_iff]
  refine WP.mono (sqrFold38_ok s₂ z2) fun s₃ ⟨e3, b4, b13, b12, k3⟩ => ?_
  have z3 : s₃.gpr .x17 = 0 := (k3.gpr _ (by decide)).trans z2
  rw [WP.block_append_iff]
  refine WP.mono (sqrFold19_ok s₃ z3 b12 b4 b13) fun s₄ ⟨q, e4, l4, k4⟩ => ?_
  have hs₄ := ((hs₁.of_keeps k2 (by decide)).of_keeps k3 (by decide)).of_keeps k4 (by decide)
  refine WP.mono (store4_ok hs₄ ho.1 ho.2.1 ho.2.2 .x8 .x9 .x10 .x11) fun t ht => ?_
  subst t
  have m4 : s₄.mem = s.mem := by rw [k4.mem, k3.mem, k2.mem, k1.mem]
  have _ho := ho.2.2
  have hf := fe_st4 s₄.mem base (o := o) (by omega) (s₄.gpr .x8) (s₄.gpr .x9) (s₄.gpr .x10)
    (s₄.gpr .x11)
  rw [x2, x3, x4, x5] at e2
  have hA : fe s.mem base a * fe s.mem base a = _ := sq_expand (word s.mem base a).toNat
    (word s.mem base (a + 8)).toNat (word s.mem base (a + 16)).toNat (word s.mem base (a + 24)).toNat
  have hlt := val4_lt (word s.mem base a) (word s.mem base (a + 8)) (word s.mem base (a + 16))
    (word s.mem base (a + 24))
  have hsq : fe s.mem base a * fe s.mem base a ≤ (2 ^ 256 - 1) * (2 ^ 256 - 1) :=
    Nat.mul_le_mul (by simp only [fe]; omega) (by simp only [fe]; omega)
  refine ⟨⟨fun r hr => ?_, by rw [rd_withMem, k4.rd, k3.rd, k2.rd, k1.rd],
    by rw [wr_withMem, k4.wr, k3.wr, k2.wr, k1.wr], by rw [sp_withMem, k4.sp, k3.sp, k2.sp, k1.sp],
    ?_⟩, by rw [mem_withMem, hf]; exact l4,
    q + 2 * val4 (s₂.gpr .x12) (s₂.gpr .x13) (s₂.gpr .x14) (s₂.gpr .x6), ?_⟩
  · simp only [altClob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [gpr_withMem, k4.gpr _ (by simp only [List.mem_cons, List.not_mem_nil, or_false, hr,
      not_false_eq_true]), k3.gpr _ (by simp only [List.mem_cons, List.not_mem_nil, or_false, hr,
      not_false_eq_true]), k2.gpr _ (by simp only [List.mem_cons, List.not_mem_nil, or_false, hr,
      not_false_eq_true]), k1.gpr _ (by simp only [List.mem_cons, List.not_mem_nil, or_false, hr,
      not_false_eq_true])]
  · rw [mem_withMem, ← m4]
    exact st4_outside _ _ (by omega) _ _ _ _
  · rw [mem_withMem, hf]
    rw [e1] at e2
    simp only [val4] at e3 e4 ⊢
    omega

end VG.Proof.X25519.AArch64.Alt
