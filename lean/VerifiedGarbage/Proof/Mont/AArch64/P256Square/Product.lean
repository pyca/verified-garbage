import VerifiedGarbage.Impl.Mont.AArch64.P256Square
import VerifiedGarbage.Proof.Ed25519.AArch64.SqrRows
import VerifiedGarbage.Proof.Mont.AArch64.P256Square.Words

namespace VG.Proof.Mont.AArch64.P256Square
open VG VG.AArch64 VG.Impl.Mont.AArch64.P256Square
open VG.Proof.Ed25519.Word64
open VG.Proof.Ed25519.AArch64

theorem cross_arith {v1 v2 v3 v4 v5 v6 k7 v7 v8 v9 k10 v10 v11 v12 _k13 v13 v14 v15 k16 v16 _k18 v18 k19 v19 k21 v21 k23 v23 _k25 v25 P0 P1 P2 P3 P4 P5 : Nat}
    (ev7 : v7 + 2^64*k7 = v3 + v2 + 0)
    (ev10 : v10 + 2^64*k10 = v5 + v4 + k7)
    (ev13 : v13 + 2^64*_k13 = v6 + 0 + k10)
    (ev16 : v16 + 2^64*k16 = v9 + v11 + 0)
    (ev18 : v18 + 2^64*_k18 = v12 + 0 + k16)
    (ev19 : v19 + 2^64*k19 = v10 + v8 + 0)
    (ev21 : v21 + 2^64*k21 = v13 + v16 + k19)
    (ev23 : v23 + 2^64*k23 = v14 + v18 + k21)
    (ev25 : v25 + 2^64*_k25 = v15 + 0 + k23)
    (m0 : v1 + 2^64*v2 = P0)
    (m1 : v3 + 2^64*v4 = P1)
    (m2 : v5 + 2^64*v6 = P2)
    (m3 : v8 + 2^64*v9 = P3)
    (m4 : v11 + 2^64*v12 = P4)
    (m5 : v14 + 2^64*v15 = P5)
    (b0 : P0 ≤ (2^64-1)*(2^64-1))
    (b1 : P1 ≤ (2^64-1)*(2^64-1))
    (b2 : P2 ≤ (2^64-1)*(2^64-1))
    (b3 : P3 ≤ (2^64-1)*(2^64-1))
    (b4 : P4 ≤ (2^64-1)*(2^64-1))
    (b5 : P5 ≤ (2^64-1)*(2^64-1)) :
    v1 + 2^64*v7 + 2^128*v19 + 2^192*v21 + 2^256*v23 + (2^256*2^64)*v25 = P0 + 2^64*P1 + 2^128*P2 + 2^128*P3 + 2^192*P4 + 2^256*P5 := by
  omega

theorem cross_value (a0 a1 a2 a3 : BitVec 64) :
    let v1 := a1 * a0
    let v2 := mulHi a1 a0
    let v3 := a2 * a0
    let v4 := mulHi a2 a0
    let v5 := a3 * a0
    let v6 := mulHi a3 a0
    let k7 := carryOut v3 v2 false
    let v7 := addCarry v3 v2 false
    let v8 := a2 * a1
    let v9 := mulHi a2 a1
    let k10 := carryOut v5 v4 k7
    let v10 := addCarry v5 v4 k7
    let v11 := a3 * a1
    let v12 := mulHi a3 a1
    let _k13 := carryOut v6 0 k10
    let v13 := addCarry v6 0 k10
    let v14 := a3 * a2
    let v15 := mulHi a3 a2
    let k16 := carryOut v9 v11 false
    let v16 := addCarry v9 v11 false
    let _v17 := a0 * a0
    let _k18 := carryOut v12 0 k16
    let v18 := addCarry v12 0 k16
    let k19 := carryOut v10 v8 false
    let v19 := addCarry v10 v8 false
    let _v20 := mulHi a0 a0
    let k21 := carryOut v13 v16 k19
    let v21 := addCarry v13 v16 k19
    let _v22 := a1 * a1
    let k23 := carryOut v14 v18 k21
    let v23 := addCarry v14 v18 k21
    let _v24 := mulHi a1 a1
    let _k25 := carryOut v15 0 k23
    let v25 := addCarry v15 0 k23
    v1.toNat + 2^64*v7.toNat + 2^128*v19.toNat + 2^192*v21.toNat + 2^256*v23.toNat + (2^256*2^64)*v25.toNat = (a1.toNat*a0.toNat) + 2^64*(a2.toNat*a0.toNat) + 2^128*(a3.toNat*a0.toNat) + 2^128*(a2.toNat*a1.toNat) + 2^192*(a3.toNat*a1.toNat) + 2^256*(a3.toNat*a2.toNat) := by
  intro v1 v2 v3 v4 v5 v6 k7 v7 v8 v9 k10 v10 v11 v12 _k13 v13 v14 v15 k16 v16 _v17 _k18 v18 k19 v19 _v20 k21 v21 _v22 k23 v23 _v24 _k25 v25
  exact cross_arith (addCarry_value v3 v2 false)
    (addCarry_value v5 v4 k7)
    (addCarry_value v6 0 k10)
    (addCarry_value v9 v11 false)
    (addCarry_value v12 0 k16)
    (addCarry_value v10 v8 false)
    (addCarry_value v13 v16 k19)
    (addCarry_value v14 v18 k21)
    (addCarry_value v15 0 k23)
    (mul_lo_hi a1 a0)
    (mul_lo_hi a2 a0)
    (mul_lo_hi a3 a0)
    (mul_lo_hi a2 a1)
    (mul_lo_hi a3 a1)
    (mul_lo_hi a3 a2)
    (mul_le a1 a0)
    (mul_le a2 a0)
    (mul_le a3 a0)
    (mul_le a2 a1)
    (mul_le a3 a1)
    (mul_le a3 a2)

theorem cross_ok (s : State) (hz : s.gpr .x7 = 0) :
    WP isa (.block crossCode) s fun t =>
      (t.gpr .x9).toNat + 2^64*(t.gpr .x10).toNat + 2^128*(t.gpr .x11).toNat + 2^192*(t.gpr .x12).toNat + 2^256*(t.gpr .x13).toNat + (2^256*2^64)*(t.gpr .x14).toNat =
        ((s.gpr .x5).toNat*(s.gpr .x4).toNat) + 2^64*((s.gpr .x16).toNat*(s.gpr .x4).toNat) + 2^128*((s.gpr .x17).toNat*(s.gpr .x4).toNat) + 2^128*((s.gpr .x16).toNat*(s.gpr .x5).toNat) + 2^192*((s.gpr .x17).toNat*(s.gpr .x5).toNat) + 2^256*((s.gpr .x17).toNat*(s.gpr .x16).toNat) ∧
      t.gpr .x8 = s.gpr .x4 * s.gpr .x4 ∧
      t.gpr .x4 = mulHi (s.gpr .x4) (s.gpr .x4) ∧
      t.gpr .x2 = s.gpr .x5 * s.gpr .x5 ∧
      t.gpr .x5 = mulHi (s.gpr .x5) (s.gpr .x5) ∧
      Keeps [.x1,.x2,.x3,.x4,.x5,.x6,.x8,.x9,.x10,.x11,.x12,.x13,.x14] s t := by
  apply WP.of_runBlock
  simp only [crossCode, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, RegUpd.c_write,
    BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, hz,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, trivial, trivial, trivial, trivial, ⟨?_, by simp only [RegUpd.mem_write, RegUpd.mem_addWithCarry],
      by simp only [RegUpd.rd_write, RegUpd.rd_addWithCarry],
      by simp only [RegUpd.wr_write, RegUpd.wr_addWithCarry],
      by simp only [RegUpd.sp_write, RegUpd.sp_addWithCarry]⟩⟩
  · have h := cross_value (s.gpr .x4) (s.gpr .x5) (s.gpr .x16) (s.gpr .x17)
    dsimp only [addCarry, carryOut, mulHi, Size.bits] at h ⊢
    exact h
  · reg_keeps

theorem double_ok (s : State) (hz : s.gpr .x7 = 0) :
    WP isa (.block doubleCode) s fun t =>
      val4 (t.gpr .x9) (t.gpr .x10) (t.gpr .x11) (t.gpr .x12) +
        2^256*((t.gpr .x13).toNat + 2^64*(t.gpr .x14).toNat + 2^128*(t.gpr .x15).toNat) =
      2*(val4 (s.gpr .x9) (s.gpr .x10) (s.gpr .x11) (s.gpr .x12) +
        2^256*((s.gpr .x13).toNat + 2^64*(s.gpr .x14).toNat)) ∧
      t.gpr .x3 = s.gpr .x16 * s.gpr .x16 ∧
      t.gpr .x16 = mulHi (s.gpr .x16) (s.gpr .x16) ∧
      t.gpr .x6 = s.gpr .x17 * s.gpr .x17 ∧
      t.gpr .x17 = mulHi (s.gpr .x17) (s.gpr .x17) ∧
      Keeps [.x3,.x6,.x9,.x10,.x11,.x12,.x13,.x14,.x15,.x16,.x17] s t := by
  apply WP.of_runBlock
  simp only [doubleCode, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, RegUpd.c_write,
    BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, hz,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, trivial, trivial, trivial, trivial, ⟨?_, by simp only [RegUpd.mem_write, RegUpd.mem_addWithCarry],
      by simp only [RegUpd.rd_write, RegUpd.rd_addWithCarry],
      by simp only [RegUpd.wr_write, RegUpd.wr_addWithCarry],
      by simp only [RegUpd.sp_write, RegUpd.sp_addWithCarry]⟩⟩
  · have h := sqrDouble_value (s.gpr .x9) (s.gpr .x10) (s.gpr .x11) (s.gpr .x12)
      (s.gpr .x13) (s.gpr .x14)
    dsimp only [addCarry, carryOut, mulHi, Size.bits] at h ⊢
    exact h
  · reg_keeps

theorem diag_value (w1 w2 w3 w4 w5 w6 w7 d0 d1 d2 d3 d4 d5 d6 d7 : BitVec 64) :
    let k1 := carryOut w1 d1 false
    let v1 := addCarry w1 d1 false
    let k2 := carryOut w2 d2 k1
    let v2 := addCarry w2 d2 k1
    let k3 := carryOut w3 d3 k2
    let v3 := addCarry w3 d3 k2
    let k4 := carryOut w4 d4 k3
    let v4 := addCarry w4 d4 k3
    let k5 := carryOut w5 d5 k4
    let v5 := addCarry w5 d5 k4
    let k6 := carryOut w6 d6 k5
    let v6 := addCarry w6 d6 k5
    let k7 := carryOut w7 d7 k6
    let v7 := addCarry w7 d7 k6
    val4 d0 v1 v2 v3 + 2^256*val4 v4 v5 v6 v7 + 2^256*(2^256*k7.toNat) =
      2^64*(val4 w1 w2 w3 w4 + 2^256*(w5.toNat+2^64*w6.toNat+2^128*w7.toNat)) + val4 d0 d1 d2 d3 + 2^256*val4 d4 d5 d6 d7 := by
  intro k1 v1 k2 v2 k3 v3 k4 v4 k5 v5 k6 v6 k7 v7
  have h1 := addCarry_value w1 d1 false
  have h2 := addCarry_value w2 d2 k1
  have h3 := addCarry_value w3 d3 k2
  have h4 := addCarry_value w4 d4 k3
  have h5 := addCarry_value w5 d5 k4
  have h6 := addCarry_value w6 d6 k5
  have h7 := addCarry_value w7 d7 k6
  change v1.toNat + 2^64*k1.toNat = w1.toNat + d1.toNat + 0 at h1
  change v2.toNat + 2^64*k2.toNat = w2.toNat + d2.toNat + k1.toNat at h2
  change v3.toNat + 2^64*k3.toNat = w3.toNat + d3.toNat + k2.toNat at h3
  change v4.toNat + 2^64*k4.toNat = w4.toNat + d4.toNat + k3.toNat at h4
  change v5.toNat + 2^64*k5.toNat = w5.toNat + d5.toNat + k4.toNat at h5
  change v6.toNat + 2^64*k6.toNat = w6.toNat + d6.toNat + k5.toNat at h6
  change v7.toNat + 2^64*k7.toNat = w7.toNat + d7.toNat + k6.toNat at h7
  simp only [val4]
  omega

theorem diag_ok (s : State) :
    WP isa (.block diagCode) s fun t => ∃ c : Nat,
      val4 (t.gpr .x8) (t.gpr .x9) (t.gpr .x10) (t.gpr .x11) +
        2^256*val4 (t.gpr .x12) (t.gpr .x13) (t.gpr .x14) (t.gpr .x15) + 2^256*(2^256*c) =
      2^64*(val4 (s.gpr .x9) (s.gpr .x10) (s.gpr .x11) (s.gpr .x12) + 2^256*((s.gpr .x13).toNat+2^64*(s.gpr .x14).toNat+2^128*(s.gpr .x15).toNat)) + val4 (s.gpr .x8) (s.gpr .x4) (s.gpr .x2) (s.gpr .x5) + 2^256*val4 (s.gpr .x3) (s.gpr .x16) (s.gpr .x6) (s.gpr .x17) ∧
      t.gpr .x1 = s.gpr .x8 <<< 32 ∧ t.gpr .x2 = s.gpr .x8 >>> 32 ∧
      Keeps [.x1,.x2,.x9,.x10,.x11,.x12,.x13,.x14,.x15] s t := by
  apply WP.of_runBlock
  simp only [diagCode, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, RegUpd.c_write,
    BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq,
    show 32 < Size.x.bits by decide,
    Option.some.injEq, exists_eq_left']
  have h := diag_value (s.gpr .x9) (s.gpr .x10) (s.gpr .x11) (s.gpr .x12) (s.gpr .x13) (s.gpr .x14) (s.gpr .x15) (s.gpr .x8) (s.gpr .x4) (s.gpr .x2) (s.gpr .x5) (s.gpr .x3) (s.gpr .x16) (s.gpr .x6) (s.gpr .x17)
  dsimp only [addCarry, carryOut, mulHi, Size.bits] at h ⊢
  refine ⟨_, h, trivial, trivial, ⟨?_, by simp only [RegUpd.mem_write, RegUpd.mem_addWithCarry],
      by simp only [RegUpd.rd_write, RegUpd.rd_addWithCarry],
      by simp only [RegUpd.wr_write, RegUpd.wr_addWithCarry],
      by simp only [RegUpd.sp_write, RegUpd.sp_addWithCarry]⟩⟩
  reg_keeps

theorem expand_square (a b c d : Nat) :
    (a+2^64*b+2^128*c+2^192*d)*(a+2^64*b+2^128*c+2^192*d) =
    2^64*(2*(b*a+2^64*(c*a)+2^128*(d*a)+2^128*(c*b)+2^192*(d*b)+2^256*(d*c))) +
    a*a+2^128*(b*b)+2^256*(c*c)+2^256*(2^128*(d*d)) := by
  grind

abbrev productClob : List Reg :=
  [.x1,.x2,.x3,.x4,.x5,.x6,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15,.x16,.x17]

/-- The scheduled cross products, doubling and diagonal additions form the exact 512-bit square. -/
theorem product_ok (s : State) (hz : s.gpr .x7 = 0) :
    WP isa (.block (crossCode ++ doubleCode ++ diagCode)) s fun t =>
      val4 (t.gpr .x8) (t.gpr .x9) (t.gpr .x10) (t.gpr .x11) +
        2^256*val4 (t.gpr .x12) (t.gpr .x13) (t.gpr .x14) (t.gpr .x15) =
      val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x16) (s.gpr .x17) *
        val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x16) (s.gpr .x17) ∧
      t.gpr .x1 = t.gpr .x8 <<< 32 ∧ t.gpr .x2 = t.gpr .x8 >>> 32 ∧
      Keeps productClob s t := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (cross_ok s hz) fun s₁ ⟨e₁, d0, d1, d2, d3, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (double_ok s₁ ((k₁.gpr _ (by decide)).trans hz))
    fun s₂ ⟨e₂, d4, d5, d6, d7, k₂⟩ => ?_
  refine WP.mono (diag_ok s₂) fun t ⟨c, e₃, lo, hi, k₃⟩ => ?_
  have h8 : t.gpr .x8 = s₂.gpr .x8 := k₃.gpr _ (by decide)
  refine ⟨?_, by rw [h8]; exact lo, by rw [h8]; exact hi,
    (k₁.mono (by decide)).trans ((k₂.mono (by decide)).trans (k₃.mono (by decide)))⟩
  rw [e₂, k₂.gpr .x8 (by decide), k₂.gpr .x4 (by decide), k₂.gpr .x2 (by decide),
    k₂.gpr .x5 (by decide), d0, d1, d2, d3, d4, d5, d6, d7,
    k₁.gpr .x16 (by decide), k₁.gpr .x17 (by decide)] at e₃
  have m0 := mul_lo_hi (s.gpr .x4) (s.gpr .x4)
  have m1 := mul_lo_hi (s.gpr .x5) (s.gpr .x5)
  have m2 := mul_lo_hi (s.gpr .x16) (s.gpr .x16)
  have m3 := mul_lo_hi (s.gpr .x17) (s.gpr .x17)
  have he := expand_square (s.gpr .x4).toNat (s.gpr .x5).toNat (s.gpr .x16).toNat (s.gpr .x17).toNat
  have hb := val4_lt (s.gpr .x4) (s.gpr .x5) (s.gpr .x16) (s.gpr .x17)
  have hbb := Nat.mul_lt_mul'' hb hb
  simp only [val4] at e₂ e₃ hbb ⊢
  omega_using [e₁, e₃, m0, m1, m2, m3, he, hbb]

end VG.Proof.Mont.AArch64.P256Square
