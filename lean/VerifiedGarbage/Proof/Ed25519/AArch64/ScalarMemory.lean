module

public import VerifiedGarbage.Proof.Ed25519.ScalarWord
import VerifiedGarbage.Proof.Ed25519.Scalar
public import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Ed25519.AArch64.Mem
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Ed25519.AArch64.Scalar
public import VerifiedGarbage.Proof.Ed25519.AArch64.Step
public import VerifiedGarbage.Proof.Ed25519.Canonical64
public import VerifiedGarbage.Spec.Ed25519

/-! ### `Ed25519.AArch64.ScalarStep`, which this module and modules that import it used -/

section

/-! The conditional subtraction of the Ed25519 order from a four-word value. -/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64 Word64
open VG.Spec.Ed25519 (L)

def scalarValue (s : State) : Nat := val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7)
def savedValue (s : State) : Nat := val4 (s.gpr .x21) (s.gpr .x22) (s.gpr .x23) (s.gpr .x24)

theorem order_limbs : val4 orderLo orderHi 0 orderTop = L := by decide

theorem subtract_chain (a b c d : Word) :
    let c0 := carryOut a (~~~orderLo) true
    let c1 := carryOut b (~~~orderHi) c0
    let c2 := carryOut c (~~~0) c1
    let c3 := carryOut d (~~~orderTop) c2
    let v := val4 (addCarry a (~~~orderLo) true) (addCarry b (~~~orderHi) c0)
      (addCarry c (~~~0) c1) (addCarry d (~~~orderTop) c2)
    c3 = decide (L ≤ val4 a b c d) ∧
      v + L = val4 a b c d + 2 ^ 256 * (1 - c3.toNat) := by
  intro c0 c1 c2 c3 v
  have e : v + val4 orderLo orderHi 0 orderTop = val4 a b c d + 2 ^ 256 * (1 - c3.toNat) := by
    simpa only [Bool.toNat_true, Nat.sub_self, Nat.add_zero] using
      sub4_value a b c d orderLo orderHi 0 orderTop true
  rw [order_limbs] at e
  have hv : v < 2 ^ 256 := val4_lt _ _ _ _
  have hx := val4_lt a b c d
  clear_value v c3 c2 c1 c0
  refine ⟨?_, e⟩
  cases c3 <;> simp only [Bool.toNat_false, Bool.toNat_true] at e
  · exact (decide_eq_false (by omega_using [hv, e])).symm
  · exact (decide_eq_true (by omega_using [e])).symm

theorem scalarSubtract_ok (s : State) (hz : s.gpr .x10 = 0) :
    WP isa (.block scalarSubtract) s fun t =>
      t.c = decide (L ≤ scalarValue s) ∧
      scalarValue t + L = scalarValue s + 2 ^ 256 * (1 - (decide (L ≤ scalarValue s)).toNat) ∧
      savedValue t = scalarValue s ∧
      Keeps [.x3, .x4, .x5, .x6, .x7, .x21, .x22, .x23, .x24] s t := by
  apply WP.of_runBlock
  simp only [scalarSubtract, const64, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, mov, exec, read_x,
    show (0 : Nat) < 4096 from by decide,
    show 16 * 0 < Size.x.bits from by decide, show 16 * 1 < Size.x.bits from by decide,
    show 16 * 2 < Size.x.bits from by decide, show 16 * 3 < Size.x.bits from by decide,
    scalarValue, savedValue, RegUpd.gpr_write, RegUpd.gpr_addWithCarry,
    RegUpd.c_write, RegUpd.c_addWithCarry, BitVec.setWidth_eq, BitVec.add_zero,
    hz, ite_true, ite_false, reduceCtorEq, movz_movk64', Option.some.injEq, exists_eq_left']
  have H := subtract_chain (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7)
  refine ⟨?_, ?_, True.intro, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  · dsimp only [addCarry, carryOut, Size.bits, scalarValue] at H ⊢
    exact H.1
  · dsimp only [addCarry, carryOut, Size.bits, scalarValue] at H ⊢
    exact H.2.trans (congrArg (fun c : Bool =>
      val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) + 2 ^ 256 * (1 - c.toNat)) H.1)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1,
      hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2, ite_false]

theorem carry_mask (c : Bool) : addCarry 0 (~~~0) c = mask (!c) := by
  cases c <;> decide

theorem scalarSelect_ok (s : State) (hz : s.gpr .x10 = 0) :
    WP isa (.block scalarSelect) s fun t =>
      scalarValue t = (if !s.c then savedValue s else scalarValue s) ∧
      Keeps [.x8, .x4, .x5, .x6, .x7, .x21, .x22, .x23, .x24] s t := by
  apply WP.of_runBlock
  simp only [scalarSelect, List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    scalarValue, savedValue, RegUpd.gpr_write, RegUpd.gpr_addWithCarry,
    BitVec.setWidth_eq, hz, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  have hm := carry_mask s.c
  dsimp only [addCarry] at hm
  simp only [hm, xor_sel']
  refine ⟨by cases s.c <;> rfl, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1,
    hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
    hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2, ite_false]

theorem select_remainder (x y : Nat) (hx : x < 2 * L)
    (he : y + L = x + 2 ^ 256 * (1 - (decide (L ≤ x)).toNat)) :
    (if L ≤ x then y else x) = x % L := by
  by_cases h : L ≤ x
  · simp only [h, decide_true, Bool.toNat_true, Nat.sub_self, Nat.mul_zero, Nat.add_zero] at he
    rw [ite_eq_left h, Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega_using [hx])]
    omega_using [he]
  · rw [ite_eq_right h, Nat.mod_eq_of_lt (by omega_using [h])]

end VG.Proof.Ed25519.AArch64

end

end

/-! ### `Ed25519.AArch64.ScalarWord`, which only this module used -/

section

/-!
# Ed25519 scalar reduction: one word on AArch64

`wordFold` turns the remainder `r < L` and the next word `w` into `l + L - h
c` for `2^64 r + w = h 2^252 + l`, with `L = 2^252 + c`: below `2L` and
congruent to `2^64 r + w` modulo `L` (`fold_nat`). Each of its blocks is
checked against the numbers it computes.
-/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 Word64
open VG.Spec.Ed25519 (L)

theorem c_limbs : orderLo.toNat + 2 ^ 64 * orderHi.toNat = cL := by decide

theorem orderHi_lt : orderHi.toNat < 2 ^ 61 := by decide

theorem foldPrep_ok (s : State) :
    WP isa (.block foldPrep) s fun t =>
      (t.gpr .x12).toNat = (s.gpr .x6).toNat / 2 ^ 60 + 16 * ((s.gpr .x7).toNat % 2 ^ 60) ∧
      (t.gpr .x13).toNat = (s.gpr .x7).toNat / 2 ^ 60 ∧
      t.gpr .x4 = s.gpr .x3 ∧ t.gpr .x5 = s.gpr .x4 ∧ t.gpr .x6 = s.gpr .x5 ∧
      (t.gpr .x7).toNat = (s.gpr .x6).toNat % 2 ^ 60 ∧
      Keeps [.x12, .x13, .x4, .x5, .x6, .x7] s t := by
  apply WP.of_runBlock
  simp only [foldPrep, mov, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show 60 < Size.x.bits from by decide, show 4 < Size.x.bits from by decide,
    show (0 : Nat) < 4096 from by decide,
    RegUpd.gpr_write, BitVec.setWidth_eq, BitVec.add_zero,
    ite_true, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨shr_or_shl _ _, shr60 _, trivial, trivial, trivial, shl_shr _, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2,
    ite_false]

theorem foldConst_ok (s : State) :
    WP isa (.block foldConst) s fun t =>
      t.gpr .x8 = orderLo ∧ t.gpr .x17 = orderHi ∧ Keeps [.x8, .x17] s t := by
  rw [foldConst, WP.block_append_iff]
  refine WP.mono (const64_ok s .x8 orderLo) fun a ⟨a8, ka⟩ => ?_
  refine WP.mono (const64_ok a .x17 orderHi) fun t ⟨t17, kt⟩ => ?_
  exact ⟨(kt.gpr .x8 (by decide)).trans a8, t17, (ka.mono (by decide)).trans (kt.mono (by decide))⟩

theorem umulh_toNat (a b : Word) :
    (BitVec.ofNat 64 (a.toNat * b.toNat / 2 ^ 64)).toNat = a.toNat * b.toNat / 2 ^ 64 := by
  have hp : a.toNat * b.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' a.isLt b.isLt
  rw [BitVec.toNat_ofNat]
  omega_arith

/-- `x (c₀ + 2^64 c₁)` from `mul`, `umulh` and one add with carry, for `c₁ < 2^61`. -/
theorem mul2_value (x c0 c1 : Word) (hc1 : c1.toNat < 2 ^ 61) :
    (x * c0).toNat +
        2 ^ 64 * (addCarry (BitVec.ofNat 64 (x.toNat * c0.toNat / 2 ^ 64)) (x * c1) false).toNat +
        2 ^ 128 * (addCarry (BitVec.ofNat 64 (x.toNat * c1.toNat / 2 ^ 64)) 0
          (carryOut (BitVec.ofNat 64 (x.toNat * c0.toNat / 2 ^ 64)) (x * c1) false)).toNat =
      x.toNat * c0.toNat + 2 ^ 64 * (x.toNat * c1.toNat) := by
  have hp1 : x.toNat * c1.toNat < 2 ^ 64 * 2 ^ 61 := Nat.mul_lt_mul'' x.isLt hc1
  have hA := umulh_toNat x c0
  have hC := umulh_toNat x c1
  have hB := BitVec.toNat_mul x c1
  have hD := BitVec.toNat_mul x c0
  have e1 := addCarry_value (BitVec.ofNat 64 (x.toNat * c0.toNat / 2 ^ 64)) (x * c1) false
  have e2 := addCarry_value (BitVec.ofNat 64 (x.toNat * c1.toNat / 2 ^ 64)) 0
    (carryOut (BitVec.ofNat 64 (x.toNat * c0.toNat / 2 ^ 64)) (x * c1) false)
  have hcy := Bool.toNat_le (carryOut (BitVec.ofNat 64 (x.toNat * c0.toNat / 2 ^ 64)) (x * c1) false)
  have hcy2 := Bool.toNat_le (carryOut (BitVec.ofNat 64 (x.toNat * c1.toNat / 2 ^ 64)) 0
    (carryOut (BitVec.ofNat 64 (x.toNat * c0.toNat / 2 ^ 64)) (x * c1) false))
  simp only [Bool.toNat_false, Nat.add_zero, show (0 : Word).toNat = 0 from rfl] at e1 e2
  omega_arith

/-- A two-word sum that cannot carry out of its top word. -/
theorem add2_value (a0 a1 b0 b1 : Word) (h : a1.toNat + b1.toNat + 1 < 2 ^ 64) :
    (addCarry a0 b0 false).toNat + 2 ^ 64 * (addCarry a1 b1 (carryOut a0 b0 false)).toNat =
      a0.toNat + 2 ^ 64 * a1.toNat + (b0.toNat + 2 ^ 64 * b1.toNat) := by
  have e1 := addCarry_value a0 b0 false
  have e2 := addCarry_value a1 b1 (carryOut a0 b0 false)
  have hcy := Bool.toNat_le (carryOut a0 b0 false)
  have hcy2 := Bool.toNat_le (carryOut a1 b1 (carryOut a0 b0 false))
  simp only [Bool.toNat_false, Nat.add_zero] at e1
  omega_arith

theorem foldMul_ok (s : State) (h8 : s.gpr .x8 = orderLo) (h17 : s.gpr .x17 = orderHi)
    (hz : s.gpr .x10 = 0) :
    WP isa (.block foldMul) s fun t =>
      (t.gpr .x14).toNat + 2 ^ 64 * (t.gpr .x15).toNat + 2 ^ 128 * (t.gpr .x16).toNat =
        (s.gpr .x12).toNat * cL ∧ Keeps [.x9, .x14, .x15, .x16] s t := by
  apply WP.of_runBlock
  simp only [foldMul, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
    BitVec.setWidth_eq, h8, h17, hz, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · have hc : (s.gpr .x12).toNat * cL =
        (s.gpr .x12).toNat * orderLo.toNat + 2 ^ 64 * ((s.gpr .x12).toNat * orderHi.toNat) := by
      rw [← c_limbs, Nat.mul_add, Nat.mul_left_comm]
    have H := mul2_value (s.gpr .x12) orderLo orderHi orderHi_lt
    dsimp only [addCarry, carryOut, Size.bits] at H ⊢
    rw [hc]
    exact H
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2,
      ite_false]

theorem mul_bit (h v : Word) (hh : h.toNat ≤ 1) : (h * v).toNat = h.toNat * v.toNat := by
  rw [BitVec.toNat_mul]
  rcases (by omega_arith : h.toNat = 0 ∨ h.toNat = 1) with e | e <;> rw [e]
  · rw [Nat.zero_mul, Nat.zero_mod]
  · rw [Nat.one_mul]; exact Nat.mod_eq_of_lt v.isLt

theorem foldHigh_ok (s : State) (h8 : s.gpr .x8 = orderLo) (h17 : s.gpr .x17 = orderHi)
    (h1 : (s.gpr .x13).toNat ≤ 1) (h16 : (s.gpr .x16).toNat < 2 ^ 62) :
    WP isa (.block foldHigh) s fun t => t.gpr .x14 = s.gpr .x14 ∧
      (t.gpr .x15).toNat + 2 ^ 64 * (t.gpr .x16).toNat =
        (s.gpr .x15).toNat + 2 ^ 64 * (s.gpr .x16).toNat + (s.gpr .x13).toNat * cL ∧
      Keeps [.x9, .x13, .x15, .x16] s t := by
  apply WP.of_runBlock
  simp only [foldHigh, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
    BitVec.setWidth_eq, h8, h17, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · have mx := mul_bit (s.gpr .x13) orderLo h1
    have my := mul_bit (s.gpr .x13) orderHi h1
    have hc : (s.gpr .x13).toNat * cL =
        (s.gpr .x13).toNat * orderLo.toNat + 2 ^ 64 * ((s.gpr .x13).toNat * orderHi.toNat) := by
      rw [← c_limbs, Nat.mul_add, Nat.mul_left_comm]
    have hy : (s.gpr .x13).toNat * orderHi.toNat < 2 ^ 61 := by
      have := orderHi_lt
      rcases (by omega_arith : (s.gpr .x13).toNat = 0 ∨ (s.gpr .x13).toNat = 1) with e | e <;>
        rw [e] <;> omega_arith
    have H := add2_value (s.gpr .x15) (s.gpr .x16) (s.gpr .x13 * orderLo) (s.gpr .x13 * orderHi)
      (by rw [my]; omega_arith)
    dsimp only [addCarry, carryOut, Size.bits] at H ⊢
    rw [H, mx, my, hc]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2,
      ite_false]

theorem orderTop_movz : (0x1000 : BitVec 16).setWidth 64 <<< (16 * 3) = orderTop := by decide

theorem foldSub_ok (s : State) (h8 : s.gpr .x8 = orderLo) (h17 : s.gpr .x17 = orderHi)
    (hz : s.gpr .x10 = 0)
    (ht : (s.gpr .x14).toNat + 2 ^ 64 * (s.gpr .x15).toNat + 2 ^ 128 * (s.gpr .x16).toNat < L) :
    WP isa (.block foldSub) s fun t =>
      val4 (t.gpr .x14) (t.gpr .x15) (t.gpr .x16) (t.gpr .x9) =
        L - ((s.gpr .x14).toNat + 2 ^ 64 * (s.gpr .x15).toNat + 2 ^ 128 * (s.gpr .x16).toNat) ∧
      Keeps [.x9, .x14, .x15, .x16] s t := by
  apply WP.of_runBlock
  simp only [foldSub, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show 16 * 3 < Size.x.bits from by decide,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_write, RegUpd.c_addWithCarry,
    BitVec.setWidth_eq, h8, h17, hz, orderTop_movz, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · have e := sub4_value orderLo orderHi 0 orderTop (s.gpr .x14) (s.gpr .x15) (s.gpr .x16) 0 true
    simp only [order_limbs, Bool.toNat_true, Nat.sub_self, Nat.add_zero] at e
    have hT : val4 (s.gpr .x14) (s.gpr .x15) (s.gpr .x16) 0 =
        (s.gpr .x14).toNat + 2 ^ 64 * (s.gpr .x15).toNat + 2 ^ 128 * (s.gpr .x16).toNat := by
      simp only [val4, show (0 : Word).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero]
    rw [hT] at e
    dsimp only [addCarry, carryOut, Size.bits] at e ⊢
    exact eq_sub_of_chain (val4_lt _ _ _ _) ht e
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2,
      ite_false]

theorem foldAdd_ok (s : State)
    (hs : scalarValue s + val4 (s.gpr .x14) (s.gpr .x15) (s.gpr .x16) (s.gpr .x9) < 2 ^ 256) :
    WP isa (.block foldAdd) s fun t =>
      scalarValue t = scalarValue s + val4 (s.gpr .x14) (s.gpr .x15) (s.gpr .x16) (s.gpr .x9) ∧
      Keeps [.x4, .x5, .x6, .x7] s t := by
  apply WP.of_runBlock
  simp only [foldAdd, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, BitVec.setWidth_eq,
    ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · have e := add4_value (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7)
      (s.gpr .x14) (s.gpr .x15) (s.gpr .x16) (s.gpr .x9) false
    simp only [Bool.toNat_false, Nat.add_zero] at e
    dsimp only [addCarry, carryOut, Size.bits, scalarValue] at e hs ⊢
    exact eq_of_chain hs e
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

/-- The registers `wordFold` changes. -/
def foldClob : List Reg := [.x4, .x5, .x6, .x7, .x8, .x9, .x12, .x13, .x14, .x15, .x16, .x17]

theorem wordFold_ok (s : State) (hr : scalarValue s < L) (hz : s.gpr .x10 = 0) :
    WP isa (.block wordFold) s fun t => scalarValue t < 2 * L ∧
      scalarValue t % L = (scalarValue s * 2 ^ 64 + (s.gpr .x3).toNat) % L ∧
      Keeps foldClob s t := by
  have hw := (s.gpr .x3).isLt
  obtain ⟨hlt, hlt2, hmod⟩ := fold_nat (scalarValue s) (s.gpr .x3).toNat hr hw
  have h0 := (s.gpr .x4).isLt; have h1 := (s.gpr .x5).isLt; have h2 := (s.gpr .x6).isLt
  have h3 : (s.gpr .x7).toNat < 2 ^ 61 := by
    have hL : L < 2 ^ 253 := by decide
    have := hr; simp only [scalarValue, val4] at this; omega_arith
  have eh : (scalarValue s * 2 ^ 64 + (s.gpr .x3).toNat) / 2 ^ 252 =
      ((s.gpr .x6).toNat / 2 ^ 60 + 16 * ((s.gpr .x7).toNat % 2 ^ 60)) +
        2 ^ 64 * ((s.gpr .x7).toNat / 2 ^ 60) := by
    simp only [scalarValue, val4]; omega_arith
  have el : (scalarValue s * 2 ^ 64 + (s.gpr .x3).toNat) % 2 ^ 252 =
      (s.gpr .x3).toNat + 2 ^ 64 * (s.gpr .x4).toNat + 2 ^ 128 * (s.gpr .x5).toNat +
        2 ^ 192 * ((s.gpr .x6).toNat % 2 ^ 60) := by
    simp only [scalarValue, val4]; omega_arith
  rw [eh] at hlt hlt2 hmod
  rw [el] at hlt2 hmod
  simp only [wordFold, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (foldPrep_ok s) fun a ⟨a12, a13, a4, a5, a6, a7, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (foldConst_ok a) fun b ⟨b8, b17, kb⟩ => ?_
  have hzb : b.gpr .x10 = 0 := by
    rw [kb.gpr .x10 (by decide), ka.gpr .x10 (by decide)]; exact hz
  rw [WP.block_append_iff]
  refine WP.mono (foldMul_ok b b8 b17 hzb) fun c ⟨ct, kc⟩ => ?_
  have c13 : c.gpr .x13 = a.gpr .x13 := by
    rw [kc.gpr .x13 (by decide), kb.gpr .x13 (by decide)]
  have c12 : c.gpr .x12 = a.gpr .x12 := by
    rw [kc.gpr .x12 (by decide), kb.gpr .x12 (by decide)]
  have hb1 : (c.gpr .x13).toNat ≤ 1 := by rw [c13, a13]; omega_arith
  have hb16 : (c.gpr .x16).toNat < 2 ^ 62 := by
    have : (b.gpr .x12).toNat * cL < 2 ^ 64 * cL :=
      Nat.mul_lt_mul_of_pos_right (b.gpr .x12).isLt (by decide)
    simp only [cL] at this ct; omega_arith
  rw [WP.block_append_iff]
  refine WP.mono (foldHigh_ok c ((kc.gpr .x8 (by decide)).trans b8)
    ((kc.gpr .x17 (by decide)).trans b17) hb1 hb16) fun d ⟨d14, dt, kd⟩ => ?_
  have hT : (d.gpr .x14).toNat + 2 ^ 64 * (d.gpr .x15).toNat + 2 ^ 128 * (d.gpr .x16).toNat =
      ((s.gpr .x6).toNat / 2 ^ 60 + 16 * ((s.gpr .x7).toNat % 2 ^ 60) +
        2 ^ 64 * ((s.gpr .x7).toNat / 2 ^ 60)) * cL := by
    have b12 : b.gpr .x12 = a.gpr .x12 := kb.gpr .x12 (by decide)
    rw [d14, Nat.add_mul, ← a12, ← a13, ← c13, ← b12, Nat.mul_assoc]
    omega_arith
  have d8 : d.gpr .x8 = orderLo := by
    rw [kd.gpr .x8 (by decide), kc.gpr .x8 (by decide)]; exact b8
  have d17 : d.gpr .x17 = orderHi := by
    rw [kd.gpr .x17 (by decide), kc.gpr .x17 (by decide)]; exact b17
  have dz : d.gpr .x10 = 0 := by
    rw [kd.gpr .x10 (by decide), kc.gpr .x10 (by decide)]; exact hzb
  rw [WP.block_append_iff]
  refine WP.mono (foldSub_ok d d8 d17 dz (by rw [hT]; exact hlt)) fun e ⟨eu, ke⟩ => ?_
  have hl : scalarValue e = (s.gpr .x3).toNat + 2 ^ 64 * (s.gpr .x4).toNat +
      2 ^ 128 * (s.gpr .x5).toNat + 2 ^ 192 * ((s.gpr .x6).toNat % 2 ^ 60) := by
    simp only [scalarValue, val4]
    rw [ke.gpr .x4 (by decide), ke.gpr .x5 (by decide), ke.gpr .x6 (by decide),
      ke.gpr .x7 (by decide), kd.gpr .x4 (by decide), kd.gpr .x5 (by decide),
      kd.gpr .x6 (by decide), kd.gpr .x7 (by decide), kc.gpr .x4 (by decide),
      kc.gpr .x5 (by decide), kc.gpr .x6 (by decide), kc.gpr .x7 (by decide),
      kb.gpr .x4 (by decide), kb.gpr .x5 (by decide), kb.gpr .x6 (by decide),
      kb.gpr .x7 (by decide), a4, a5, a6, a7]
  rw [hT] at eu
  refine WP.mono (foldAdd_ok e (by rw [hl, eu]; have := order_bound; omega_arith)) fun t ⟨tv, kt⟩ => ?_
  refine ⟨by rw [tv, hl, eu]; exact hlt2, by rw [tv, hl, eu]; exact hmod, ?_⟩
  exact ((((ka.mono (by decide)).trans (kb.mono (by decide))).trans
    ((kc.mono (by decide)).trans (kd.mono (by decide)))).trans (ke.mono (by decide))).trans
    (kt.mono (by decide))

end VG.Proof.Ed25519.AArch64

end

end


/-! Merged from `Proof.Ed25519.AArch64.ScalarLoop`. -/

@[expose] public section

section
/-!
# Scalar reduction: the eight-word loop

The invariant is the value modulo L of the already consumed top words of the
little-endian input. The body writes no memory.
-/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64
open VG.Spec.Ed25519 (L bytesAt decodeLE)

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by
  simp only [bytesAt, List.length_map, List.length_range]

def wordRead : List Instr :=
  [.subImm .x .x19 .x19 8, .add .x .x9 .x1 .x19, .ldr .x .x3 .x9 0]

theorem wordRead_ok (s : State) (k : Nat) (hb : s.gpr .x19 = BitVec.ofNat 64 (8 * (k + 1)))
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 (8 * k)) 8) :
    WP isa (.block wordRead) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 (8 * k) ∧
      t.gpr .x3 = s.mem.readW (s.gpr .x1 + BitVec.ofNat 64 (8 * k)) 64 ∧
      Keeps [.x19, .x9, .x3] s t := by
  have hn : s.gpr .x19 - BitVec.ofNat 64 8 = BitVec.ofNat 64 (8 * k) := by
    rw [hb, show 8 * (k + 1) = 8 * k + 8 by omega_using [], BitVec.ofNat_add, BitVec.add_sub_cancel]
  apply WP.of_runBlock
  simp only [wordRead, runBlock_cons, runStep_some, runBlock_nil, exec, read_x, addr, State.load,
    Size.bytes, show (8 : Nat) < 4096 from by decide, show (0 : Nat) % 8 = 0 from rfl,
    show (0 : Nat) < 4096 * 8 from by decide, and_self,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    hn, BitVec.add_zero, BitVec.setWidth_eq, hr,
    ite_true, ite_false, reduceCtorEq, Option.bind_some, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, rfl, ⟨fun r h => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  simp only [RegUpd.gpr_write, h.1, h.2.1, h.2.2, ite_false]

/-- The registers the loop changes. -/
def scalarBodyClob : List Reg :=
  [.x19, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x12, .x13, .x14, .x15, .x16, .x17,
    .x21, .x22, .x23, .x24]

theorem scalarWord_ok (s : State) (k : Nat)
    (hb : s.gpr .x19 = BitVec.ofNat 64 (8 * (k + 1)))
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 (8 * k)) 8)
    (hv : scalarValue s < L) (hz : s.gpr .x10 = 0) :
    WP isa (.block scalarWord) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 (8 * k) ∧
      scalarValue t = (scalarValue s * 2 ^ 64 +
        (s.mem.readW (s.gpr .x1 + BitVec.ofNat 64 (8 * k)) 64).toNat) % L ∧
      Keeps scalarBodyClob s t := by
  rw [show scalarWord = wordRead ++ (wordFold ++ (scalarSubtract ++ scalarSelect)) by
    simp only [scalarWord, wordRead, List.append_assoc, List.cons_append, List.nil_append],
    WP.block_append_iff]
  refine WP.mono (wordRead_ok s k hb hr) fun a ⟨ab, ax, ka⟩ => ?_
  have av : scalarValue a = scalarValue s := by
    simp only [scalarValue, ka.gpr .x4 (by decide), ka.gpr .x5 (by decide),
      ka.gpr .x6 (by decide), ka.gpr .x7 (by decide)]
  have az : a.gpr .x10 = 0 := (ka.gpr .x10 (by decide)).trans hz
  rw [WP.block_append_iff]
  refine WP.mono (wordFold_ok a (av ▸ hv) az) fun b ⟨b2, bm, kb⟩ => ?_
  have bz : b.gpr .x10 = 0 := (kb.gpr .x10 (by decide)).trans az
  rw [WP.block_append_iff]
  refine WP.mono (scalarSubtract_ok b bz) fun c ⟨cc, cu, csaved, kc⟩ => ?_
  have cz : c.gpr .x10 = 0 := (kc.gpr .x10 (by decide)).trans bz
  refine WP.mono (scalarSelect_ok c cz) fun t ⟨tv, kt⟩ => ?_
  have he := select_remainder (scalarValue b) (scalarValue c) b2 cu
  refine ⟨?_, ?_, (((ka.mono (by decide)).trans (kb.mono (by decide))).trans
    (kc.mono (by decide))).trans (kt.mono (by decide))⟩
  · rw [kt.gpr .x19 (by decide), kc.gpr .x19 (by decide), kb.gpr .x19 (by decide)]
    exact ab
  · rw [cc, csaved] at tv
    have hs : scalarValue t = if L ≤ scalarValue b then scalarValue c else scalarValue b := by
      by_cases h : L ≤ scalarValue b <;> simpa only [h, decide_true, decide_false,
        Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_false, ite_true] using tv
    rw [hs, he, bm, av, ax]

theorem scalar_counter_test : ∀ n < 8,
    (BitVec.ofNat 64 (8 * n) != 0) = decide (n ≠ 0) := by decide

structure ScalarInv (s₀ : State) (n : Nat) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ 8
  counter : s.gpr .x19 = BitVec.ofNat 64 (8 * n)
  value : scalarValue s =
    decodeLE (bytesAt s₀.mem (s₀.gpr .x1 + BitVec.ofNat 64 (8 * n)) (64 - 8 * n)) % L
  keeps : Keeps scalarBodyClob s₀ s

theorem scalarLoop_ok (s₀ : State) (hb : s₀.gpr .x19 = 64) (hz : scalarValue s₀ = 0)
    (hr : ∀ k < 8, InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x1 + BitVec.ofNat 64 (8 * k)) 8)
    (hz0 : s₀.gpr .x10 = 0) :
    WP isa (.loop (.block scalarWord) (.nonzero .x .x19)) s₀ fun t =>
      scalarValue t = decodeLE (bytesAt s₀.mem (s₀.gpr .x1) 64) % L ∧
      Keeps scalarBodyClob s₀ t := by
  apply WP.loop (ScalarInv s₀) (n := 8)
  · intro n s hi
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := hi.positive; omega_using [this] : n ≠ 0)
    have hk : k < 8 := by have := hi.bound; omega_using [this]
    have hp : s.gpr .x1 = s₀.gpr .x1 := hi.keeps.gpr .x1 (by decide)
    have hread : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 (8 * k)) 8 := by
      rw [hi.keeps.rd, hi.keeps.wr, hp]; exact hr k hk
    have hv : scalarValue s < L := by rw [hi.value]; exact Nat.mod_lt _ order_pos
    have hzs := (hi.keeps.gpr .x10 (by decide)).trans hz0
    refine WP.mono (scalarWord_ok s k hi.counter hread hv hzs) fun t ⟨htb, htv, htk⟩ => ?_
    have kt := hi.keeps.trans htk
    have vt : scalarValue t =
        decodeLE (bytesAt s₀.mem (s₀.gpr .x1 + BitVec.ofNat 64 (8 * k)) (64 - 8 * k)) % L := by
      rw [htv, hi.value, hp, hi.keeps.mem, words_step _ _ k hk, Nat.succ_eq_add_one, mod_step]
    by_cases hk0 : k = 0
    · subst hk0
      refine Or.inl ⟨by simp only [eval, read_x, htb, scalar_counter_test 0 (by decide),
        show decide ((0 : Nat) ≠ 0) = false from rfl], ?_, kt⟩
      simpa only [Nat.mul_zero, BitVec.add_zero, Nat.sub_zero] using vt
    · exact Or.inr ⟨by simp only [eval, read_x, htb, scalar_counter_test k hk, decide_eq_true hk0],
        k, by omega_using [], ⟨by omega_using [hk0], by omega_using [hk], htb, vt, kt⟩⟩
  · refine ⟨by decide, by decide, hb, ?_, ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩⟩
    rw [hz]
    rfl

end VG.Proof.Ed25519.AArch64
end

/-! Scalar reducer saves, restores, and output stores. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64

/-- The six used callee-saved registers occupy scratch bytes 0–47. -/
def Saved (base : Addr) (g : Reg → BitVec 64) (m : Mem) : Prop :=
  ∀ rd ∈ saved, word m base rd.2 = g rd.1

theorem scalarSave_ok {s : State} {base : Addr} (hc : s.gpr .x2 = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block scalarSave) s fun t =>
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      Outside base 0 48 s.mem t.mem ∧ Saved base s.gpr t.mem := by
  have w : ∀ d, d + 8 ≤ 8192 → InRegions s.wr (off base d) 8 :=
    fun d hd => ⟨_, hw, contains_sc hd⟩
  apply WP.of_runBlock
  simp only [scalarSave, saved, List.map_cons, List.map_nil, runBlock_cons, runStep_some, runBlock_nil,
    exec, addr, Size.bytes, State.store, read_x, hc, BitVec.setWidth_eq,
    Nat.reduceMod, Nat.reduceMul, Nat.reduceLT, and_self, ite_true,
    w 0 (by omega_using []), w 8 (by omega_using []), w 16 (by omega_using []), w 24 (by omega_using []), w 32 (by omega_using []), w 40 (by omega_using []),
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨True.intro, True.intro, True.intro, True.intro, ?_, fun rd hrd => ?_⟩
  · exact ((((((Outside.refl base 0 48 s.mem).writeW (by decide) (by decide) (by decide) _).writeW
      (by decide) (by decide) (by decide) _).writeW (by decide) (by decide) (by decide) _).writeW
      (by decide) (by decide) (by decide) _).writeW (by decide) (by decide) (by decide) _).writeW
      (by decide) (by decide) (by decide) _
  · change word _ base rd.2 = s.gpr rd.1
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hrd
    simp only [write64_eq_writeW]
    rcases hrd with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (disch := decide) only [word_writeW_sep, word_writeW_self]

theorem scalarRestore_ok {s : State} {base : Addr} (hb : s.gpr .x2 = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) {g : Reg → BitVec 64} (hsv : Saved base g s.mem) :
    WP isa (.block scalarRestore) s fun t =>
      (∀ rd ∈ saved, t.gpr rd.1 = g rd.1) ∧ Keeps [.x19, .x20, .x21, .x22, .x23, .x24] s t := by
  have hr : ∀ d, d + 8 ≤ 8192 → InRegions (s.rd ++ s.wr) (off base d) 8 :=
    fun d hd => ⟨_, List.mem_append_right _ hw, contains_sc hd⟩
  apply WP.of_runBlock
  simp only [scalarRestore, saved, List.map_cons, List.map_nil, runBlock_cons, runStep_some, runBlock_nil,
    exec, addr, Size.bytes, State.load, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write,
    RegUpd.wr_write, hb, BitVec.setWidth_eq, Nat.reduceMod, Nat.reduceMul, Nat.reduceLT, and_self,
    hr 0 (by omega_using []), hr 8 (by omega_using []), hr 16 (by omega_using []), hr 24 (by omega_using []), hr 32 (by omega_using []), hr 40 (by omega_using []),
    ite_true, ite_false, reduceCtorEq, Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun rd hrd => ?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  · have e := hsv rd hrd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hrd
    rcases hrd with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simpa only [RegUpd.gpr_write, ite_true, ite_false, reduceCtorEq, word, Mem.readW,
        BitVec.setWidth_eq] using e
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false]

theorem scalarOut_ok {s : State} {q : Addr} (hq : s.gpr .x0 = q) (hw : (⟨q, 32⟩ : Region) ∈ s.wr) :
    WP isa (.block [.str .x .x4 .x0 0, .str .x .x5 .x0 8, .str .x .x6 .x0 16, .str .x .x7 .x0 24]) s
      fun t => t = { s with mem := st4 s.mem q 0 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) } := by
  have w : ∀ d, d + 8 ≤ 32 → InRegions s.wr (off q d) 8 :=
    fun d hd => ⟨_, hw, Offset.contains_base q hd (by omega_using [hd])⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes, State.store, read_x,
    hq, BitVec.setWidth_eq, Nat.reduceMod, Nat.reduceMul, Nat.reduceLT, and_self, ite_true,
    w 0 (by omega_using []), w 8 (by omega_using []), w 16 (by omega_using []), w 24 (by omega_using []),
    Option.bind_some, Option.some.injEq, exists_eq_left']
  rfl

theorem scalarInit_ok (s : State) :
    WP isa (.block scalarInit) s fun t =>
      t.gpr .x19 = 64 ∧ scalarValue t = 0 ∧ t.gpr .x10 = 0 ∧
      Keeps [.x4, .x5, .x6, .x7, .x10, .x19] s t := by
  apply WP.of_runBlock
  simp only [scalarInit, zero4, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, show 16 * 0 < Size.w.bits from by decide,
    scalarValue, RegUpd.gpr_write, ite_true, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
    hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false]

end VG.Proof.Ed25519.AArch64
