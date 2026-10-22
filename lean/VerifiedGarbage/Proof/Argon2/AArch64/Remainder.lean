module

public import VerifiedGarbage.Impl.Argon2.AArch64.Remainder
public import VerifiedGarbage.Proof.Argon2.AArch64.DivideStep
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Argon2.AArch64.Divide
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.RelCT
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.RelCT
meta import VerifiedGarbage.Impl.Argon2.AArch64.Remainder
meta import VerifiedGarbage.Proof.Argon2.AArch64.DivideStep
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Argon2.AArch64.Divide
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-! # The fixed-time remainder for ARM64 reference lanes -/

@[expose] public section

namespace VG
materialize_code Impl.Argon2.AArch64.Remainder.code
end VG

namespace VG.Proof.Argon2.AArch64.Remainder

open VG VG.AArch64 VG.Impl.Argon2.AArch64.Remainder
open VG.Proof.Argon2.AArch64.Divide (Keeps)

def changed : List Reg := [.x0, .x4, .x9]

theorem extr_value (a x : BitVec 64) (ha : a.toNat < 2 ^ 32) :
    ((a ++ x).extractLsb' 63 64).toNat = 2 * a.toNat + x.toNat / 2 ^ 63 := by
  have hx := x.isLt
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt hx,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  simp only [Nat.reducePow] at *
  omega

theorem reduce_value (e l : BitVec 64) (hl : l.toNat < 2 ^ 32) (he : e.toNat < 2 * l.toNat) :
    (if decide (2 ^ 64 ≤ e.toNat + (~~~l).toNat + (true).toNat) = true
      then e + ~~~l + BitVec.ofNat 64 (true).toNat else e).toNat = e.toNat % l.toNat := by
  have hn := BitVec.toNat_not (x := l)
  simp only [Bool.toNat_true, decide_eq_true_eq, Nat.reducePow] at *
  split
  · have hle : l.toNat ≤ e.toNat := by omega
    have hm : e.toNat % l.toNat = e.toNat - l.toNat := by
      rw [Nat.mod_eq_sub_mod hle, Nat.mod_eq_of_lt (by omega : e.toNat - l.toNat < l.toNat)]
    rw [BitVec.toNat_add, BitVec.toNat_add, hn, BitVec.toNat_ofNat, hm]
    omega
  · rw [Nat.mod_eq_of_lt (by omega)]

theorem step_ok (s : State) (ha : (s.gpr .x4).toNat < (s.gpr .x1).toNat)
    (hl : (s.gpr .x1).toNat < 2 ^ 32) :
    WP isa (.block step) s fun t =>
      (t.gpr .x4).toNat = (2 * (s.gpr .x4).toNat + (s.gpr .x0).toNat / 2 ^ 63) %
        (s.gpr .x1).toNat ∧
      t.gpr .x0 = s.gpr .x0 <<< 1 ∧ t.gpr .x1 = s.gpr .x1 ∧ Keeps changed s t := by
  have he := extr_value (s.gpr .x4) (s.gpr .x0) (by omega)
  apply WP.of_runBlock
  simp only [step, runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    show 63 < 64 from by decide, show 1 < 64 from by decide, ite_true, CondCode.holds,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, BitVec.setWidth_eq,
    reduceCtorEq, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨?_, trivial, trivial, ?_⟩
  · have hr := reduce_value _ _ hl (by rw [he]; have := (s.gpr .x0).isLt; omega)
    rw [hr, he]
  · constructor
    · intro r hr
      simp only [changed, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2, ite_false]
    all_goals rfl

/-- After `k` steps, x0 holds the unconsumed bits at the top and x4 the
remainder of the consumed ones. -/
structure Invariant (n l : BitVec 64) (k : Nat) (s : State) : Prop where
  numerator : s.gpr .x0 = n <<< (32 + k)
  divisor : s.gpr .x1 = l
  remainder : (s.gpr .x4).toNat = n.toNat / 2 ^ (32 - k) % l.toNat

theorem next_bit (n : BitVec 64) (k : Nat) (hk : k < 32) :
    n.toNat / 2 ^ (32 - (k + 1)) =
      2 * (n.toNat / 2 ^ (32 - k)) + (n <<< (32 + k)).toNat / 2 ^ 63 := by
  have hj : 32 - k = (32 - (k + 1)) + 1 := by omega
  rw [hj, Divide.prefix_step n (32 - (k + 1))]
  congr 1
  have hlt := (n <<< (32 + k)).isLt
  have hbit : (n <<< (32 + k)).toNat / 2 ^ 63 = ((n <<< (32 + k)).getLsbD 63).toNat := by
    rw [← BitVec.testBit_toNat, Nat.testBit_eq_decide_div_mod_eq]
    generalize (n <<< (32 + k)).toNat = v at hlt ⊢
    have : v / 2 ^ 63 < 2 := by
      rw [Nat.div_lt_iff_lt_mul (by decide)]; simpa using hlt
    rcases (by omega : v / 2 ^ 63 = 0 ∨ v / 2 ^ 63 = 1) with h | h <;> rw [h] <;> rfl
  rw [hbit, BitVec.getLsbD_shiftLeft]
  simp only [show (63 : Nat) < 64 from by decide, decide_true, Bool.true_and,
    show ¬ (63 < 32 + k) from by omega, decide_false, Bool.not_false,
    show 63 - (32 + k) = 32 - (k + 1) from by omega]

theorem steps_ok (n l : BitVec 64) (hl0 : 0 < l.toNat)
    (hl : l.toNat < 2 ^ 32) (k m : Nat) (hkm : k + m = 32) (s : State)
    (h : Invariant n l k s) :
    WP isa (.block (steps m)) s fun t => Invariant n l 32 t ∧ Keeps changed s t := by
  induction m generalizing k s with
  | zero =>
    rw [show k = 32 by omega] at h
    exact WP.block_nil ⟨h, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | succ m ih =>
    rw [steps, List.replicate_succ, List.flatten_cons, WP.block_append_iff]
    have ha : (s.gpr .x4).toNat < (s.gpr .x1).toNat := by
      rw [h.remainder, h.divisor]; exact Nat.mod_lt _ hl0
    refine (step_ok s ha (by rw [h.divisor]; exact hl)).mono ?_
    rintro t ⟨h4, h0, h1, kt⟩
    have ht : Invariant n l (k + 1) t := by
      refine ⟨?_, h1.trans h.divisor, ?_⟩
      · rw [h0, h.numerator, ← BitVec.shiftLeft_add, Nat.add_assoc]
      · rw [h4, h.remainder, h.divisor, h.numerator, next_bit n k (by omega),
          Nat.add_mod (2 * (_ % _)), Nat.add_mod (2 * _), Nat.mul_mod 2 (_ % _),
          Nat.mul_mod 2 (_ / _), Nat.mod_mod]
    refine (ih (k + 1) (by omega) t ht).mono ?_
    rintro u ⟨hu, ku⟩
    exact ⟨hu, kt.trans ku⟩

theorem setup_ok (s : State) (hn : (s.gpr .x0).toNat < 2 ^ 32) :
    WP isa (.block setup) s fun t =>
      Invariant (s.gpr .x0) (s.gpr .x1) 0 t ∧ Keeps changed s t := by
  apply WP.of_runBlock
  simp only [setup, runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    Nat.reduceMul, Nat.reduceLT, show 32 < 64 from by decide, ite_true,
    BitVec.shiftLeft_zero, RegUpd.gpr_write, BitVec.setWidth_eq, reduceCtorEq, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨⟨rfl, rfl, ?_⟩, ?_⟩
  · rw [Nat.div_eq_of_lt hn, Nat.zero_mod]
    rfl
  · constructor
    · intro r hr
      simp only [changed, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_write, hr.1, hr.2.1, ite_false]
    all_goals rfl

theorem code_ok (s : State) (hn : (s.gpr .x0).toNat < 2 ^ 32)
    (hd : 0 < (s.gpr .x1).toNat) (hd' : (s.gpr .x1).toNat < 2 ^ 32) :
    WP isa code s fun t =>
      (t.gpr .x4).toNat = (s.gpr .x0).toNat % (s.gpr .x1).toNat ∧ Keeps changed s t := by
  rw [code, WP.block_append_iff]
  refine (setup_ok s hn).mono ?_
  rintro u ⟨hu, ku⟩
  refine (steps_ok _ _ hd hd' 0 32 rfl u hu).mono ?_
  rintro t ⟨ht, kt⟩
  refine ⟨?_, ku.trans kt⟩
  rw [ht.remainder, Nat.sub_self, Nat.pow_zero, Nat.div_one]

/-- A secret numerator and divisor do not affect the trace. -/
theorem code_secret_rel : RelCT isa (fun s t => s.sp = t.sp) code (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [])
    (fun _ _ h => ⟨h, by simp [Taint.mem_ofRegs]⟩) [] (by taint_decide)).mono
    (fun _ _ h => h) (fun _ _ h => h.1)

end VG.Proof.Argon2.AArch64.Remainder
