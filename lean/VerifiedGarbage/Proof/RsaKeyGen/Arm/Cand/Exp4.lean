module
public import VerifiedGarbage.Impl.RsaKeyGen.Arm.Candidate
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Rsa.RecoverExp
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Bignum.Arm.MontMath
import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.Rsa.Arm.KeyWs
import VerifiedGarbage.Proof.Rsa.Arm.RvVP
import VerifiedGarbage.Spec.RsaKeyGen


/-! # A candidate on ARMv7: the masks of the shift and the word `2^(t mod 64)`

From `t` (header word `sTc`): the masks of `σ > 1`, `σ > 2` and `σ > 3` for
the shift `σ` (`sgv`), and the halves of `2^(t mod 64)` (`pw`), computed
under masks, as functions of `t` (`sg_val`, `pw_val`, checked for every
`t mod 64`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Cand
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.Rsa (b2n)

/-! ## The values -/

/-- `powStep j`: `y << 2^j` if bit `j` of `x` is set. -/
def pstep (j : Nat) (x y : BitVec 32) : BitVec 32 := y ^^^ (((y <<< (2 ^ j)) ^^^ y) &&& (0 - ((x >>> j) &&& 1)))

/-- The halves of `2^(x mod 64)`, as `powWord` computes them. -/
def pw (x : BitVec 32) : BitVec 32 × BitVec 32 :=
  let x6 := x &&& 63
  let y := pstep 4 x6 (pstep 3 x6 (pstep 2 x6 (pstep 1 x6 (pstep 0 x6 1))))
  let hi := y &&& (0 - ((x6 >>> 5) &&& 1))
  (y ^^^ hi, hi)

/-- The masks of `σ > 1`, `σ > 2` and `σ > 3`, as `sigMasks` computes them. -/
def sg (x : BitVec 32) : BitVec 32 × BitVec 32 × BitVec 32 :=
  let x3 := x &&& 3
  let z := (x3 - 1) >>> 31
  ((((x3 ^^^ 1) - 1) >>> 31) ^^^ 1, (((x3 ^^^ 3) - 1) >>> 31) ||| z, z)

theorem and_mask {t k : Nat} (hk : k < 32) :
    BitVec.ofNat 32 t &&& BitVec.ofNat 32 (2 ^ k - 1) = BitVec.ofNat 32 (t % 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  have : 2 ^ k ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) (by omega)
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 2 ^ k - 1) (by omega),
    Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega)),
    Nat.mod_eq_of_lt (a := t % 2 ^ k) (by have := Nat.mod_lt t (Nat.two_pow_pos k); omega)]

theorem pw_small : ∀ t < 64, (pw (BitVec.ofNat 32 t)).1.toNat + 2 ^ 32 * (pw (BitVec.ofNat 32 t)).2.toNat = 2 ^ t := by
  decide

theorem pw_mod (t : Nat) : pw (BitVec.ofNat 32 t) = pw (BitVec.ofNat 32 (t % 64)) := by
  have e : ∀ x : Nat, BitVec.ofNat 32 x &&& 63 = BitVec.ofNat 32 (x % 64) := fun x => and_mask (k := 6) (by decide)
  unfold pw
  simp only [e, Nat.mod_mod]

/-- The 64-bit word of the halves is `2^(t mod 64)`. -/
theorem pw_val (t : Nat) :
    (pw (BitVec.ofNat 32 t)).1.toNat + 2 ^ 32 * (pw (BitVec.ofNat 32 t)).2.toNat = 2 ^ (t % 64) := by
  rw [pw_mod]; exact pw_small _ (Nat.mod_lt _ (by decide))

theorem sg_small : ∀ t < 4, (sg (BitVec.ofNat 32 t)).1.toNat = b2n (decide (t ≠ 1)) ∧
    (sg (BitVec.ofNat 32 t)).2.1.toNat = b2n (decide (t = 3 ∨ t = 0)) ∧
    (sg (BitVec.ofNat 32 t)).2.2.toNat = b2n (decide (t = 0)) := by
  decide

theorem sg_mod (t : Nat) : sg (BitVec.ofNat 32 t) = sg (BitVec.ofNat 32 (t % 4)) := by
  have e : ∀ x : Nat, BitVec.ofNat 32 x &&& 3 = BitVec.ofNat 32 (x % 4) := fun x => and_mask (k := 2) (by decide)
  unfold sg
  simp only [e, Nat.mod_mod]

theorem sg_val (t : Nat) : (sg (BitVec.ofNat 32 t)).1.toNat = b2n (decide (t % 4 ≠ 1)) ∧
    (sg (BitVec.ofNat 32 t)).2.1.toNat = b2n (decide (t % 4 = 3 ∨ t % 4 = 0)) ∧
    (sg (BitVec.ofNat 32 t)).2.2.toNat = b2n (decide (t % 4 = 0)) := by
  rw [sg_mod]; exact sg_small _ (Nat.mod_lt _ (by decide))

/-! ## The code -/

theorem powStep_ok {j : Nat} (hj : j < 5) {u : State} {x y : BitVec 32} (r1 : u.gpr .r1 = x) (r2 : u.gpr .r2 = y)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ u', Rest [.r2, .r3, .r4] u u' → u'.mem = u.mem → u'.gpr .r1 = x → u'.gpr .r2 = pstep j x y →
      WP isa (.block rest) u' Q) :
    WP isa (.block (powStep j ++ rest)) u Q := by
  have h2j : 1 ≤ 2 ^ j ∧ 2 ^ j ≤ 31 := by
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl <;> decide
  -- The bit of `x` into `r3`.
  have hb : ∀ {rest' : List Instr} {Q' : State → Prop}, (∀ u', Rest [.r3] u u' → u'.mem = u.mem →
      u'.gpr .r3 = (x >>> j) &&& 1 → WP isa (.block rest') u' Q') →
      WP isa (.block ((if j = 0 then [.dp .and .r3 .r1 (.imm 1)] else
        [.mov .r3 (.shifted .r1 .lsr j), .dp .and .r3 .r3 (.imm 1)]) ++ rest')) u Q' := by
    intro rest' Q' k'
    by_cases h0 : j = 0
    · subst h0
      simp only [↓reduceIte, List.cons_append, List.nil_append]
      exact wp_dp (op2_imm (by decide)) fun u1 v1 => k' u1 (v1.rest (by simp)) v1.mem (by
        rw [v1.gpr, dpVal, r1, BitVec.ushiftRight_zero])
    · simp only [h0, ↓reduceIte, List.cons_append, List.nil_append]
      exact wp_mov (op2_lsr (by omega)) fun u1 v1 => wp_dp (op2_imm (by decide)) fun u2 v2 =>
        k' u2 ((v1.rest (by simp)).trans (v2.rest (by simp))) (by rw [v2.mem, v1.mem]) (by
          rw [v2.gpr, dpVal, v1.gpr, r1])
  unfold powStep
  rw [List.append_assoc]
  refine hb fun u1 k1 m1 b1 => ?_
  simp only [List.cons_append, List.nil_append]
  refine wp_mov (op2_imm (by decide)) fun u2 v2 => wp_dp (op2_reg _ _) fun u3 v3 =>
    wp_mov (op2_lsl h2j) fun u4 v4 => wp_dp (op2_reg _ _) fun u5 v5 => wp_dp (op2_reg _ _) fun u6 v6 =>
      wp_dp (op2_reg _ _) fun u7 v7 => ?_
  have k7 : Rest [.r2, .r3, .r4] u u7 := (k1.mono (by simp)).trans ((v2.rest (by simp)).trans ((v3.rest (by simp)).trans
    ((v4.rest (by simp)).trans ((v5.rest (by simp)).trans ((v6.rest (by simp)).trans (v7.rest (by simp)))))))
  have y1 : u1.gpr .r2 = y := by rw [k1.gpr _ (by decide), r2]
  refine k u7 k7 (by rw [v7.mem, v6.mem, v5.mem, v4.mem, v3.mem, v2.mem, m1]) (by rw [k7.gpr _ (by decide), r1]) ?_
  have e3 : u3.gpr .r3 = 0 - ((x >>> j) &&& 1) := by
    rw [v3.gpr, dpVal, v2.gpr, v2.other _ (by decide), b1]
  have e4 : u4.gpr .r4 = y <<< (2 ^ j) := by rw [v4.gpr, v3.other _ (by decide), v2.other _ (by decide), y1]
  have e5 : u5.gpr .r4 = (y <<< (2 ^ j)) ^^^ y := by
    rw [v5.gpr, dpVal, e4, v4.other _ (by decide), v3.other _ (by decide), v2.other _ (by decide), y1]
  have e6 : u6.gpr .r4 = ((y <<< (2 ^ j)) ^^^ y) &&& (0 - ((x >>> j) &&& 1)) := by
    rw [v6.gpr, dpVal, e5, v5.other _ (by decide), v4.other _ (by decide), e3]
  rw [v7.gpr, dpVal, e6, v6.other _ (by decide), v5.other _ (by decide), v4.other _ (by decide),
    v3.other _ (by decide), v2.other _ (by decide), y1]
  rfl

end VG.Proof.RsaKeyGen.Arm.Cand
