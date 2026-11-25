module

public import VerifiedGarbage.Impl.Mont.AArch64.P256Square
public import VerifiedGarbage.Proof.Mont.AArch64.Ops
import VerifiedGarbage.Proof.Mont.AArch64.Chain
import VerifiedGarbage.Proof.Mont.AArch64.Csub
import VerifiedGarbage.Proof.Ed25519.Word64
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The P-256 square on AArch64

`core_ok`: the square `[a]² R⁻¹` below `2p`; `square_ok`: reduced below `p`.
The products are atoms of linear facts about the carry chains, and so are the
halves of the words of `q`, which the shifted sums are linear in.
-/

@[expose] public section

namespace VG.Proof.Mont.AArch64.P256Square

open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Mont.AArch64.P256Square
open VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

/-- The prime. -/
def p : Nat := 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff

/-- The radix. -/
def R : Nat := 2 ^ 256

theorem supported_mod {M : Mod} {m : Nat} (h : supported M = true) (hm : M.ok m = true) :
    M.n = 4 ∧ m = p := by
  simp only [supported, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain hr := M.ok_red hm
  rw [h.2, h.1, show Red.ofModulus 4 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff =
    .friendly [.pow2 32, .zero, .gen 0xffffffff00000001, .zero] by decide +kernel] at hr
  simp only [Red.ok, Bool.and_eq_true, beq_iff_eq] at hr
  have hd := hr.1.2
  have hl := hr.1.1.2
  change 2 ^ 32 + 2 ^ 64 * (0 + 2 ^ 64 * (0xffffffff00000001 + 2 ^ 64 * (0 + 2 ^ 64 * 0))) =
    (m + 1) / 2 ^ 64 at hd
  refine ⟨h.1, ?_⟩
  unfold p
  omega_using [hd, hl]

/-! ## Words -/

section
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64

/-- `adcs` along two lists of words. -/
private def addL : List (BitVec 64) → List (BitVec 64) → Bool → List (BitVec 64)
  | x :: xs, y :: ys, k => addCarry x y k :: addL xs ys (carryOut x y k)
  | _, _, _ => []

/-- The carry of `addL`. -/
private def outL : List (BitVec 64) → List (BitVec 64) → Bool → Bool
  | x :: xs, y :: ys, k => outL xs ys (carryOut x y k)
  | _, _, k => k

private def valL : List (BitVec 64) → Nat
  | [] => 0
  | x :: xs => x.toNat + 2 ^ 64 * valL xs

private theorem addL_value : ∀ (xs ys : List (BitVec 64)) (k : Bool), xs.length = ys.length →
    valL (addL xs ys k) + 2 ^ (64 * xs.length) * (outL xs ys k).toNat = valL xs + valL ys + k.toNat
  | [], [], k, _ => by simp [valL, addL, outL]
  | x :: xs, y :: ys, k, h => by
    have ih := addL_value xs ys (carryOut x y k) (by simpa using h)
    have e := addCarry_value x y k
    simp only [valL, addL, outL, List.length_cons, pow64_succ, Nat.mul_assoc]
    generalize 2 ^ (64 * xs.length) * (outL xs ys (carryOut x y k)).toNat = w at *
    omega_using [ih, e]

private theorem addL_mod (xs ys : List (BitVec 64)) (k : Bool) (h : xs.length = ys.length) :
    valL (addL xs ys k) = (valL xs + valL ys + k.toNat) % 2 ^ (64 * xs.length) := by
  have e := addL_value xs ys k h
  have l : ∀ zs : List (BitVec 64), valL zs < 2 ^ (64 * zs.length) := by
    intro zs
    induction zs with
    | nil => simp [valL]
    | cons z zs ih =>
      rw [valL, List.length_cons, pow64_succ]
      exact word_add_lt z.isLt ih
  have ll : ∀ (xs ys : List (BitVec 64)) (k : Bool), xs.length = ys.length →
      (addL xs ys k).length = xs.length := by
    intro xs
    induction xs with
    | nil => intro ys k h; cases ys <;> simp [addL]
    | cons x xs ih =>
      intro ys k h
      cases ys with
      | nil => simp at h
      | cons y ys => simp only [addL, List.length_cons, ih ys _ (by simpa using h)]
  have lt := l (addL xs ys k)
  rw [ll xs ys k h] at lt
  rw [← e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt lt]

private theorem valL_not : ∀ xs : List (BitVec 64),
    valL (xs.map (~~~·)) + valL xs + 1 = 2 ^ (64 * xs.length)
  | [] => rfl
  | x :: xs => by
    have ih := valL_not xs
    have hx := x.isLt
    simp only [List.map_cons, valL, List.length_cons, pow64_succ, BitVec.toNat_not]
    omega_using [ih, hx]

/-- A borrow chain, with the last borrow dropped. -/
private theorem subL_mod (xs ys : List (BitVec 64)) (k : Bool) (h : xs.length = ys.length) :
    (valL (addL xs (ys.map (~~~·)) k) + valL ys + (!k).toNat) % 2 ^ (64 * xs.length) =
      valL xs % 2 ^ (64 * xs.length) := by
  have e := addL_value xs (ys.map (~~~·)) k (by simpa using h)
  have n := valL_not ys
  rw [← h] at n
  rw [← Nat.add_mul_mod_self_left (valL xs) _ 1,
    ← Nat.add_mul_mod_self_left _ _ (outL xs (ys.map (~~~·)) k).toNat]
  congr 1
  generalize 2 ^ (64 * xs.length) * (outL xs (ys.map (~~~·)) k).toNat = w at *
  cases k <;> simp only [Bool.toNat_true, Bool.toNat_false, Bool.not_true, Bool.not_false] at e ⊢ <;>
    omega_using [e, n]

private theorem add_value (a b : BitVec 64) (k : Bool) :
    (a + b + BitVec.ofNat 64 k.toNat).toNat + 2 ^ 64 * (decide (2 ^ 64 ≤ a.toNat + b.toNat + k.toNat)).toNat =
      a.toNat + b.toNat + k.toNat := addCarry_value a b k

private theorem extr_value (n m : BitVec 64) :
    ((n ++ m).extractLsb' 32 64).toNat = m.toNat / 2 ^ 32 + 2 ^ 32 * (n.toNat % 2 ^ 32) := by
  have hm := m.isLt
  have hn := n.isLt
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_append, Nat.shiftRight_eq_div_pow,
    ← Nat.shiftLeft_add_eq_or_of_lt hm, Nat.shiftLeft_eq]
  omega_using [hm, hn]

/-- Runs a block of register arithmetic. -/
local macro "exec_block" c:ident "[" hz:term "]" : tactic => `(tactic| (
  apply WP.of_runBlock
  simp only [$c:ident, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, RegUpd.c_write, Size.bits,
    BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, show (32 : Nat) < 64 by decide, $hz:term,
    Option.some.injEq, exists_eq_left']))

/-- The registers but those written are kept, and all else. -/
local macro "keeps_rest" : tactic => `(tactic| (
  refine ⟨fun r hr => ?_, by simp only [RegUpd.mem_write, RegUpd.mem_addWithCarry],
    by simp only [RegUpd.rd_write, RegUpd.rd_addWithCarry],
    by simp only [RegUpd.wr_write, RegUpd.wr_addWithCarry],
    by simp only [RegUpd.sp_write, RegUpd.sp_addWithCarry]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr, ite_false]))

/-- `addL_mod` (or `addL_value`) at the words the goal adds. -/
local macro "chain_value" h:term "," hz:term : tactic => `(tactic| (
  have h := $h
  simp only [valL, addL, outL, addCarry, carryOut, List.length_cons, List.length_nil,
    List.map_cons, List.map_nil, Bool.toNat_false, BitVec.toNat_zero, Nat.mul_zero, Nat.add_zero, Nat.zero_add, Nat.reduceAdd, -Nat.reducePow, -Nat.reduceMul] at h
  simp only [regsVal, RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, Size.bits,
    BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, $hz:term,
    Bool.toNat_false, BitVec.toNat_zero, Nat.mul_zero, Nat.add_zero, Nat.zero_add, -Nat.reducePow, -Nat.reduceMul]
  exact h))

/-! ## Blocks -/

private theorem crossMul_ok (s : State) :
    WP isa (.block crossMul) s fun t =>
      (t.gpr .x8).toNat + 2 ^ 64 * (t.gpr .x9).toNat = (s.gpr .x3).toNat * (s.gpr .x4).toNat ∧
      (t.gpr .x1).toNat + 2 ^ 64 * (t.gpr .x2).toNat = (s.gpr .x3).toNat * (s.gpr .x5).toNat ∧
      (t.gpr .x10).toNat + 2 ^ 64 * (t.gpr .x11).toNat = (s.gpr .x3).toNat * (s.gpr .x6).toNat ∧
      (t.gpr .x14).toNat + 2 ^ 64 * (t.gpr .x15).toNat = (s.gpr .x4).toNat * (s.gpr .x6).toNat ∧
      (t.gpr .x12).toNat + 2 ^ 64 * (t.gpr .x13).toNat = (s.gpr .x5).toNat * (s.gpr .x6).toNat ∧
      (t.gpr .x16).toNat + 2 ^ 64 * (t.gpr .x17).toNat = (s.gpr .x4).toNat * (s.gpr .x5).toNat ∧
      Keeps [.x1, .x2, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] s t := by
  exec_block crossMul [true_and]
  exact ⟨mul_lo_hi _ _, mul_lo_hi _ _, mul_lo_hi _ _, mul_lo_hi _ _, mul_lo_hi _ _, mul_lo_hi _ _,
    by keeps_rest⟩

private theorem diagonalMul_ok (s : State) :
    WP isa (.block diagonalMul) s fun t =>
      (t.gpr .x15).toNat + 2 ^ 64 * (t.gpr .x1).toNat = (s.gpr .x3).toNat * (s.gpr .x3).toNat ∧
      (t.gpr .x2).toNat + 2 ^ 64 * (t.gpr .x16).toNat = (s.gpr .x4).toNat * (s.gpr .x4).toNat ∧
      (t.gpr .x17).toNat + 2 ^ 64 * (t.gpr .x3).toNat = (s.gpr .x5).toNat * (s.gpr .x5).toNat ∧
      (t.gpr .x4).toNat + 2 ^ 64 * (t.gpr .x6).toNat = (s.gpr .x6).toNat * (s.gpr .x6).toNat ∧
      Keeps [.x1, .x2, .x3, .x4, .x6, .x15, .x16, .x17] s t := by
  exec_block diagonalMul [true_and]
  exact ⟨mul_lo_hi _ _, mul_lo_hi _ _, mul_lo_hi _ _, mul_lo_hi _ _, by keeps_rest⟩

private theorem crossAdd_ok (s : State) (hz : s.gpr .x7 = 0) :
    WP isa (.block crossAdd) s fun t =>
      regsVal t [.x9, .x10, .x11, .x12, .x13] =
        (regsVal s [.x9, .x10, .x11, .x12, .x13] + regsVal s [.x1, .x2, .x14, .x15]) % 2 ^ (64 * 5) ∧
      Keeps [.x9, .x10, .x11, .x12, .x13] s t := by
  exec_block crossAdd [hz]
  refine ⟨?_, by keeps_rest⟩
  chain_value (addL_mod [s.gpr .x9, s.gpr .x10, s.gpr .x11, s.gpr .x12, s.gpr .x13] [s.gpr .x1, s.gpr .x2, s.gpr .x14, s.gpr .x15, 0] false rfl), hz

private theorem crossAdd'_ok (s : State) (hz : s.gpr .x7 = 0) :
    WP isa (.block crossAdd') s fun t =>
      regsVal t [.x10, .x11, .x12, .x13] =
        (regsVal s [.x10, .x11, .x12, .x13] + regsVal s [.x16, .x17]) % 2 ^ (64 * 4) ∧
      Keeps [.x10, .x11, .x12, .x13] s t := by
  exec_block crossAdd' [hz]
  refine ⟨?_, by keeps_rest⟩
  chain_value (addL_mod [s.gpr .x10, s.gpr .x11, s.gpr .x12, s.gpr .x13] [s.gpr .x16, s.gpr .x17, 0, 0] false rfl), hz

private theorem double_ok (s : State) (hz : s.gpr .x7 = 0) :
    WP isa (.block double) s fun t =>
      regsVal t [.x8, .x9, .x10, .x11, .x12, .x13, .x14] =
        (regsVal s [.x8, .x9, .x10, .x11, .x12, .x13] + regsVal s [.x8, .x9, .x10, .x11, .x12, .x13]) % 2 ^ (64 * 7) ∧
      Keeps [.x8, .x9, .x10, .x11, .x12, .x13, .x14] s t := by
  exec_block double [hz]
  refine ⟨?_, by keeps_rest⟩
  chain_value (addL_mod [s.gpr .x8, s.gpr .x9, s.gpr .x10, s.gpr .x11, s.gpr .x12, s.gpr .x13, 0] [s.gpr .x8, s.gpr .x9, s.gpr .x10, s.gpr .x11, s.gpr .x12, s.gpr .x13, 0] false rfl), hz

private theorem diagonalAdd_ok (s : State) :
    WP isa (.block diagonalAdd) s fun t =>
      regsVal t [.x8, .x9, .x10, .x11, .x12, .x13, .x14] =
        (regsVal s [.x8, .x9, .x10, .x11, .x12, .x13, .x14] + regsVal s [.x1, .x2, .x16, .x17, .x3, .x4, .x6]) % 2 ^ (64 * 7) ∧
      Keeps [.x8, .x9, .x10, .x11, .x12, .x13, .x14] s t := by
  exec_block diagonalAdd [true_and]
  refine ⟨?_, by keeps_rest⟩
  chain_value (addL_mod [s.gpr .x8, s.gpr .x9, s.gpr .x10, s.gpr .x11, s.gpr .x12, s.gpr .x13, s.gpr .x14] [s.gpr .x1, s.gpr .x2, s.gpr .x16, s.gpr .x17, s.gpr .x3, s.gpr .x4, s.gpr .x6] false rfl), true_and

private theorem addTop_ok (s : State) (hz : s.gpr .x7 = 0) :
    WP isa (.block addTop) s fun t =>
      regsVal t [.x11, .x12, .x13, .x14] =
        (regsVal s [.x11, .x12, .x13, .x14] + regsVal s [.x6, .x16] + s.c.toNat) % 2 ^ (64 * 4) ∧
      Keeps [.x11, .x12, .x13, .x14] s t := by
  exec_block addTop [hz]
  refine ⟨?_, by keeps_rest⟩
  chain_value (addL_mod [s.gpr .x11, s.gpr .x12, s.gpr .x13, s.gpr .x14] [s.gpr .x6, s.gpr .x16, 0, 0] s.c rfl), hz

private theorem sum_ok (s : State) (hz : s.gpr .x7 = 0) :
    WP isa (.block sum) s fun t =>
      regsVal t [.x8, .x9, .x10, .x11, .x12] =
        (regsVal s [.x11, .x12, .x13, .x14] + regsVal s [.x15, .x2, .x3, .x1]) % 2 ^ (64 * 5) ∧
      Keeps [.x8, .x9, .x10, .x11, .x12] s t := by
  exec_block sum [hz]
  refine ⟨?_, by keeps_rest⟩
  chain_value (addL_mod [s.gpr .x11, s.gpr .x12, s.gpr .x13, s.gpr .x14, 0] [s.gpr .x15, s.gpr .x2, s.gpr .x3, s.gpr .x1, 0] false rfl), hz

private theorem addShift_ok (s : State) (hz : s.gpr .x7 = 0) :
    WP isa (.block addShift) s fun t => ∃ k : Bool,
      (t.gpr .x4).toNat + 2 ^ 64 * k.toNat = (s.gpr .x10).toNat + (s.gpr .x4).toNat ∧
      regsVal t [.x15, .x2, .x3, .x1] =
        (regsVal s [.x15, .x2, .x3, .x1] + regsVal s [.x8, .x9, .x5] + k.toNat) % 2 ^ (64 * 4) ∧
      Keeps [.x1, .x2, .x3, .x4, .x15] s t := by
  exec_block addShift [hz]
  refine ⟨carryOut (s.gpr .x10) (s.gpr .x4) false, addCarry_value _ _ false, ?_, by keeps_rest⟩
  chain_value (addL_mod [s.gpr .x15, s.gpr .x2, s.gpr .x3, s.gpr .x1] [s.gpr .x8, s.gpr .x9, s.gpr .x5, 0]
    (carryOut (s.gpr .x10) (s.gpr .x4) false) rfl), hz

private theorem subShift_ok (s : State) :
    WP isa (.block subShift) s fun t => ∃ b : Bool, ∃ g : BitVec 64,
      g.toNat + (s.gpr .x1).toNat = (s.gpr .x15).toNat + 2 ^ 64 * b.toNat ∧
      (regsVal t [.x15, .x2, .x3, .x1] + regsVal s [.x2, .x3, .x6, .x16] + b.toNat) % 2 ^ (64 * 4) =
        regsVal s [.x15, .x8, .x9, .x5] % 2 ^ (64 * 4) ∧
      Keeps [.x1, .x2, .x3, .x15] s t := by
  exec_block subShift [true_and]
  refine ⟨!carryOut (s.gpr .x15) (~~~s.gpr .x1) true, addCarry (s.gpr .x15) (~~~s.gpr .x1) true, ?_, ?_,
    by keeps_rest⟩
  · have h := subCarry_value (s.gpr .x15) (s.gpr .x1) true
    cases hc : carryOut (s.gpr .x15) (~~~s.gpr .x1) true <;>
      simp only [hc, Bool.toNat_true, Bool.toNat_false, Bool.not_true, Bool.not_false] at h ⊢ <;>
      omega_using [h]
  · chain_value (subL_mod [s.gpr .x15, s.gpr .x8, s.gpr .x9, s.gpr .x5]
      [s.gpr .x2, s.gpr .x3, s.gpr .x6, s.gpr .x16] (carryOut (s.gpr .x15) (~~~s.gpr .x1) true) rfl), true_and

private theorem quotient_ok (s : State) :
    WP isa (.block quotient) s fun t => ∃ c1 c2 b : Bool,
      (t.gpr .x1).toNat = 2 ^ 32 * ((s.gpr .x15).toNat % 2 ^ 32) ∧
      t.gpr .x15 = s.gpr .x15 ∧
      (t.gpr .x4).toNat + (t.gpr .x1).toNat = (s.gpr .x15).toNat + 2 ^ 64 * b.toNat ∧
      (t.gpr .x8).toNat + 2 ^ 64 * c1.toNat = (s.gpr .x8).toNat + (t.gpr .x1).toNat ∧
      (t.gpr .x2).toNat = (t.gpr .x15).toNat / 2 ^ 32 + 2 ^ 32 * ((t.gpr .x8).toNat % 2 ^ 32) ∧
      (t.gpr .x9).toNat + 2 ^ 64 * c2.toNat = (s.gpr .x9).toNat + (t.gpr .x2).toNat + c1.toNat ∧
      (t.gpr .x3).toNat = (t.gpr .x8).toNat / 2 ^ 32 + 2 ^ 32 * ((t.gpr .x9).toNat % 2 ^ 32) ∧
      (t.gpr .x10).toNat + 2 ^ 64 * t.c.toNat = (s.gpr .x10).toNat + (t.gpr .x3).toNat + c2.toNat ∧
      t.gpr .x5 = t.gpr .x10 + t.gpr .x4 ∧
      (t.gpr .x6).toNat = (t.gpr .x9).toNat / 2 ^ 32 + 2 ^ 32 * ((t.gpr .x5).toNat % 2 ^ 32) ∧
      (t.gpr .x16).toNat = (t.gpr .x5).toNat / 2 ^ 32 ∧
      Keeps [.x1, .x2, .x3, .x4, .x5, .x6, .x8, .x9, .x10, .x16] s t := by
  exec_block quotient [true_and]
  have hL : (s.gpr .x15 <<< 32).toNat = 2 ^ 32 * ((s.gpr .x15).toNat % 2 ^ 32) := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    omega_using []
  generalize s.gpr .x15 <<< 32 = L at *
  have f1 := extr_value (s.gpr .x8) (s.gpr .x15)
  generalize (s.gpr .x8 ++ s.gpr .x15).extractLsb' 32 64 = e at *
  have e1 := add_value (s.gpr .x8) L false
  generalize s.gpr .x8 + L + BitVec.ofNat 64 false.toNat = q1 at *
  generalize decide (2 ^ 64 ≤ (s.gpr .x8).toNat + L.toNat + false.toNat) = c1 at *
  have e2 := add_value (s.gpr .x9) e c1
  generalize s.gpr .x9 + e + BitVec.ofNat 64 c1.toNat = q2 at *
  generalize decide (2 ^ 64 ≤ (s.gpr .x9).toNat + e.toNat + c1.toNat) = c2 at *
  have f2 := extr_value q2 q1
  generalize (q2 ++ q1).extractLsb' 32 64 = f at *
  have e3 := add_value (s.gpr .x10) f c2
  generalize s.gpr .x10 + f + BitVec.ofNat 64 c2.toNat = q3 at *
  generalize decide (2 ^ 64 ≤ (s.gpr .x10).toNat + f.toNat + c2.toNat) = c3 at *
  have f1' : e.toNat = (s.gpr .x15).toNat / 2 ^ 32 + 2 ^ 32 * (q1.toNat % 2 ^ 32) := by
    rw [f1]
    rw [Bool.toNat_false, Nat.add_zero, hL] at e1
    omega_using [e1]
  refine ⟨c1, c2, decide ((s.gpr .x15).toNat < L.toNat), hL, ?_, e1, f1', e2, f2, e3,
    extr_value _ _, ?_, by keeps_rest⟩
  · have h1 := (s.gpr .x15).isLt
    have h2 := L.isLt
    rw [BitVec.toNat_sub]
    by_cases h : (s.gpr .x15).toNat < L.toNat <;>
      simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;>
      omega_using [h, h1, h2]
  · rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

end

/-! ## The arithmetic of the square -/

private theorem mul_max {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    a * b ≤ 340282366920938463426481119284349108225 :=
  Nat.mul_le_mul (Nat.le_of_lt_succ ha) (Nat.le_of_lt_succ hb)

private theorem square_expand (a0 a1 a2 a3 : Nat) :
    (a0 + 2 ^ 64 * (a1 + 2 ^ 64 * (a2 + 2 ^ 64 * a3))) * (a0 + 2 ^ 64 * (a1 + 2 ^ 64 * (a2 + 2 ^ 64 * a3))) =
      a0 * a0 + 2 ^ 64 * (2 * (a0 * a1)) + 2 ^ 128 * (2 * (a0 * a2) + a1 * a1) +
      2 ^ 192 * (2 * (a0 * a3) + 2 * (a1 * a2)) + 2 ^ 256 * (2 * (a1 * a3) + a2 * a2) +
      2 ^ 256 * (2 ^ 64 * (2 * (a2 * a3))) + 2 ^ 256 * (2 ^ 128 * (a3 * a3)) := by
  generalize h1 : a1 + 2 ^ 64 * (a2 + 2 ^ 64 * a3) = b1
  generalize h2 : a2 + 2 ^ 64 * a3 = b2 at h1
  have sq : ∀ x y : Nat, (x + 2 ^ 64 * y) * (x + 2 ^ 64 * y) =
      x * x + 2 ^ 64 * (2 * (x * y)) + 2 ^ 128 * (y * y) := fun x y => by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_left_comm x, Nat.mul_assoc, Nat.mul_assoc,
      Nat.mul_left_comm y, Nat.mul_comm y x]
    omega_using []
  have m : ∀ x y z : Nat, x * (y + 2 ^ 64 * z) = x * y + 2 ^ 64 * (x * z) := fun x y z => by
    rw [Nat.mul_add, Nat.mul_left_comm]
  have e0 := sq a0 b1
  have e1 := sq a1 b2
  have e2 := sq a2 a3
  have f0 := m a0 a1 b2
  have f1 := m a0 a2 a3
  have f2 := m a1 a2 a3
  rw [h1] at e1 f0
  rw [h2] at e2 f1 f2
  omega_using [e0, e1, e2, f0, f1, f2]

/-- The parts of `core` before the reduction, as numbers: products `pᵢⱼ`, and the sums of the words. -/
private theorem product_arith {p01 p02 p03 p12 p13 p23 p00 p11 p22 p33 : Nat}
    (m01 : p01 ≤ 340282366920938463426481119284349108225) (m02 : p02 ≤ 340282366920938463426481119284349108225)
    (m03 : p03 ≤ 340282366920938463426481119284349108225) (m12 : p12 ≤ 340282366920938463426481119284349108225)
    (m13 : p13 ≤ 340282366920938463426481119284349108225) (m23 : p23 ≤ 340282366920938463426481119284349108225)
    (m00 : p00 ≤ 340282366920938463426481119284349108225) (m11 : p11 ≤ 340282366920938463426481119284349108225)
    (m22 : p22 ≤ 340282366920938463426481119284349108225) (m33 : p33 ≤ 340282366920938463426481119284349108225)
    {s1 u v w d t0 t : Nat} {r : Nat}
    (hu : s1 + 2 ^ 64 * u = p01 + 2 ^ 128 * p03 + 2 ^ 256 * p23)
    (hv : v = (u + p02 + 2 ^ 128 * p13) % 2 ^ (64 * 5))
    (hw : w = (r + p12) % 2 ^ (64 * 4)) {s2 : Nat} (hs : v = s2 + 2 ^ 64 * r)
    (hd : d = ((s1 + 2 ^ 64 * (s2 + 2 ^ 64 * w)) + (s1 + 2 ^ 64 * (s2 + 2 ^ 64 * w))) % 2 ^ (64 * 7))
    {y : Nat} (hy : t0 + 2 ^ 64 * y = p00 + 2 ^ 128 * p11 + 2 ^ 256 * p22 + 2 ^ 256 * (2 ^ 128 * p33))
    (ht : t = (d + y) % 2 ^ (64 * 7)) :
    t0 + 2 ^ 64 * t = p00 + 2 ^ 64 * (2 * p01) + 2 ^ 128 * (2 * p02 + p11) +
      2 ^ 192 * (2 * p03 + 2 * p12) + 2 ^ 256 * (2 * p13 + p22) +
      2 ^ 256 * (2 ^ 64 * (2 * p23)) + 2 ^ 256 * (2 ^ 128 * p33) := by
  rw [Nat.mod_eq_of_lt (by omega)] at hv
  rw [Nat.mod_eq_of_lt (by omega)] at hw
  rw [Nat.mod_eq_of_lt (by omega)] at hd
  rw [Nat.mod_eq_of_lt (by omega)] at ht
  omega

private theorem quotient_arith {t0 t1 t2 t3 q1 q2 q3 L e f E H g q3' g2 : Nat} {c1 c2 c3 k b b2 : Nat}
    (h0 : t0 < 2 ^ 64) (h1 : q1 < 2 ^ 64) (h2 : q2 < 2 ^ 64) (h3 : q3 < 2 ^ 64) (hg : g < 2 ^ 64)
    (hg2 : g2 < 2 ^ 64)
    (hL : L = 2 ^ 32 * (t0 % 2 ^ 32)) (eg : g + L = t0 + 2 ^ 64 * b) (e1 : q1 + 2 ^ 64 * c1 = t1 + L)
    (he : e = t0 / 2 ^ 32 + 2 ^ 32 * (q1 % 2 ^ 32)) (e2 : q2 + 2 ^ 64 * c2 = t2 + e + c1)
    (hf : f = q1 / 2 ^ 32 + 2 ^ 32 * (q2 % 2 ^ 32)) (e3 : q3' + 2 ^ 64 * c3 = t3 + f + c2)
    (e4 : q3 + 2 ^ 64 * k = q3' + g)
    (hE : E = q2 / 2 ^ 32 + 2 ^ 32 * (q3 % 2 ^ 32)) (hH : H = q3 / 2 ^ 32)
    (eg2 : g2 + L = t0 + 2 ^ 64 * b2) {Q S W w u hi x z : Nat}
    (hQ : Q = t0 + 2 ^ 64 * (q1 + 2 ^ 64 * (q2 + 2 ^ 64 * q3)))
    (hS : S = e + 2 ^ 64 * (f + 2 ^ 64 * (E + 2 ^ 64 * H)))
    (hw : (w + S + b2) % 2 ^ (64 * 4) = Q % 2 ^ (64 * 4)) (lw : w < 2 ^ 256)
    (hu : u = (w + (q1 + 2 ^ 64 * (q2 + 2 ^ 64 * q3)) + k) % 2 ^ (64 * 4))
    (hW : W = t0 + 2 ^ 64 * (t1 + 2 ^ 64 * (t2 + 2 ^ 64 * (t3 + 2 ^ 64 * hi))))
    (lW : W ≤ (p - 1) * (p - 1))
    (hx : x = (hi + (E + 2 ^ 64 * H) + c3) % 2 ^ (64 * 4))
    (hz : z = (x + u) % 2 ^ (64 * 5)) (lb : b2 ≤ 1) (lb' : b ≤ 1) (lc : c3 ≤ 1) (lk : k ≤ 1) :
    R * z = W + Q * p ∧ Q < R := by
  have eb : b2 = b := by omega_using [eg, eg2, hg, hg2, h0]
  subst eb
  have lQ : Q < 2 ^ 256 := by omega_using [hQ, h0, h1, h2, h3]
  have hSQ : S = Q / 2 ^ 32 := by omega_using [hS, hQ, he, hf, hE, hH, h0, h1, h2, h3]
  have hb : b2 = 1 → 0 < t0 := by omega_using [eg2, hL, hg2]
  have hw' : w + S + b2 = Q := by omega_using [hw, lw, lQ, hSQ, hb, hQ, lb]
  rw [Nat.mod_eq_of_lt (by omega_using [hw', hSQ, hQ, lQ, h0, h1, h2, h3, lk])] at hu
  have lhi : hi ≤ (p - 1) * (p - 1) / 2 ^ 256 := by omega_using [hW, lW]
  rw [show (p - 1) * (p - 1) / 2 ^ 256 =
    115792089183396302108101010622590916696416568118661299565705949134266174537724 by decide +kernel] at lhi
  rw [Nat.mod_eq_of_lt (by omega_using [lhi, hE, hH, h2, h3, lc])] at hx
  rw [Nat.mod_eq_of_lt (by omega_using [hx, hu, lhi, hE, hH, h1, h2, h3, lc, lk, lw])] at hz
  refine ⟨?_, lQ⟩
  have d0 := Nat.div_add_mod t0 (2 ^ 32)
  have d1 := Nat.div_add_mod q1 (2 ^ 32)
  have d2 := Nat.div_add_mod q2 (2 ^ 32)
  have d3 := Nat.div_add_mod q3 (2 ^ 32)
  rw [← hH] at d3
  generalize t0 % 2 ^ 32 = l0, t0 / 2 ^ 32 = u0, q1 % 2 ^ 32 = l1, q1 / 2 ^ 32 = u1, q2 % 2 ^ 32 = l2,
    q2 / 2 ^ 32 = u2, q3 % 2 ^ 32 = l3 at *
  clear hSQ lhi hb lQ lW lw
  unfold R p
  omega_using [hz, hx, hu, hW, hw', hQ, hS, e1, e2, e3, e4, eg, hL, he, hf, hE, d0, d1, d2, d3]


/-! ## The code -/

/-- The registers `square` changes. -/
def squareClob : List Reg := clob 4

/-- What `square` keeps. -/
structure SquareKeep (base : Addr) (o : Nat) (s t : State) : Prop where
  gpr : ∀ r, r ∉ squareClob → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : Outside base o 32 s.mem t.mem

theorem SquareKeep.toOpKeep {M : Mod} {base : Addr} {o : Nat} {s t : State} (h : SquareKeep base o s t)
    (hn : M.n = 4) : OpKeep M base o s t :=
  ⟨fun r hr => h.gpr r (by rwa [hn] at hr), h.rd, h.wr, h.sp,
    fun x hx _ => h.mem x (by rwa [hn] at hx)⟩

/-- `t₀, …, t₇`, in `x15` and `x8`–`x14`. -/
private theorem product_ok (s : State) (hz : s.gpr .x7 = 0) :
    WP isa (.block (crossMul ++ (crossAdd ++ (crossAdd' ++ (double ++ (diagonalMul ++ diagonalAdd)))))) s fun t =>
      (t.gpr .x15).toNat + 2 ^ 64 * regsVal t [.x8, .x9, .x10, .x11, .x12, .x13, .x14] =
        regsVal s operand * regsVal s operand ∧
      t.gpr .x7 = 0 ∧ Keeps squareClob s t := by
  rw [WP.block_append_iff]
  refine WP.mono (crossMul_ok s) fun s1 ⟨p01, p02, p03, p13, p23, p12, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (crossAdd_ok s1 (by rw [k1.gpr _ (by decide), hz])) fun s2 ⟨e2, k2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (crossAdd'_ok s2 (by rw [k2.gpr _ (by decide), k1.gpr _ (by decide), hz]))
    fun s3 ⟨e3, k3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (double_ok s3 (by rw [k3.gpr _ (by decide), k2.gpr _ (by decide), k1.gpr _ (by decide), hz]))
    fun s4 ⟨e4, k4⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (diagonalMul_ok s4) fun s5 ⟨p00, p11, p22, p33, k5⟩ => ?_
  refine WP.mono (diagonalAdd_ok s5) fun t ⟨e6, k6⟩ => ?_
  have k14 : Keeps [.x1, .x2, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] s s4 :=
    ((k1.trans (k2.mono (by decide))).trans (k3.mono (by decide))).trans (k4.mono (by decide))
  refine ⟨?_, by rw [k6.gpr _ (by decide), k5.gpr _ (by decide), k14.gpr _ (by decide), hz],
    ((k14.mono (by decide)).trans (k5.mono (by decide))).trans (k6.mono (by decide))⟩
  rw [k14.gpr .x3 (by decide)] at p00
  rw [k14.gpr .x4 (by decide)] at p11
  rw [k14.gpr .x5 (by decide)] at p22
  rw [k14.gpr .x6 (by decide)] at p33
  have l3 := (s.gpr .x3).isLt
  have l4 := (s.gpr .x4).isLt
  have l5 := (s.gpr .x5).isLt
  have l6 := (s.gpr .x6).isLt
  rw [show regsVal s5 [.x8, .x9, .x10, .x11, .x12, .x13, .x14] =
    regsVal s4 [.x8, .x9, .x10, .x11, .x12, .x13, .x14] from
    regsVal_congr fun r hr => k5.gpr r ((by decide : ∀ r ∈ [Reg.x8, .x9, .x10, .x11, .x12, .x13, .x14],
      r ∉ [Reg.x1, .x2, .x3, .x4, .x6, .x15, .x16, .x17]) r hr)] at e6
  rw [show regsVal s2 [.x16, .x17] = regsVal s1 [.x16, .x17] from
    regsVal_congr fun r hr => k2.gpr r ((by decide : ∀ r ∈ [Reg.x16, .x17],
      r ∉ [Reg.x9, .x10, .x11, .x12, .x13]) r hr)] at e3
  simp only [regsVal, operand, Nat.mul_zero, Nat.add_zero, -Nat.reducePow, -Nat.reduceMul] at e2 e3 e4 e6 ⊢
  rw [k3.gpr .x8 (by decide), k2.gpr .x8 (by decide), k3.gpr .x9 (by decide)] at e4
  rw [square_expand, k6.gpr .x15 (by decide)]
  exact product_arith (mul_max l3 l4) (mul_max l3 l5) (mul_max l3 l6) (mul_max l4 l5) (mul_max l4 l6)
    (mul_max l5 l6) (mul_max l3 l3) (mul_max l4 l4) (mul_max l5 l5) (mul_max l6 l6)
    (s1 := (s1.gpr .x8).toNat) (s2 := (s2.gpr .x9).toNat)
    (u := regsVal s1 [.x9, .x10, .x11, .x12, .x13])
    (y := regsVal s5 [.x1, .x2, .x16, .x17, .x3, .x4, .x6])
    (by rw [← p01, ← p03, ← p23]; simp only [regsVal]; omega_using [])
    (e2.trans (by rw [← p02, ← p13]; congr 1; simp only [regsVal]; omega_using [])) (e3.trans (by rw [← p12])) rfl e4
    (by rw [← p00, ← p11, ← p22, ← p33]; simp only [regsVal]; omega_using []) (by simpa only [regsVal, Nat.mul_zero, Nat.add_zero, -Nat.reducePow, -Nat.reduceMul] using e6)

/-- The reduction of `t₀, …, t₇`. -/
private theorem reduction_ok (s : State) (hz : s.gpr .x7 = 0) {W : Nat}
    (hW : (s.gpr .x15).toNat + 2 ^ 64 * regsVal s [.x8, .x9, .x10, .x11, .x12, .x13, .x14] = W)
    (lW : W ≤ (p - 1) * (p - 1)) :
    WP isa (.block (quotient ++ (addTop ++ (subShift ++ (addShift ++ sum))))) s fun t => ∃ Q < R,
      R * (regsVal t result + R * (t.gpr .x12).toNat) = W + Q * p ∧
        t.gpr .x7 = 0 ∧ Keeps squareClob s t := by
  rw [WP.block_append_iff]
  refine WP.mono (quotient_ok s) fun s1 ⟨c1, c2, b, hL, x15, eg, e1, he, e2, hf, e3, hq, hE, hH, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (addTop_ok s1 (by rw [k1.gpr _ (by decide), hz])) fun s2 ⟨a2, k2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (subShift_ok s2) fun s3 ⟨b2, g2, eg2, hw, k3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (addShift_ok s3 (by rw [k3.gpr _ (by decide), k2.gpr _ (by decide), k1.gpr _ (by decide), hz]))
    fun s4 ⟨k, e4, hu, k4⟩ => ?_
  refine WP.mono (sum_ok s4 (by rw [k4.gpr _ (by decide), k3.gpr _ (by decide), k2.gpr _ (by decide),
    k1.gpr _ (by decide), hz])) fun t ⟨e5, k5⟩ => ?_
  have lw := regsVal_lt s3 [.x15, .x2, .x3, .x1]
  rw [show regsVal s2 [.x2, .x3, .x6, .x16] = regsVal s1 [.x2, .x3, .x6, .x16] from
      regsVal_congr fun r hr => k2.gpr r ((by decide : ∀ r ∈ [Reg.x2, .x3, .x6, .x16],
        r ∉ [Reg.x11, .x12, .x13, .x14]) r hr),
    show regsVal s2 [.x15, .x8, .x9, .x5] = regsVal s1 [.x15, .x8, .x9, .x5] from
      regsVal_congr fun r hr => k2.gpr r ((by decide : ∀ r ∈ [Reg.x15, .x8, .x9, .x5],
        r ∉ [Reg.x11, .x12, .x13, .x14]) r hr)] at hw
  rw [show regsVal s3 [.x8, .x9, .x5] = regsVal s1 [.x8, .x9, .x5] from
      regsVal_congr fun r hr => ((k2.mono (by decide)).trans (k3.mono (by decide)) : Keeps
        [.x1, .x2, .x3, .x15, .x11, .x12, .x13, .x14] s1 s3).gpr r ((by decide : ∀ r ∈ [Reg.x8, .x9, .x5],
        r ∉ [Reg.x1, .x2, .x3, .x15, .x11, .x12, .x13, .x14]) r hr)] at hu
  rw [show regsVal s4 [.x11, .x12, .x13, .x14] = regsVal s2 [.x11, .x12, .x13, .x14] from
      regsVal_congr fun r hr => ((k3.mono (by decide)).trans (k4.mono (by decide)) : Keeps
        [.x1, .x2, .x3, .x4, .x15] s2 s4).gpr r ((by decide : ∀ r ∈ [Reg.x11, .x12, .x13, .x14],
        r ∉ [Reg.x1, .x2, .x3, .x4, .x15]) r hr)] at e5
  rw [show regsVal s1 [.x11, .x12, .x13, .x14] = regsVal s [.x11, .x12, .x13, .x14] from
      regsVal_congr fun r hr => k1.gpr r ((by decide : ∀ r ∈ [Reg.x11, .x12, .x13, .x14],
        r ∉ [Reg.x1, .x2, .x3, .x4, .x5, .x6, .x8, .x9, .x10, .x16]) r hr)] at a2
  rw [k3.gpr .x10 (by decide), k2.gpr .x10 (by decide), k3.gpr .x4 (by decide), k2.gpr .x4 (by decide)] at e4
  rw [k2.gpr .x1 (by decide), k2.gpr .x15 (by decide)] at eg2
  rw [x15] at he eg2
  have l1 := (s.gpr .x15).isLt
  have hq' : (s1.gpr .x5).toNat + 2 ^ 64 * k.toNat = (s1.gpr .x10).toNat + (s1.gpr .x4).toNat := by
    rw [← e4, hq, BitVec.toNat_add]
    have := (s4.gpr .x4).isLt
    omega_using [e4, this, Bool.toNat_le k]
  have hz' : regsVal t result + R * (t.gpr .x12).toNat = regsVal t [.x8, .x9, .x10, .x11, .x12] := by
    simp only [regsVal, result, R]
    omega_using []
  rw [hz']
  simp only [regsVal, Nat.mul_zero, Nat.add_zero, -Nat.reducePow, -Nat.reduceMul, x15] at hW hw
  have key := quotient_arith l1 (s1.gpr .x8).isLt (s1.gpr .x9).isLt (s1.gpr .x5).isLt (s1.gpr .x4).isLt g2.isLt
    hL eg e1 he e2 hf e3 hq' hE hH eg2 rfl rfl hw lw
    (hu.trans (by simp only [regsVal, Nat.mul_zero, Nat.add_zero]))
    (hi := regsVal s [.x11, .x12, .x13, .x14]) (by
      rw [← hW]
      simp only [regsVal, Nat.mul_zero, Nat.add_zero]) lW
    (a2.trans (by simp only [regsVal, Nat.mul_zero, Nat.add_zero])) e5
    (Bool.toNat_le _) (Bool.toNat_le _) (Bool.toNat_le _) (Bool.toNat_le _)
  refine ⟨_, key.2, key.1, by rw [k5.gpr _ (by decide), k4.gpr _ (by decide), k3.gpr _ (by decide),
    k2.gpr _ (by decide), k1.gpr _ (by decide), hz], (((k1.mono (by decide)).trans (k2.mono (by decide))).trans
    ((k3.mono (by decide)).trans (k4.mono (by decide)))).trans (k5.mono (by decide))⟩

/-- The square before its last subtraction. -/
theorem core_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a : Nat}
    (ha : a + 32 ≤ size) (ha8 : a % 8 = 0) (hA : wordsVal s.mem base a 4 < p) :
    WP isa (.block (core a)) s fun t =>
      (regsVal t result + R * (t.gpr .x12).toNat < 2 * p ∧
        (regsVal t result + R * (t.gpr .x12).toNat) * R % p =
          wordsVal s.mem base a 4 * wordsVal s.mem base a 4 % p) ∧
      t.gpr .x7 = 0 ∧ Keeps squareClob s t := by
  rw [core, ← List.singleton_append, List.append_assoc, WP.block_append_iff]
  refine WP.mono (zero7_ok s) fun s1 ⟨z1, k1⟩ => ?_
  rw [loads_eq, WP.block_append_iff]
  refine WP.mono (loadsR_ok operand (hs.of_keeps k1 (by decide)).ptr (a := a) ha ha8 (by decide) (by decide))
    fun s2 ⟨e2, k2, _⟩ => ?_
  have z2 : s2.gpr .x7 = 0 := by rw [k2.gpr _ (by decide), z1]
  rw [k1.mem] at e2
  change regsVal s2 operand = wordsVal s.mem base a 4 at e2
  rw [show (crossMul ++ crossAdd ++ crossAdd' ++ double ++ diagonalMul ++ diagonalAdd ++ quotient ++
      addTop ++ subShift ++ addShift ++ sum) =
    (crossMul ++ (crossAdd ++ (crossAdd' ++ (double ++ (diagonalMul ++ diagonalAdd))))) ++
      (quotient ++ (addTop ++ (subShift ++ (addShift ++ sum)))) by simp only [List.append_assoc],
    WP.block_append_iff]
  refine WP.mono (product_ok s2 z2) fun s3 ⟨e3, z3, k3⟩ => ?_
  rw [e2] at e3
  have hA' : wordsVal s.mem base a 4 * wordsVal s.mem base a 4 ≤ (p - 1) * (p - 1) :=
    Nat.mul_le_mul (Nat.le_sub_one_of_lt hA) (Nat.le_sub_one_of_lt hA)
  refine WP.mono (reduction_ok s3 z3 e3 hA') fun t ⟨Q, hQ, e4, z4, k4⟩ => ?_
  have k : Keeps squareClob s t :=
    (((k1.mono (by decide)).trans (k2.mono (by decide))).trans k3).trans k4
  refine ⟨⟨?_, ?_⟩, z4, k⟩
  · generalize regsVal t result + R * (t.gpr .x12).toNat = z at *
    generalize wordsVal s.mem base a 4 * wordsVal s.mem base a 4 = W at *
    simp only [p, R] at *
    omega
  · rw [Nat.mul_comm, e4, Nat.add_mul_mod_self_right]

/-- `[o] = [a]² R⁻¹ mod p`. -/
theorem square_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} (hn : M.n = 4)
    (hM : ModOkA M size p s.mem base) (hMA : ModA M) {o a : Nat} (ho : o + 32 ≤ size)
    (ha : a + 32 ≤ size) (ho8 : o % 8 = 0) (ha8 : a % 8 = 0) (hA : wordsVal s.mem base a 4 < p) :
    WP isa (.block (square M o a)) s fun t => SquareKeep base o s t ∧
      wordsVal t.mem base o 4 < p ∧
      wordsVal t.mem base o 4 * R % p = wordsVal s.mem base a 4 * wordsVal s.mem base a 4 % p := by
  rw [square, WP.block_append_iff]
  refine WP.mono (core_ok hs ha ha8 hA) fun s₁ ⟨⟨hb, e₁⟩, z₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (csubR_ok hs₁ (M := M) (m := p) (ts := result) (top := .x12) (by rw [hn]; rfl) hM.n0 hM.n10
    (by unfold Fresh; decide) hM.mo hMA.mo z₁ (by rw [k₁.mem]; exact hM.val) (by rw [hn]; exact hb))
    fun s₂ ⟨e₂, k₂⟩ => ?_
  rw [hn] at e₂
  have k₂' : Keeps squareClob s₁ s₂ := k₂.mono (by rw [hn]; decide)
  have hs₂ := hs₁.of_keeps k₂' (by decide)
  refine WP.mono (stores_ok result hs₂ ho ho8 (by decide)) fun t ⟨e₃, k₃, o₃⟩ => ?_
  change wordsVal t.mem base o 4 = regsVal s₂ result at e₃
  have kp := k₁.trans k₂'
  refine ⟨⟨fun r hr => (k₃.gpr r (by simp)).trans (kp.gpr r hr), k₃.rd.trans kp.rd, k₃.wr.trans kp.wr,
    k₃.sp.trans kp.sp, fun x hx => (o₃ x hx).trans (congrFun kp.mem x)⟩, ?_, ?_⟩
  · rw [e₃, e₂]; exact Nat.mod_lt _ (by decide)
  · rw [e₃, e₂, Nat.mod_mul_mod]; exact e₁

end VG.Proof.Mont.AArch64.P256Square
