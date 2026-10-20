module
public import VerifiedGarbage.Proof.Argon2.AArch64.DivideStep

import VerifiedGarbage.Proof.Argon2.Divide
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # Fixed-time division as a loop

`Divide.loopCode` runs `bit 31` thirty-two times, doubling x0 after each step
so that step `k` takes bit `31 - k` of the numerator, and counts x15 down. -/

@[expose] public section

namespace VG.Proof.Argon2.AArch64.Divide

open VG VG.AArch64 VG.Impl.Argon2.AArch64.Divide

/-- `changed`, and the consumed numerator and the counter. -/
def loopChanged : List Reg := [.x3, .x4, .x6, .x8, .x5, .x9, .x0, .x15]

/-- After `k` steps, of the numerator and divisor in `s₀`. -/
structure LoopInv (s₀ : State) (k : Nat) (s : State) : Prop where
  bound : k ≤ 32
  shifted : (s.gpr .x0).toNat = (s₀.gpr .x0).toNat * 2 ^ k
  divisor : s.gpr .x1 = s₀.gpr .x1
  count : s.gpr .x15 = BitVec.ofNat 64 (32 - k)
  remainder : (s.gpr .x4).toNat < (s₀.gpr .x1).toNat
  equation : (s₀.gpr .x0).toNat / 2 ^ (32 - k) =
    (s.gpr .x5).toNat * (s₀.gpr .x1).toNat + (s.gpr .x4).toNat
  keeps : Keeps loopChanged s₀ s

theorem advance_ok (s : State) :
    WP isa (.block loopAdvance) s fun t =>
      t.gpr .x0 = s.gpr .x0 + s.gpr .x0 ∧ t.gpr .x15 = s.gpr .x15 - 1 ∧
      Keeps [.x0, .x15] s t := by
  apply WP.of_runBlock
  simp only [loopAdvance, runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    show 1 < 4096 from by decide,
    RegUpd.gpr_write, BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_, ?_⟩
  · rfl
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]
  all_goals rfl

/-- Bit 31 of the shifted numerator is the numerator's bit `31 - k`. -/
theorem shifted_bit (x : BitVec 64) (N k : Nat) (hk : k < 32) (hx : x.toNat = N * 2 ^ k) :
    (x.getLsbD 31).toNat = N / 2 ^ (31 - k) % 2 := by
  rw [← BitVec.testBit_toNat, Nat.toNat_testBit, hx,
    show 2 ^ 31 = 2 ^ (31 - k) * 2 ^ k by rw [← Nat.pow_add]; congr 1; omega,
    Nat.mul_div_mul_right _ _ (Nat.two_pow_pos k)]

theorem prefix_split (N k : Nat) (hk : k < 32) :
    N / 2 ^ (32 - (k + 1)) = 2 * (N / 2 ^ (32 - k)) + N / 2 ^ (31 - k) % 2 := by
  have h := Nat.mod_add_div (N / 2 ^ (31 - k)) 2
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ, show (31 - k).succ = 32 - k by omega] at h
  rw [show 32 - (k + 1) = 31 - k by omega]
  omega

theorem loopBody_ok (s₀ : State) (hn : (s₀.gpr .x0).toNat < 2 ^ 32)
    (hd : 0 < (s₀.gpr .x1).toNat) (hd' : (s₀.gpr .x1).toNat < 2 ^ 32)
    (k : Nat) (hk : k < 32) (s : State) (h : LoopInv s₀ k s) :
    WP isa loopBody s (LoopInv s₀ (k + 1)) := by
  have hqmul := Nat.le_mul_of_pos_right (s.gpr .x5).toNat hd
  have hprefix := Nat.div_le_self (s₀.gpr .x0).toNat (2 ^ (32 - k))
  have he := h.equation
  have hq : (s.gpr .x5).toNat < 2 ^ 32 := by omega
  have hr : (s.gpr .x4).toNat < 2 ^ 32 := Nat.lt_trans h.remainder hd'
  unfold loopBody
  refine WP.seq ((bit_ok s 31 (by decide) hr hq (by rw [h.divisor]; exact hd')).mono ?_)
  rintro a ⟨ha4, ha5, ka⟩
  refine (advance_ok a).mono ?_
  rintro t ⟨dbl, cnt, kt⟩
  have bit := shifted_bit (s.gpr .x0) (s₀.gpr .x0).toNat k hk h.shifted
  have hs := VG.Proof.Argon2.divide_step h.equation h.remainder
    (Bool.toNat_le ((s.gpr .x0).getLsbD 31))
  have a0 : a.gpr .x0 = s.gpr .x0 := ka.regs .x0 (by decide)
  have a1 : a.gpr .x1 = s.gpr .x1 := ka.regs .x1 (by decide)
  rw [h.divisor] at ha4 ha5
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have small : (s₀.gpr .x0).toNat * 2 ^ (k + 1) < 2 ^ 64 := by
      have : 2 ^ (k + 1) ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) (by omega)
      calc (s₀.gpr .x0).toNat * 2 ^ (k + 1) < 2 ^ 32 * 2 ^ 32 :=
            Nat.mul_lt_mul_of_lt_of_le hn this (Nat.two_pow_pos _)
        _ = 2 ^ 64 := by decide
    rw [Nat.pow_succ, ← Nat.mul_assoc] at small
    rw [dbl, a0, BitVec.toNat_add, h.shifted, Nat.mod_eq_of_lt (by omega), Nat.pow_succ,
      ← Nat.mul_assoc]
    omega
  · rw [kt.regs .x1 (by decide), a1, h.divisor]
  · rw [cnt, ka.regs .x15 (by decide), h.count,
      show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega)]
    congr 1
  · rw [kt.regs .x4 (by decide), ha4]; exact hs.2
  · rw [kt.regs .x4 (by decide), kt.regs .x5 (by decide), ha4, ha5, prefix_split _ k hk, ← bit]
    exact hs.1
  · exact h.keeps.trans ((ka.mono (by decide)).trans (kt.mono (by decide)))

theorem loopSetup_ok (s : State) (hn : (s.gpr .x0).toNat < 2 ^ 32) (hd : 0 < (s.gpr .x1).toNat) :
    WP isa (.block loopSetup) s (LoopInv s 0) := by
  apply WP.of_runBlock
  simp only [loopSetup, setup, List.cons_append, List.nil_append, runBlock_cons, runStep_some,
    runBlock_nil, exec, Size.bits, Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero,
    ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, Nat.pow_zero, Nat.mul_one]
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false]
  · simp only [RegUpd.gpr_write, ite_true]; rfl
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true]; exact hd
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true]
    change (s.gpr .x0).toNat / 2 ^ 32 = 0 * (s.gpr .x1).toNat + 0
    rw [Nat.div_eq_of_lt hn, Nat.zero_mul, Nat.zero_add]
  · constructor
    · intro r hr
      simp only [loopChanged, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_write, hr.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.2.2, ite_false]
    all_goals rfl

theorem loopCode_ok (s : State) (hn : (s.gpr .x0).toNat < 2 ^ 32)
    (hd : 0 < (s.gpr .x1).toNat) (hd' : (s.gpr .x1).toNat < 2 ^ 32) :
    WP isa loopCode s fun t =>
      (t.gpr .x5).toNat = (s.gpr .x0).toNat / (s.gpr .x1).toNat ∧
      (t.gpr .x4).toNat = (s.gpr .x0).toNat % (s.gpr .x1).toNat ∧
      Keeps loopChanged s t := by
  unfold loopCode
  refine WP.seq ((loopSetup_ok s hn hd).mono ?_)
  intro a ha
  refine (WP.loop (M := isa) (fun n u => ∃ k, n = 32 - k ∧ k < 32 ∧ LoopInv s k u) ?_ 32 a
    ⟨0, rfl, by decide, ha⟩)
  rintro n u ⟨k, rfl, hk, h⟩
  refine (loopBody_ok s hn hd hd' k hk u h).mono ?_
  intro t next
  have flag : eval (.nonzero .x .x15) t = some (decide (32 - (k + 1) ≠ 0)) := by
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, next.count]
    congr 1
    rw [Bool.eq_iff_iff, bne_iff_ne, decide_eq_true_iff, ne_eq, ne_eq]
    refine not_congr ⟨fun eq => ?_, fun eq => by rw [eq]; rfl⟩
    have num := congrArg BitVec.toNat eq
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 32 - (k + 1) < 2 ^ 64),
      show (0 : BitVec 64).toNat = 0 from rfl] using num
  by_cases done : k + 1 = 32
  · refine .inl ⟨?_, ?_⟩
    · simpa only [show 32 - (k + 1) = 0 by omega, ne_eq, not_true_eq_false, decide_false] using flag
    · have he := next.equation
      rw [done, Nat.sub_self, Nat.pow_zero, Nat.div_one] at he
      obtain ⟨hq, hr⟩ := VG.Proof.Argon2.divide_result hd he next.remainder
      exact ⟨hq, hr, next.keeps⟩
  · refine .inr ⟨?_, 32 - (k + 1), by omega, k + 1, rfl, by omega, next⟩
    change eval (.nonzero .x .x15) t = some true
    rw [flag]
    exact congrArg some (decide_eq_true (by omega : 32 - (k + 1) ≠ 0))

end VG.Proof.Argon2.AArch64.Divide
