module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! The 8192-bit safe-prime budget is 2^32: its first decrement borrows
from the high word rather than treating the low word's zero as exhaustion. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Ffdh.Arm
open VG.Proof.X25519.Arm (Rest)

theorem decrementWords_ok (s : State) {n : Nat} (positive : 0 < n) (bound : n ≤ 2 ^ 32)
    (low : s.gpr .r9 = BitVec.ofNat 32 n)
    (high : s.gpr .r10 = BitVec.ofNat 32 (n / 2 ^ 32)) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterSearch.decrementWords) s fun t =>
      (t.gpr .r9 = BitVec.ofNat 32 (n - 1) ∧
        t.gpr .r10 = BitVec.ofNat 32 ((n - 1) / 2 ^ 32) ∧ t.mem = s.mem) ∧
        Rest [.r9, .r10, .r12] s t := by
  have lower : BitVec.ofNat 32 n - 1 = BitVec.ofNat 32 (n - 1) := by
    change BitVec.ofNat 32 n - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) positive]
  have noborrow : decide (1 ≤ (BitVec.ofNat 32 n).toNat) = decide (n < 2 ^ 32) := by
    by_cases small : n < 2 ^ 32
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
      simp only [show 1 ≤ n by omega, small, decide_true]
    · have full : n = 2 ^ 32 := by omega
      subst n
      rfl
  have upper : BitVec.ofNat 32 (n / 2 ^ 32) - 1 +
      (if n < 2 ^ 32 then 1 else 0) = BitVec.ofNat 32 ((n - 1) / 2 ^ 32) := by
    by_cases small : n < 2 ^ 32
    · rw [ite_eq_left small, Nat.div_eq_of_lt small,
        Nat.div_eq_of_lt (by omega : n - 1 < 2 ^ 32)]
      rfl
    · have full : n = 2 ^ 32 := by omega
      subst n
      rfl
  refine withRest [.r9, .r10, .r12] ?_ (by
    intro r hr op hop
    have checked : (instrs (.block VG.Impl.Ffdh.Arm.ParameterSearch.decrementWords : Prog isa)).all
        (fun op => !(clobbers op r)) = true := by
      cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have h := List.all_eq_true.mp checked op hop
    cases hc : clobbers op r <;> simp_all) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.decrementWords
  ffrun [low, high, lower, noborrow, upper,
    show (0 : BitVec 32) = 0#32 from rfl, BitVec.zero_add,
    show (1 : BitVec 32).toNat = 1 from rfl, decide_eq_true_eq]
  exact upper

theorem budgetGuard_ok (s : State) {n : Nat} (bound : n ≤ 2 ^ 32)
    (low : s.gpr .r9 = BitVec.ofNat 32 n)
    (high : s.gpr .r10 = BitVec.ofNat 32 (n / 2 ^ 32)) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterSearch.budgetGuard) s fun t =>
      (t.z = decide (n = 0) ∧ t.mem = s.mem) ∧ Rest [.r9] s t := by
  have zero : ((BitVec.ofNat 32 n ||| BitVec.ofNat 32 (n / 2 ^ 32)) == (0 : BitVec 32)) =
      decide (n = 0) := by
    by_cases small : n < 2 ^ 32
    · rw [Nat.div_eq_of_lt small]
      change ((BitVec.ofNat 32 n ||| 0#32) == (0 : BitVec 32)) = _
      rw [BitVec.or_zero, VG.Proof.X25519.Arm.ofNat_beq_zero small]
    · have full : n = 2 ^ 32 := by omega
      subst n
      rfl
  refine withRest [.r9] ?_ (by
    intro r hr op hop
    have checked : (instrs (.block VG.Impl.Ffdh.Arm.ParameterSearch.budgetGuard : Prog isa)).all
        (fun op => !(clobbers op r)) = true := by
      cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have h := List.all_eq_true.mp checked op hop
    cases hc : clobbers op r <;> simp_all) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.budgetGuard
  ffrun [low, high, show (0 : BitVec 32) = 0#32 from rfl, BitVec.sub_zero]
  exact zero

end VG.Proof.Ffdh.Arm.ParameterSearch
