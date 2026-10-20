module
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Spec.Rsa
import VerifiedGarbage.Proof.Rsa.RecoverMath

/-! # Termination and result of public trailing-zero stripping -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.Spec.Rsa VG.Proof.Rsa

theorem factor_step {v : Nat} (pos : 0 < v) (even : v % 2 = 0) :
    0 < v / 2 ∧ (splitTwos v).1 = (splitTwos (v / 2)).1 + 1 ∧
      (splitTwos v).2 = (splitTwos (v / 2)).2 := by
  have eq := splitTwos_even (by omega) even
  exact ⟨by omega, by rw [eq], by rw [eq]⟩

theorem factor_terminal {v : Nat} (odd : v % 2 = 1) : (splitTwos v).1 = 0 ∧ (splitTwos v).2 = v := by
  rw [splitTwos_odd odd]
  exact ⟨rfl, rfl⟩
end VG.Proof.Dsa.X86.Generation
