module

public import VerifiedGarbage.Spec.Ffdh.VettedKeyGeneration
import VerifiedGarbage.Proof.Ffdh.KeyScalar
import Mathlib.Tactic.NormNum

/-! Exact vetted groups have scalar bounds exceeding their recommended widths. -/

@[expose] public section
namespace VG.Proof.Ffdh.VettedPolicy
open VG

private theorem recognized_properties {a : Spec.Ffdh.Parameters} {bits : Nat}
    (recognized : Spec.Ffdh.vettedExponentBits a = some bits) :
    bits ≤ 400 ∧ 2 ^ 400 < a.p := by
  have pow400 : (2 : Nat) ^ 400 = 2 ^ 200 * 2 ^ 200 := by
    rw [show (400 : Nat) = 200 + 200 from rfl, Nat.pow_add]
  rw [pow400]
  unfold Spec.Ffdh.vettedExponentBits at recognized
  split at recognized
  · cases recognized
  split at recognized
  · rename_i choice
    cases recognized
    have choices : a.p = Spec.Ffdh.modp2048Prime ∨ a.p = Spec.Ffdh.ffdhe2048Prime := by
      simpa only [Bool.or_eq_true, beq_iff_eq] using choice
    rcases choices with prime | prime <;> rw [prime] <;>
      norm_num [Spec.Ffdh.modp2048Prime, Spec.Ffdh.ffdhe2048Prime]
  split at recognized
  · rename_i choice
    cases recognized
    have choices : a.p = Spec.Ffdh.modp3072Prime ∨ a.p = Spec.Ffdh.ffdhe3072Prime := by
      simpa only [Bool.or_eq_true, beq_iff_eq] using choice
    rcases choices with prime | prime <;> rw [prime] <;>
      norm_num [Spec.Ffdh.modp3072Prime, Spec.Ffdh.ffdhe3072Prime]
  split at recognized
  · rename_i choice
    cases recognized
    have choices : a.p = Spec.Ffdh.modp4096Prime ∨ a.p = Spec.Ffdh.ffdhe4096Prime := by
      simpa only [Bool.or_eq_true, beq_iff_eq] using choice
    rcases choices with prime | prime <;> rw [prime] <;>
      norm_num [Spec.Ffdh.modp4096Prime, Spec.Ffdh.ffdhe4096Prime]
  split at recognized
  · rename_i choice
    cases recognized
    have choices : a.p = Spec.Ffdh.modp6144Prime ∨ a.p = Spec.Ffdh.ffdhe6144Prime := by
      simpa only [Bool.or_eq_true, beq_iff_eq] using choice
    rcases choices with prime | prime <;> rw [prime] <;>
      norm_num [Spec.Ffdh.modp6144Prime, Spec.Ffdh.ffdhe6144Prime]
  split at recognized
  · rename_i choice
    cases recognized
    have choices : a.p = Spec.Ffdh.modp8192Prime ∨ a.p = Spec.Ffdh.ffdhe8192Prime := by
      simpa only [Bool.or_eq_true, beq_iff_eq] using choice
    rcases choices with prime | prime <;> rw [prime] <;>
      norm_num [Spec.Ffdh.modp8192Prime, Spec.Ffdh.ffdhe8192Prime]
  cases recognized

theorem recognized_q {a : Spec.Ffdh.Parameters} {bits : Nat}
    (recognized : Spec.Ffdh.vettedExponentBits a = some bits) :
    a.q = none ∨ a.q = some ((a.p - 1) / 2) := by
  unfold Spec.Ffdh.vettedExponentBits at recognized
  split at recognized
  · cases recognized
  rename_i guard
  cases qeq : a.q with
  | none => exact Or.inl rfl
  | some q =>
    right
    simp only [qeq, Option.isSome_some, Bool.true_and, Bool.or_eq_true, bne_iff_ne] at guard
    by_contra different
    exact guard (Or.inr different)

private theorem half_bound {p n : Nat} (hp : 2 * n < p) : n ≤ p - 1 ∧ n ≤ (p - 1) / 2 := by
  omega

private theorem lower_bitLength {n x : Nat} (lower : 2 ^ n ≤ x) : n < Spec.RsaKeyGen.bitLength x := by
  have nonzero : x ≠ 0 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.two_pow_pos _) lower)
  have upper := (VG.Proof.Ffdh.KeyScalar.bitLength_bounds nonzero).2
  exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (Nat.lt_of_le_of_lt lower upper)

theorem recognized_le_bound {a : Spec.Ffdh.Parameters} {bits : Nat}
    (recognized : Spec.Ffdh.vettedExponentBits a = some bits) :
    bits ≤ Spec.RsaKeyGen.bitLength (Spec.Ffdh.scalarBound a) := by
  have properties := recognized_properties recognized
  have power : (2 : Nat) ^ 400 = 2 * 2 ^ 399 := by
    rw [show (400 : Nat) = 200 + 200 from rfl, Nat.pow_add,
      show (399 : Nat) = 200 + 199 from rfl, Nat.pow_add,
      show (200 : Nat) = 199 + 1 from rfl, Nat.pow_succ]
  have halves := half_bound (by rw [← power]; exact properties.2)
  have bound : 2 ^ 399 ≤ Spec.Ffdh.scalarBound a := by
    rcases recognized_q recognized with absent | present
    · simpa only [Spec.Ffdh.scalarBound, absent, Option.getD_none] using halves.1
    · simpa only [Spec.Ffdh.scalarBound, present, Option.getD_some] using halves.2
  have large := lower_bitLength bound
  exact Nat.le_trans properties.1 (Nat.succ_le_of_lt large)

theorem bits_of_recognized_uncapped {a : Spec.Ffdh.Parameters} {bits : Nat}
    (recognized : Spec.Ffdh.vettedExponentBits a = some bits) :
    Spec.Ffdh.generationScalarBits a = bits := by
  simp only [Spec.Ffdh.generationScalarBits, recognized, Nat.min_eq_left (recognized_le_bound recognized)]

end VG.Proof.Ffdh.VettedPolicy
