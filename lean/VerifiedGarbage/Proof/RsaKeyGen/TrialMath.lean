import VerifiedGarbage.Proof.RsaKeyGen.Table
import Mathlib.Data.Nat.ModEq
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# A candidate for an RSA prime: trial division's arithmetic

For each prime `s` of the table, the implementations reduce the candidate
`c` by Montgomery reduction of its 32-bit halves, `acc := (acc + h) 2^(−32)
mod s` (`redc_math`): after all its words, `acc < 2 s` and
`acc 2^(64 w) ≡ c (mod s)` (`trial_word_math`), so `s` divides `c` iff
`acc` is 0 or `s` (`trial_div`). `tabWord_entry`: the entries of a word of
the table.
-/

namespace VG.Proof.RsaKeyGen

open VG.Impl.RsaKeyGen

/-- Montgomery reduction by `2^32` modulo the odd `s`, with `sv = −s⁻¹ mod
2^64`, of `X < s 2^32`: exact, below `2 s`, and `X 2^(−32) mod s`. -/
theorem redc_math {X s sv : Nat} (hinv : (s * sv + 1) % 2 ^ 64 = 0) (hX : X < s * 2 ^ 32) :
    (X + X * sv % 2 ^ 64 % 2 ^ 32 * s) % 2 ^ 32 = 0 ∧
    (X + X * sv % 2 ^ 64 % 2 ^ 32 * s) / 2 ^ 32 < 2 * s ∧
    ((X + X * sv % 2 ^ 64 % 2 ^ 32 * s) / 2 ^ 32 * 2 ^ 32) % s = X % s := by
  have hm : X * sv % 2 ^ 64 % 2 ^ 32 = X * sv % 2 ^ 32 :=
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by decide))
  rw [hm]
  have hd : (X + X * sv % 2 ^ 32 * s) % 2 ^ 32 = 0 := by
    have h64 : 2 ^ 32 ∣ s * sv + 1 :=
      Nat.dvd_trans (Nat.pow_dvd_pow 2 (by decide)) (Nat.dvd_of_mod_eq_zero hinv)
    have hq := Nat.div_add_mod (X * sv) (2 ^ 32)
    have : X + X * sv % 2 ^ 32 * s + 2 ^ 32 * (X * sv / 2 ^ 32) * s = X * (s * sv + 1) := by
      rw [Nat.add_assoc, ← Nat.add_mul, Nat.add_comm (X * sv % 2 ^ 32), hq, Nat.mul_add, Nat.mul_one,
        Nat.add_comm, Nat.mul_assoc, Nat.mul_comm sv s]
    have h2 : 2 ^ 32 ∣ X + X * sv % 2 ^ 32 * s + 2 ^ 32 * (X * sv / 2 ^ 32) * s := by
      rw [this]; exact Nat.dvd_mul_left_of_dvd h64 X
    have h3 : 2 ^ 32 ∣ 2 ^ 32 * (X * sv / 2 ^ 32) * s := Nat.dvd_mul_right_of_dvd (Nat.dvd_mul_right _ _) _
    exact Nat.mod_eq_zero_of_dvd ((Nat.dvd_add_right h3).mp (by rwa [Nat.add_comm] at h2))
  have hu : X * sv % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hexact : (X + X * sv % 2 ^ 32 * s) / 2 ^ 32 * 2 ^ 32 = X + X * sv % 2 ^ 32 * s := by
    have := Nat.div_add_mod (X + X * sv % 2 ^ 32 * s) (2 ^ 32)
    rw [hd, Nat.add_zero, Nat.mul_comm] at this; exact this
  refine ⟨hd, ?_, ?_⟩
  · have hus : X * sv % 2 ^ 32 * s < 2 ^ 32 * s := Nat.mul_lt_mul_of_pos_right hu (by
      rcases Nat.eq_zero_or_pos s with h | h
      · rw [h, Nat.zero_mul] at hX; omega
      · exact h)
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
    rw [Nat.mul_comm s (2 ^ 32)] at hX
    calc X + X * sv % 2 ^ 32 * s < 2 ^ 32 * s + 2 ^ 32 * s := Nat.add_lt_add hX hus
      _ = 2 * s * 2 ^ 32 := by rw [← Nat.two_mul, Nat.mul_comm (2 ^ 32) s, ← Nat.mul_assoc]
  · rw [hexact, Nat.add_mul_mod_self_right]

/-- Two reductions of a word's halves: `acc 2^(64 j) ≡ c_j` carries on to
`j + 1` words. -/
theorem trial_word_math {s acc r1 r2 x V j : Nat} (h1 : r1 * 2 ^ 32 % s = (x % 2 ^ 32 + acc) % s)
    (h2 : r2 * 2 ^ 32 % s = (x / 2 ^ 32 + r1) % s) (hV : acc * 2 ^ (64 * j) % s = V % s) :
    r2 * 2 ^ (64 * (j + 1)) % s = (V + 2 ^ (64 * j) * x) % s := by
  have e1 : r1 * 2 ^ 32 ≡ x % 2 ^ 32 + acc [MOD s] := h1
  have e2 : r2 * 2 ^ 32 ≡ x / 2 ^ 32 + r1 [MOD s] := h2
  have eV : acc * 2 ^ (64 * j) ≡ V [MOD s] := hV
  have e3 : r2 * 2 ^ 64 ≡ x + acc [MOD s] := by
    have : r2 * 2 ^ 64 = r2 * 2 ^ 32 * 2 ^ 32 := by rw [Nat.mul_assoc, ← Nat.pow_add]
    rw [this]
    refine (e2.mul_right (2 ^ 32)).trans ?_
    rw [Nat.add_mul]
    refine (Nat.ModEq.add_left _ e1).trans ?_
    rw [← Nat.add_assoc, Nat.mul_comm (x / 2 ^ 32), Nat.add_comm (2 ^ 32 * (x / 2 ^ 32)), Nat.mod_add_div]
  have : r2 * 2 ^ (64 * (j + 1)) = r2 * 2 ^ 64 * 2 ^ (64 * j) := by
    rw [Nat.mul_assoc, ← Nat.pow_add]; congr 2; omega
  rw [this]
  show r2 * 2 ^ 64 * 2 ^ (64 * j) ≡ V + 2 ^ (64 * j) * x [MOD s]
  refine (e3.mul_right _).trans ?_
  rw [Nat.add_mul, Nat.add_comm]
  exact (eV.add_right _).trans (by rw [Nat.mul_comm x])

/-- `s` divides `c` iff `acc ∈ {0, s}`, for `acc < 2 s` with
`acc 2^(64 w) ≡ c (mod s)` and `s` odd. -/
theorem trial_div {acc c sp w : Nat} (hodd : sp % 2 = 1) (hacc : acc < 2 * sp)
    (h : acc * 2 ^ (64 * w) % sp = c % sp) : c % sp = 0 ↔ acc = 0 ∨ acc = sp := by
  have hcop : Nat.Coprime sp (2 ^ (64 * w)) := by
    apply Nat.Coprime.pow_right
    show Nat.gcd sp 2 = 1
    rw [Nat.gcd_comm, Nat.gcd_rec, hodd]; rfl
  rw [← h]
  constructor
  · intro h0
    have hd : sp ∣ acc := hcop.dvd_of_dvd_mul_right (Nat.dvd_of_mod_eq_zero h0)
    obtain ⟨q, hq⟩ := hd
    rcases q with _ | _ | q
    · left; rw [hq, Nat.mul_zero]
    · right; rw [hq, Nat.mul_one]
    · exfalso; rw [hq] at hacc
      have : sp * 2 ≤ sp * (q + 1 + 1) := Nat.mul_le_mul_left _ (by omega)
      omega
  · rintro (rfl | rfl)
    · simp
    · exact Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_right _ _)

/-- A table word's entries. -/
theorem tabWord_entry {i j : Nat} (hi : i < 256) (hj : j < 4) :
    ((BitVec.ofNat 64 (tabWord i) >>> (16 * j)) &&& 0xFFFF).toNat = tabEntry (4 * i + j) := by
  have e0 := (tabEntry_facts (i := 4 * i) (by omega)).2.2
  have e1 := (tabEntry_facts (i := 4 * i + 1) (by omega)).2.2
  have e2 := (tabEntry_facts (i := 4 * i + 2) (by omega)).2.2
  have e3 := (tabEntry_facts (i := 4 * i + 3) (by omega)).2.2
  have hlt : tabWord i < 2 ^ 64 := by unfold tabWord; omega
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt,
    show (0xFFFF : BitVec 64).toNat = 2 ^ 16 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  unfold tabWord
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;>
    simp only [Nat.reduceMul, Nat.reducePow, Nat.div_one, Nat.add_zero] <;> omega

end VG.Proof.RsaKeyGen
