module

public import VerifiedGarbage.Proof.RsaKeyGen.Table
public import VerifiedGarbage.Proof.Framework.PowLit

/-!
# A candidate for an RSA prime: trial division by 16-bit halves

For 32-bit targets, trial division reduces the candidate `c` by Montgomery
reduction of its 16-bit halves, `acc := (acc + h) 2^(−16) mod s`
(`redc16_math`), with `−s⁻¹ mod 2^16` from three steps of Newton's
iteration on 32-bit words (`ninv`, `ninv_tab` for every entry of the
table): after a 32-bit word `x`, `acc 2^32 ≡ x + acc` (`trial_word16`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen

open VG.Impl.RsaKeyGen

/-- One step of Newton's iteration for `s⁻¹`, on 32-bit words. -/
def nstep (s x : BitVec 32) : BitVec 32 := x * (2 - s * x)

/-- `−s⁻¹ mod 2^16` for an odd `s`, as the 32-bit code computes it. -/
def ninv (s : BitVec 32) : BitVec 32 := ((0 - nstep s (nstep s (nstep s s))) <<< 16) >>> 16

theorem ninv_lt (s : BitVec 32) : (ninv s).toNat < 2 ^ 16 := by
  unfold ninv
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := (((0 - nstep s (nstep s (nstep s s))) <<< 16)).isLt
  omega

theorem slots_ninv : slots.all (fun s => (s * (ninv (BitVec.ofNat 32 s)).toNat + 1) % 2 ^ 16 == 0) = true := by
  unfold slots; rw [primes.lit_eq]; decide +kernel

/-- `ninv` of every entry of the table is `−s⁻¹ mod 2^16`. -/
theorem ninv_tab {i : Nat} (hi : i < 1024) :
    (tabEntry i * (ninv (BitVec.ofNat 32 (tabEntry i))).toNat + 1) % 2 ^ 16 = 0 := by
  have h := List.all_eq_true.mp slots_ninv (slots[i]'(by rw [slots_length]; exact hi)) (List.getElem_mem _)
  simp only [beq_iff_eq] at h
  have : tabEntry i = slots[i]'(by rw [slots_length]; exact hi) := by
    unfold tabEntry; exact getD_of_lt _
  rw [this]; exact h

/-- Montgomery reduction by `2^16` modulo `s`, with `sv = −s⁻¹ mod 2^16`, of
`X < s 2^16`: exact, below `2 s`, and `X 2^(−16) mod s`. -/
theorem redc16_math {X s sv : Nat} (hinv : (s * sv + 1) % 2 ^ 16 = 0) (hX : X < s * 2 ^ 16) :
    (X + X * sv % 2 ^ 16 * s) % 2 ^ 16 = 0 ∧
    (X + X * sv % 2 ^ 16 * s) / 2 ^ 16 < 2 * s ∧
    ((X + X * sv % 2 ^ 16 * s) / 2 ^ 16 * 2 ^ 16) % s = X % s := by
  have hd : (X + X * sv % 2 ^ 16 * s) % 2 ^ 16 = 0 := by
    have h16 : 2 ^ 16 ∣ s * sv + 1 := Nat.dvd_of_mod_eq_zero hinv
    have hq := Nat.div_add_mod (X * sv) (2 ^ 16)
    have : X + X * sv % 2 ^ 16 * s + 2 ^ 16 * (X * sv / 2 ^ 16) * s = X * (s * sv + 1) := by
      rw [Nat.add_assoc, ← Nat.add_mul, Nat.add_comm (X * sv % 2 ^ 16), hq, Nat.mul_add, Nat.mul_one,
        Nat.add_comm, Nat.mul_assoc, Nat.mul_comm sv s]
    have h2 : 2 ^ 16 ∣ X + X * sv % 2 ^ 16 * s + 2 ^ 16 * (X * sv / 2 ^ 16) * s := by
      rw [this]; exact Nat.dvd_mul_left_of_dvd h16 X
    have h3 : 2 ^ 16 ∣ 2 ^ 16 * (X * sv / 2 ^ 16) * s := Nat.dvd_mul_right_of_dvd (Nat.dvd_mul_right _ _) _
    exact Nat.mod_eq_zero_of_dvd ((Nat.dvd_add_right h3).mp (by rwa [Nat.add_comm] at h2))
  have hu : X * sv % 2 ^ 16 < 2 ^ 16 := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hexact : (X + X * sv % 2 ^ 16 * s) / 2 ^ 16 * 2 ^ 16 = X + X * sv % 2 ^ 16 * s := by
    have := Nat.div_add_mod (X + X * sv % 2 ^ 16 * s) (2 ^ 16)
    rw [hd, Nat.add_zero, Nat.mul_comm] at this; exact this
  refine ⟨hd, ?_, ?_⟩
  · have hus : X * sv % 2 ^ 16 * s < 2 ^ 16 * s := Nat.mul_lt_mul_of_pos_right hu (by
      rcases Nat.eq_zero_or_pos s with h | h
      · rw [h, Nat.zero_mul] at hX; omega
      · exact h)
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
    rw [Nat.mul_comm s (2 ^ 16)] at hX
    calc X + X * sv % 2 ^ 16 * s < 2 ^ 16 * s + 2 ^ 16 * s := Nat.add_lt_add hX hus
      _ = 2 * s * 2 ^ 16 := by rw [← Nat.two_mul, Nat.mul_comm (2 ^ 16) s, ← Nat.mul_assoc]
  · rw [hexact, Nat.add_mul_mod_self_right]

/-- Two reductions of a 32-bit word's halves: `acc 2^(32 j) ≡ c_j` carries on
to `j + 1` words. -/
theorem trial_word16 {s acc r1 r2 x V j : Nat} (h1 : r1 * 2 ^ 16 % s = (x % 2 ^ 16 + acc) % s)
    (h2 : r2 * 2 ^ 16 % s = (x / 2 ^ 16 + r1) % s) (hV : acc * 2 ^ (32 * j) % s = V % s) :
    r2 * 2 ^ (32 * (j + 1)) % s = (V + 2 ^ (32 * j) * x) % s := by
  have mr : ∀ {a b : Nat} (c : Nat), a % s = b % s → a * c % s = b * c % s := fun c h => by
    rw [Nat.mul_mod, h, ← Nat.mul_mod]
  have ml : ∀ {a b : Nat} (c : Nat), a % s = b % s → (c + a) % s = (c + b) % s := fun c h => by
    rw [Nat.add_mod, h, ← Nat.add_mod]
  have e3 : r2 * 2 ^ 32 % s = (x + acc) % s := by
    have : r2 * 2 ^ 32 = r2 * 2 ^ 16 * 2 ^ 16 := by rw [Nat.mul_assoc, ← Nat.pow_add]
    rw [this, ← Nat.mod_mul_mod, h2, Nat.mod_mul_mod, Nat.add_mul, ml _ h1, ← Nat.add_assoc,
      Nat.mul_comm (x / 2 ^ 16), Nat.add_comm (2 ^ 16 * (x / 2 ^ 16)), Nat.mod_add_div]
  have : r2 * 2 ^ (32 * (j + 1)) = r2 * 2 ^ 32 * 2 ^ (32 * j) := by
    rw [Nat.mul_assoc, ← Nat.pow_add]; congr 2; omega
  rw [this, mr _ e3, Nat.add_mul, ml _ hV, Nat.add_comm, Nat.mul_comm x]

end VG.Proof.RsaKeyGen
