module

public import VerifiedGarbage.Proof.Rsa.FixedBaseComb

/-! Fixed-position extraction from a shifted, zero-padded comb exponent. -/

@[expose] public section
namespace VG.Proof.Rsa.FixedBaseComb
open VG.Spec.Rsa.FixedBaseComb (rows)

theorem bit_mod_width (x width position : Nat) (h : position < width) :
    bit (x % 2^width) position = bit x position := by
  have power : 2^width = 2^position * 2^(width-position) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  unfold bit
  rw [power, Nat.mod_mul_right_div_self]
  apply Nat.mod_mod_of_dvd
  change 2^1 ∣ 2^(width-position)
  exact Nat.pow_dvd_pow 2 (show 1 ≤ width-position by omega)

theorem bit_shift_up (x shift position : Nat) (h : shift ≤ position) :
    bit (x * 2^shift) position = bit x (position-shift) := by
  have power : 2^position = 2^(position-shift) * 2^shift := by
    rw [← Nat.pow_add]
    congr 1
    omega
  unfold bit
  rw [power, Nat.mul_div_mul_right x (2^(position-shift)) (Nat.two_pow_pos shift)]

/-- All five fixed extraction positions read the intended original row,
including the extra zero bits in the 224- and 256-bit schedules. -/
theorem shifted_tooth (bits x width row tooth : Nat)
    (hr : row < rows bits) (ht : tooth < 5) (hw : 5*rows bits ≤ width) :
    bit ((x * 2^(rows bits-1-row)) % 2^width) ((tooth+1)*rows bits-1) =
      bit x (row + tooth*rows bits) := by
  have dpos : 0 < rows bits := by omega
  have bound : (tooth+1)*rows bits ≤ 5*rows bits :=
    Nat.mul_le_mul_right _ (by omega)
  have low : rows bits ≤ (tooth+1)*rows bits := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (rows bits) (show 1 ≤ tooth+1 by omega)
  rw [bit_mod_width _ _ _ (by omega), bit_shift_up _ _ _ (by omega)]
  congr 1
  rw [Nat.add_mul, Nat.one_mul]
  omega

end VG.Proof.Rsa.FixedBaseComb
