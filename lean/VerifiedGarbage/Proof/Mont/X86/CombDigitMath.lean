module

public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Rsa.FixedBaseComb
import VerifiedGarbage.Proof.Framework.Omega

/-! ### `Rsa.FixedBaseCombShift`, which this module and modules that import it used -/

section

/-! Fixed-position extraction from a shifted, zero-padded comb exponent. -/

@[expose] public section
namespace VG.Proof.Rsa.FixedBaseComb
open VG.Spec.Rsa.FixedBaseComb (rows)

theorem bit_mod_width (x width position : Nat) (h : position < width) :
    bit (x % 2^width) position = bit x position := by
  have power : 2^width = 2^position * 2^(width-position) := by
    rw [← Nat.pow_add]
    congr 1
    omega_using [h]
  unfold bit
  rw [power, Nat.mod_mul_right_div_self]
  apply Nat.mod_mod_of_dvd
  change 2^1 ∣ 2^(width-position)
  exact Nat.pow_dvd_pow 2 (show 1 ≤ width-position by omega_using [h])

theorem bit_shift_up (x shift position : Nat) (h : shift ≤ position) :
    bit (x * 2^shift) position = bit x (position-shift) := by
  have power : 2^position = 2^(position-shift) * 2^shift := by
    rw [← Nat.pow_add]
    congr 1
    omega_using [h]
  unfold bit
  rw [power, Nat.mul_div_mul_right x (2^(position-shift)) (Nat.two_pow_pos shift)]

/-- All five fixed extraction positions read the intended original row,
including the extra zero bits in the 224- and 256-bit schedules. -/
theorem shifted_tooth (bits x width row tooth : Nat)
    (hr : row < rows bits) (ht : tooth < 5) (hw : 5*rows bits ≤ width) :
    bit ((x * 2^(rows bits-1-row)) % 2^width) ((tooth+1)*rows bits-1) =
      bit x (row + tooth*rows bits) := by
  have dpos : 0 < rows bits := by omega_using [hr]
  have bound : (tooth+1)*rows bits ≤ 5*rows bits :=
    Nat.mul_le_mul_right _ (by omega_using [ht])
  have low : rows bits ≤ (tooth+1)*rows bits := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (rows bits) (show 1 ≤ tooth+1 by omega_using [])
  rw [bit_mod_width _ _ _ (by omega_using [hr, hw, bound]), bit_shift_up _ _ _ (by omega_using [low])]
  congr 1
  rw [Nat.add_mul, Nat.one_mul]
  omega_using [hr]

end VG.Proof.Rsa.FixedBaseComb

end

end

/-! Read a fixed-position comb bit through its containing 32-bit word. -/

@[expose] public section
namespace VG.Proof.Mont.X86.Comb
open VG VG.Proof.Mont
open VG.Proof.Rsa.FixedBaseComb

theorem val32_word {m : Mem} {base : Addr} {o k j : Nat} (hj : j<k) :
    val32 m base o k / 2^(32*j) % 2^32 = w32 m base (o+4*j) := by
  have split : k=j+(k-j) := by omega_using [hj]
  rw [split,val32_append]
  rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),Nat.div_eq_of_lt (val32_lt _ _ _ _),Nat.zero_add]
  have tail : k-j=(k-j-1)+1 := by omega_using [hj]
  rw [tail,val32]
  have wordLt : w32 m base (o+4*j)<2^32 := (m.readW (off base (o+4*j)) 32).isLt
  rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt wordLt]

theorem word_bit {m : Mem} {base : Addr} {o k p : Nat} (hp : p<32*k) :
    bit (w32 m base (o+4*(p/32))) (p%32) = bit (val32 m base o k) p := by
  rw [←val32_word (by omega_using [hp] : p/32<k)]
  have hrem : p%32<32 := Nat.mod_lt _ (by decide)
  have width : 2^32=2^(p%32)*2^(32-p%32) := by
    rw [←Nat.pow_add]; congr 1; omega_using []
  unfold bit
  rw [width,Nat.mod_mul_right_div_self]
  rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega_using [] : 1≤32-p%32))]
  rw [Nat.div_div_eq_div_mul,←Nat.pow_add]
  congr 2
  exact congrArg (2^·) (Nat.div_add_mod p 32)

end VG.Proof.Mont.X86.Comb
