module

public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Mont.X86.Compact.Prepared
public import VerifiedGarbage.Proof.Rsa.MontContract

/-! # The prepared 64-bit contract implies native-word arithmetic conditions -/

@[expose] public section
namespace VG.Proof.Mont.X86.Compact
open VG VG.Proof.Mont VG.Proof.Rsa.Mont

theorem numAt_val32 (m : Mem) (W : Addr) (w j : Nat) :
    numAt m W w j = val32 m W (arrAt w j) (2 * w) := by
  unfold numAt
  rw [show 8 * w = 4 * (2 * w) by omega]
  exact VG.Proof.Bignum.read_eq_val32 m W (2 * w) (arrAt w j)

theorem val32_low (m : Mem) (W : Addr) (d : Nat) {n : Nat} (positive : 0 < n) :
    val32 m W d n % 2 ^ 32 = w32 m W d := by
  cases n with
  | zero => omega
  | succ n =>
    rw [val32, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt]
    exact (m.readW (off W d) 32).isLt

theorem inverse_low {u v : Nat} (h : (u * v + 1) % 2 ^ 64 = 0) :
    ((u % 2 ^ 32) * (v % 2 ^ 32) + 1) % 2 ^ 32 = 0 := by
  have low := congrArg (· % 2 ^ 32) h
  rw [Nat.mod_mod_of_dvd _ (by decide)] at low
  simpa only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod] using low

theorem prepared_inverse {m : Mem} {W : Addr} {w : Nat} (positive : 0 < w)
    (inverse : ((m.readW (W + BitVec.ofNat 64 (arrAt w aM)) 64).toNat *
      (wordAt m W minvWord).toNat + 1) % 2 ^ 64 = 0) :
    (val32 m W (arrAt w aM) (2 * w) * w32 m W 56 + 1) % 2 ^ 32 = 0 := by
  have h := inverse_low inverse
  have modulus : (m.readW (W + BitVec.ofNat 64 (arrAt w aM)) 64).toNat % 2 ^ 32 =
      w32 m W (arrAt w aM) := by
    change (m.read (off W (arrAt w aM)) (4 * 2)).toNat % 2 ^ 32 = _
    rw [VG.Proof.Bignum.read_eq_val32, val32_low _ _ _ (by decide)]
  rw [modulus, ← header_low m W minvWord] at h
  change (w32 m W (arrAt w aM) * w32 m W 56 + 1) % 2 ^ 32 = 0 at h
  have low := val32_low m W (arrAt w aM) (n := 2 * w) (by omega)
  simpa only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, low] using h

end VG.Proof.Mont.X86.Compact
