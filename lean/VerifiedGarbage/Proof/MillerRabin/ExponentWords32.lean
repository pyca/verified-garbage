module

public import VerifiedGarbage.Proof.Mont.Words32

/-! # Native exponent words are digits of the represented integer -/

@[expose] public section
namespace VG.Proof.MillerRabin
open VG VG.Proof.Mont

def exponentWord (E i : Nat) : BitVec 32 := BitVec.ofNat 32 (E / 2 ^ (32 * i))

theorem val32_digit (m : Mem) (W : Addr) {d N i : Nat} (index : i < N) :
    val32 m W d N / 2 ^ (32 * i) % 2 ^ 32 = w32 m W (d + 4 * i) := by
  have positive : 0 < 2 ^ (32 * i) := Nat.two_pow_pos _
  have low := val32_lt m W d i
  rw [show N = i + (N - i) by omega, val32_append,
    Nat.add_mul_div_left _ _ positive, Nat.div_eq_of_lt low, Nat.zero_add,
    show N - i = (N - i - 1) + 1 by omega, val32, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (m.readW (off W (d + 4 * i)) 32).isLt

theorem read_exponentWord {m : Mem} {W : Addr} {d N i E : Nat}
    (value : val32 m W d N = E) (index : i < N) :
    m.readW (off W (d + 4 * i)) 32 = exponentWord E i := by
  apply BitVec.eq_of_toNat_eq
  change w32 m W (d + 4 * i) = (exponentWord E i).toNat
  rw [exponentWord, BitVec.toNat_ofNat, ← value, val32_digit m W index]

end VG.Proof.MillerRabin
