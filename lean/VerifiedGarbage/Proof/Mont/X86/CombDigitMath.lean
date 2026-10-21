module

public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Rsa.FixedBaseCombShift
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Rsa.FixedBaseComb

/-! Read a fixed-position comb bit through its containing 32-bit word. -/

@[expose] public section
namespace VG.Proof.Mont.X86.Comb
open VG VG.Proof.Mont
open VG.Proof.Rsa.FixedBaseComb

theorem val32_word {m : Mem} {base : Addr} {o k j : Nat} (hj : j<k) :
    val32 m base o k / 2^(32*j) % 2^32 = w32 m base (o+4*j) := by
  have split : k=j+(k-j) := by omega
  rw [split,val32_append]
  rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),Nat.div_eq_of_lt (val32_lt _ _ _ _),Nat.zero_add]
  have tail : k-j=(k-j-1)+1 := by omega
  rw [tail,val32]
  have wordLt : w32 m base (o+4*j)<2^32 := (m.readW (off base (o+4*j)) 32).isLt
  rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt wordLt]

theorem word_bit {m : Mem} {base : Addr} {o k p : Nat} (hp : p<32*k) :
    bit (w32 m base (o+4*(p/32))) (p%32) = bit (val32 m base o k) p := by
  rw [←val32_word (by omega : p/32<k)]
  have hrem : p%32<32 := Nat.mod_lt _ (by decide)
  have width : 2^32=2^(p%32)*2^(32-p%32) := by
    rw [←Nat.pow_add]; congr 1; omega
  unfold bit
  rw [width,Nat.mod_mul_right_div_self]
  rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega : 1≤32-p%32))]
  rw [Nat.div_div_eq_div_mul,←Nat.pow_add]
  congr 2
  exact congrArg (2^·) (Nat.div_add_mod p 32)

end VG.Proof.Mont.X86.Comb
