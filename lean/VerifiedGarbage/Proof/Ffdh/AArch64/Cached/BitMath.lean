module

public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Comb
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.PowLit

/-! Width-guard and byte-extraction arithmetic for the public comb indices. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64

theorem sign_sub {a b : Nat} (ha : a<2^63) (hb : b<2^63) :
 ((BitVec.ofNat 64 a - BitVec.ofNat 64 b) >>> 63) =
 (if a<b then 1#64 else 0#64) := by
 apply BitVec.eq_of_toNat_eq
 simp only [BitVec.toNat_ushiftRight,BitVec.toNat_sub,BitVec.toNat_ofNat,Nat.shiftRight_eq_div_pow]
 rw [Nat.mod_eq_of_lt (by omega : a<2^64),Nat.mod_eq_of_lt (by omega : b<2^64)]
 split_ifs with h
 · change ((2^64-b+a)%2^64)/2^63=1
   rw [Nat.mod_eq_of_lt (by omega)]
   omega
 · change ((2^64-b+a)%2^64)/2^63=0
   have eq : 2^64-b+a=2^64+(a-b) := by omega
   rw [eq,Nat.add_mod_left,Nat.mod_eq_of_lt (by omega)]
   omega

theorem byte_bit : ∀ (b : Byte), ∀ n<8,
 ((BitVec.ofNat 64 b.toNat >>> n) &&& 1#64).toNat = b.toNat / 2^n % 2 := by
 decide +kernel

theorem mask_bits : ∀ n<8,
 (255#64 >>> (7-n)).toNat = 2^(n+1)-1 := by
 decide +kernel

end VG.Proof.Ffdh.AArch64.Cached
