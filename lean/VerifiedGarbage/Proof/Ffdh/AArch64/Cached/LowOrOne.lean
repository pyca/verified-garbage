module

public import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Ffdh.AArch64.Checks
import VerifiedGarbage.Proof.Framework.Omega

/-! Setting the low bit of a multiword value preserves all its higher bits. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.Proof.Bignum

theorem wv_low_or_one (m : Mem) (B : Addr) {d w : Nat} (positive : 0<w) (fit : d+8*w≤2^64) :
 wv (m.writeW (off B d) (word m B d ||| 1#64)) B d w=2*(wv m B d w/2)+1 := by
 have low := wv_mod64 m B d (by omega : 1≤w)
 have mod2 : (word m B d).toNat%2=wv m B d w%2 := by omega
 have split (m : Mem) : wv m B d w=(word m B d).toNat+2^64*wv m B (d+8) (w-1) := by
  have h := wv_add m B d 1 (w-1)
  rw [show 1+(w-1)=w by omega] at h
  simpa only [wv,Nat.mul_zero,Nat.pow_zero,Nat.mul_one,Nat.one_mul,Nat.add_zero,Nat.zero_add,Nat.reduceMul,Nat.reducePow] using h
 have frame := writeW_outside m B (word m B d ||| 1#64) (by omega : d+8≤2^64)
 have orValue := VG.Proof.Ffdh.AArch64.or1_toNat (word m B d)
 change (word m B d ||| 1#64).toNat=(word m B d).toNat+(1-(word m B d).toNat%2) at orValue
 rw [split,word_writeW_self,orValue,
  frame.wv (Or.inr (by omega : d+8≤d+8)) (by omega)]
 have original := split m
 omega

end VG.Proof.Ffdh.AArch64.Cached
