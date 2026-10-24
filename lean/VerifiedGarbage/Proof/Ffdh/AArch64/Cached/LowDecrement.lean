module

public import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Framework.Omega

/-! An odd modulus permits p−1 by decrementing only its low limb, without a borrow. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.Proof.Bignum

theorem wv_low_decrement (m : Mem) (B : Addr) {d w : Nat} (positive : 0<w)
 (fit : d+8*w≤2^64) (odd : wv m B d w%2=1) :
 wv (m.writeW (off B d) (word m B d-1#64)) B d w=wv m B d w-1 := by
 have low := wv_mod64 m B d (by omega : 1≤w)
 have positiveLow : 0<(word m B d).toNat := by
  have : wv m B d w%2^64%2=1 := by omega
  rw [low] at this
  omega
 have sub : (word m B d-1#64).toNat=(word m B d).toNat-1 := by
  simp only [BitVec.toNat_sub,show (1#64).toNat=1 from rfl]
  have := (word m B d).isLt
  omega
 have split (m : Mem) : wv m B d w= (word m B d).toNat + 2^64*wv m B (d+8) (w-1) := by
  have h := wv_add m B d 1 (w-1)
  rw [show 1+(w-1)=w by omega] at h
  simpa only [wv,Nat.mul_zero,Nat.pow_zero,Nat.mul_one,Nat.one_mul,Nat.add_zero,Nat.zero_add,Nat.reduceMul,Nat.reducePow] using h
 have frame := writeW_outside m B (word m B d-1#64) (by omega : d+8≤2^64)
 rw [split,word_writeW_self,sub,frame.wv (Or.inr (by omega : d+8≤d+8)) (by omega),split]
 omega

end VG.Proof.Ffdh.AArch64.Cached
