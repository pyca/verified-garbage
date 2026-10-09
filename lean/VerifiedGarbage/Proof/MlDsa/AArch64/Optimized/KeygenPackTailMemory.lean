import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackStreamMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackTail

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64 VG.Proof.MlDsa.Pack

theorem slice_word (G base sh w : Nat) (h : sh+w≤64) :
    ((BitVec.ofNat 64 (G/2^base))>>>sh).setWidth w=BitVec.ofNat w (G/2^(base+sh)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth,BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow,VG.Proof.MlKem.mod_pow_div_mod _ h,
    Nat.div_div_eq_div_mul,←Nat.pow_add,BitVec.toNat_ofNat]

theorem narrow_word (G base w : Nat) (h : w≤64) :
    (BitVec.ofNat 64 (G/2^base)).setWidth w=BitVec.ofNat w (G/2^base) := by
  simpa only [BitVec.ushiftRight_zero,Nat.add_zero] using slice_word G base 0 w (by omega)

theorem smallWord_byte (G k n : Nat) {j : Nat} (hj : j<n) :
    (BitVec.ofNat (8*n) (G/2^(8*k))).extractLsb' (8*j) 8=byteOf G (k+j) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat,BitVec.toNat_ofNat,Nat.shiftRight_eq_div_pow,
    VG.Proof.MlKem.mod_pow_div_mod _ (by omega),Nat.div_div_eq_div_mul,←Nat.pow_add,←Nat.mul_add]
  rfl

theorem written_small (G k n : Nat) (m : Mem) (out : Addr) :
    Written m (m.writeW out (BitVec.ofNat (8*n) (G/2^(8*k)))) out n (fun j=>byteOf G (k+j)) :=
  (written_word m out n _).congr fun _j hj=>smallWord_byte G k n hj


theorem narrow_zero (G w : Nat) (h : w≤64) :
    (BitVec.ofNat 64 G).setWidth w=BitVec.ofNat w G := by
  simpa only [Nat.pow_zero,Nat.div_one] using narrow_word G 0 w h

theorem slice_zero (G sh w : Nat) (h : sh+w≤64) :
    ((BitVec.ofNat 64 G)>>>sh).setWidth w=BitVec.ofNat w (G/2^sh) := by
  simpa only [Nat.pow_zero,Nat.div_one,Nat.zero_add] using slice_word G 0 sh w h

theorem tail_written (nb G : Nat) (hn : TailWidth nb) (m : Mem) (out : Addr) :
    Written m (tailResult nb m out (BitVec.ofNat 64 G)).1
      (out+BitVec.ofNat 64 (nb/8*8)) (nb%8) (byteOf G) := by
  rcases hn with rfl|rfl|rfl|rfl|rfl
  · simp [tailResult]
    rw [slice_zero G 8 8 (by decide),slice_zero G 16 8 (by decide)]
    have h0 := written_small G 0 1 (m) (out+BitVec.ofNat 64 0)
    simp only [Nat.mul_zero,Nat.pow_zero,Nat.div_one,Nat.zero_add] at h0
    have h1 := written_small G 1 1 ((m).writeW (out+BitVec.ofNat 64 0) (BitVec.ofNat 8 G)) ((out+BitVec.ofNat 64 0)+BitVec.ofNat 64 1)
    have p1 := written_append h0 h1 (by decide)
    have h2 := written_small G 2 1 (((m).writeW (out+BitVec.ofNat 64 0) (BitVec.ofNat 8 G)).writeW ((out+BitVec.ofNat 64 0)+BitVec.ofNat 64 1) (BitVec.ofNat 8 (G/2^8))) ((out+BitVec.ofNat 64 0)+BitVec.ofNat 64 2)
    have p2 := written_append p1 h2 (by decide)
    simpa only [BitVec.add_assoc,BitVec.add_zero] using p2
  · simp [tailResult, BitVec.add_assoc, ←BitVec.shiftRight_add]
    rw [slice_zero G 32 8 (by decide),slice_zero G 40 8 (by decide)]
    have h0 := written_small G 0 4 (m) (out+BitVec.ofNat 64 0)
    simp only [Nat.mul_zero,Nat.pow_zero,Nat.div_one,Nat.zero_add] at h0
    have h1 := written_small G 4 1 ((m).writeW (out+BitVec.ofNat 64 0) (BitVec.ofNat 32 G)) ((out+BitVec.ofNat 64 0)+BitVec.ofNat 64 4)
    have p1 := written_append h0 h1 (by decide)
    have h2 := written_small G 5 1 (((m).writeW (out+BitVec.ofNat 64 0) (BitVec.ofNat 32 G)).writeW ((out+BitVec.ofNat 64 0)+BitVec.ofNat 64 4) (BitVec.ofNat 8 (G/2^32))) ((out+BitVec.ofNat 64 0)+BitVec.ofNat 64 5)
    have p2 := written_append p1 h2 (by decide)
    simpa only [BitVec.add_assoc,BitVec.add_zero] using p2
  · simp [tailResult]
    have h0 := written_small G 0 1 (m) (out+BitVec.ofNat 64 8)
    simp only [Nat.mul_zero,Nat.pow_zero,Nat.div_one,Nat.zero_add] at h0
    simpa only [BitVec.add_assoc,BitVec.add_zero] using h0
  · simp [tailResult, BitVec.add_assoc]
    rw [slice_zero G 8 8 (by decide)]
    have h0 := written_small G 0 1 (m) (out+BitVec.ofNat 64 8)
    simp only [Nat.mul_zero,Nat.pow_zero,Nat.div_one,Nat.zero_add] at h0
    have h1 := written_small G 1 1 ((m).writeW (out+BitVec.ofNat 64 8) (BitVec.ofNat 8 G)) ((out+BitVec.ofNat 64 8)+BitVec.ofNat 64 1)
    have p1 := written_append h0 h1 (by decide)
    simpa only [BitVec.add_assoc,BitVec.reduceAdd] using p1
  · simp [tailResult]
    rw [slice_zero G 32 8 (by decide)]
    have h0 := written_small G 0 4 (m) (out+BitVec.ofNat 64 8)
    simp only [Nat.mul_zero,Nat.pow_zero,Nat.div_one,Nat.zero_add] at h0
    have h1 := written_small G 4 1 ((m).writeW (out+BitVec.ofNat 64 8) (BitVec.ofNat 32 G)) ((out+BitVec.ofNat 64 8)+BitVec.ofNat 64 4)
    have p1 := written_append h0 h1 (by decide)
    simpa only [BitVec.add_assoc,BitVec.reduceAdd] using p1

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
