module
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Spec.Rsa.Contract

import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # Packed byte exports have the shared RSA precomputation word format -/

@[expose] public section

namespace VG.Proof.Bignum
open VG

theorem read_eq_wv (m : Mem) (base : Addr) (d : Nat) :
    ∀ k, (m.read (off base d) (8 * k)).toNat = wv m base d k
  | 0 => by simp [Mem.read, wv]
  | k + 1 => by
    rw [show 8 * (k + 1) = 8 + 8 * k by omega, VG.Proof.Mont.read_toNat_add,
      read_eq_wv m base d k, wv, Offset.add_add, show 8 * (8 * k) = 64 * k by omega]
    rfl

theorem wordsAt_two_reads {m : Mem} {p : Addr} {w x y : Nat}
    (first : (m.read p (8 * w)).toNat = x)
    (second : (m.read (off p (8 * w)) (8 * w)).toNat = y) :
    Spec.Rsa.wordsAt m p (2 * w) = Spec.Rsa.toWords x w ++ Spec.Rsa.toWords y w := by
  have hx : wv m p 0 w = x := by
    rw [← read_eq_wv]; simpa only [off, BitVec.add_zero] using first
  have hy : wv m p (8 * w) w = y := by rw [← read_eq_wv]; exact second
  apply wordsAt_two
  · intro i hi
    have h := word_eq_ofNat m p 0 w hi
    simpa only [Nat.zero_add, hx] using h
  · intro i hi
    rw [word_eq_ofNat m p (8 * w) w hi, hy]

theorem wordsAt_zero_read {m : Mem} {p : Addr} {n : Nat}
    (zero : (m.read p (8 * n)).toNat = 0) :
    Spec.Rsa.wordsAt m p n = List.replicate n 0 := by
  have hz : wv m p 0 n = 0 := by
    rw [← read_eq_wv]; simpa only [off, BitVec.add_zero] using zero
  apply List.ext_getElem
  · simp only [Spec.Rsa.wordsAt, List.length_map, List.length_range, List.length_replicate]
  · intro i hi hj
    have bound : i < n := by simpa only [List.length_replicate] using hj
    have h := word_eq_ofNat m p 0 n bound
    rw [hz, Nat.zero_div] at h
    simp only [Spec.Rsa.wordsAt, List.getElem_map, List.getElem_range, List.getElem_replicate]
    change word m p (8 * i) = BitVec.ofNat 64 0
    simpa only [Nat.zero_add] using h

end VG.Proof.Bignum
