module

public import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Framework.Offset

/-! # Bytes read from an encoded message or an implicit-rejection buffer -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc
open VG VG.Proof.Bignum

theorem bytesAt_getD {m : Mem} {p : Addr} {n i : Nat} (hi : i < n) (d : Byte) :
    (Spec.Rsa.bytesAt m p n).getD i d = m (p + BitVec.ofNat 64 i) := by
  rw [← List.getElem_eq_getD (h := by rw [bytesAt_length]; exact hi) d]
  simp [Spec.Rsa.bytesAt]

theorem bytesAt_add (m : Mem) (p : Addr) (a b : Nat) :
    Spec.Rsa.bytesAt m p (a + b) = Spec.Rsa.bytesAt m p a ++ Spec.Rsa.bytesAt m (p + BitVec.ofNat 64 a) b := by
  simp only [Spec.Rsa.bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  simp only [Function.comp, Offset.add_add]

theorem bytesAt_take (m : Mem) (p : Addr) {k n : Nat} (h : k ≤ n) :
    Spec.Rsa.bytesAt m p k = (Spec.Rsa.bytesAt m p n).take k := by
  simp only [Spec.Rsa.bytesAt, ← List.map_take, List.take_range, Nat.min_eq_left h]

end VG.Proof.RsaPkcs1Enc
