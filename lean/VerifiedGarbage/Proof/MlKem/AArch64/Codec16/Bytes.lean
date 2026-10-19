module
public import VerifiedGarbage.Proof.MlKem.AArch64.Common
public import VerifiedGarbage.Proof.Rc4.AArch64.Vec

import VerifiedGarbage.Proof.Framework.Offset

/-! # Contiguous stores in the 384-byte encoding -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Codec16
open VG VG.AArch64 VG.Proof.MlKem.AArch64

theorem bytes_write {m : Mem} {p : Addr} {t n : Nat} {L old : Nat → Byte}
    (h : BytesUpTo m p 384 t L old) (hn : t+n ≤ 384) {x : BitVec (8*n)}
    (hx : ∀ i < n, x.extractLsb' (8*i) 8 = L (t+i)) :
    BytesUpTo (m.write (p+BitVec.ofNat 64 t) n x) p 384 (t+n) L old := by
  intro j hj
  have d : ((p+BitVec.ofNat 64 j)-(p+BitVec.ofNat 64 t)).toNat =
      if t ≤ j then j-t else 2^64+j-t := by
    exact Offset.sub_toNat' p (by omega) (by omega)
  rw [Mem.write,d]
  by_cases ht : t ≤ j
  · rw [ite_eq_left ht]
    by_cases hnj : j-t<n
    · rw [ite_eq_left hnj,ite_eq_left (by omega),hx _ hnj]
      congr 1; omega
    · rw [ite_eq_right hnj,h j hj,ite_eq_right (by omega),ite_eq_right (by omega)]
  · rw [ite_eq_right ht,ite_eq_right (by omega),h j hj,ite_eq_left (by omega),ite_eq_left (by omega)]

end VG.Proof.MlKem.AArch64.Codec16
