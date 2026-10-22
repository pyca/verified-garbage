module

public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.GetElem

/-! Equal packed copies preserve the byte strings used by shared specifications. -/

@[expose] public section
namespace VG.Proof.Bignum
open VG

theorem bytesAt_getD (m : Mem) (p : Addr) {n i : Nat} (hi : i < n) :
    (Spec.Rsa.bytesAt m p n).getD i 0 = m (p + BitVec.ofNat 64 i) := by
  simp only [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hi, Option.map_some, Option.getD_some]

theorem bytesAt_eq_of_read {m m' : Mem} {p q : Addr} {n : Nat}
    (copy : m'.read q n = m.read p n) : Spec.Rsa.bytesAt m' q n = Spec.Rsa.bytesAt m p n := by
  unfold Spec.Rsa.bytesAt
  apply List.map_congr_left
  intro i hi
  have bound := List.mem_range.mp hi
  have byte := congrArg (fun v : BitVec (8 * n) => v.extractLsb' (8 * i) 8) copy
  rw [Mem.extractLsb'_read _ _ bound, Mem.extractLsb'_read _ _ bound] at byte
  exact byte

end VG.Proof.Bignum
