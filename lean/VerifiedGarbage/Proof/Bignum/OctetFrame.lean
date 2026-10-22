module

public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Omega

/-! Preserve byte-buffer values across disjoint arithmetic writes. -/

@[expose] public section
namespace VG.Proof.Mont
open VG

theorem Outside.bytesAt {m m' : Mem} {base : Addr} {d n offset len : Nat}
    (F : Outside base d n m m') (apart : offset + len ≤ d ∨ d + n ≤ offset)
    (bound : offset + len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' (off base offset) len = Spec.Rsa.bytesAt m (off base offset) len := by
  unfold Spec.Rsa.bytesAt
  apply List.map_congr_left
  intro i hi
  have index : i < len := List.mem_range.mp hi
  change m' (base + BitVec.ofNat 64 offset + BitVec.ofNat 64 i) = _
  rw [Offset.add_add]
  apply F
  simp only [ofs, Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show offset + i < 2 ^ 64 by omega)]
  omega

end VG.Proof.Mont
