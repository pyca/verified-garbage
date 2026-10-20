module
public import VerifiedGarbage.Proof.Bignum.Words

import VerifiedGarbage.Proof.Bignum.ExportEncoding
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem

/-! # External packed integers remain unchanged by scratch writes -/

@[expose] public section
namespace VG.Proof.Bignum
open VG VG.Proof.Mont

theorem scratch_wv {base p : Addr} {bytes len d n : Nat} {m m' : Mem}
    (O : Outside base 0 bytes m m') (fit : bytes ≤ 2 ^ 64) (lenFit : len < 2 ^ 64)
    (countFit : 8 * n < 2 ^ 64) (inside : d + 8 * n ≤ len)
    (sep : Region.Disjoint ⟨p, len⟩ ⟨base, bytes⟩) : wv m' p d n = wv m p d n := by
  have F := outside_frame O (by omega)
  simp only [BitVec.add_zero] at F
  rw [← read_eq_wv, ← read_eq_wv]
  rw [F.read (r := ⟨p, len⟩) (Offset.contains_base _ inside (by omega))
    (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact sep) countFit]

end VG.Proof.Bignum
