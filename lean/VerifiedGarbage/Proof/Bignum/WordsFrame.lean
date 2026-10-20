module
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.Spec.Rsa.Contract

import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem

/-! # Scratch writes preserve external packed RSA key words -/

@[expose] public section
namespace VG.Proof.Bignum
open VG VG.Proof.Mont

theorem scratch_words {base p : Addr} {bytes n : Nat} {m m' : Mem}
    (O : Outside base 0 bytes m m') (fit : bytes ≤ 2 ^ 64)
    (countFit : 8 * n ≤ 2 ^ 64) (sep : Region.Disjoint ⟨p, 8 * n⟩ ⟨base, bytes⟩) :
    Spec.Rsa.wordsAt m' p n = Spec.Rsa.wordsAt m p n := by
  have F := outside_frame O (by omega)
  simp only [BitVec.add_zero] at F
  unfold Spec.Rsa.wordsAt
  apply List.map_congr_left
  intro i hi
  have bound := List.mem_range.mp hi
  apply F.readW (r := ⟨p, 8 * n⟩)
    (Offset.contains_base _ (by omega) (by omega)) ?_ (by decide)
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact sep

end VG.Proof.Bignum
