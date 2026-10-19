module

public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Spec.Rsa.Contract

/-! # Translate offset-based arithmetic frames to byte-region frames -/

@[expose] public section
namespace VG.Proof.Bignum
open VG VG.Proof.Mont

theorem outside_frame {base : Addr} {d len : Nat} {m m' : Mem}
    (O : Outside base d len m m') (fit : d + len ≤ 2 ^ 64) :
    Frame [⟨off base d, len⟩] m m' := by
  intro a ha
  have H := ha ⟨off base d, len⟩ (by simp)
  have I := Offset.lt_iff a base fit
  change ¬ ((a - off base d).toNat + 1 ≤ len) at H
  change (a - off base d).toNat < len ↔ d ≤ ofs base a ∧ ofs base a < d + len at I
  apply O
  omega

theorem scratch_bytes {base p : Addr} {bytes len : Nat} {m m' : Mem}
    (O : Outside base 0 bytes m m') (fit : len ≤ 2 ^ 64)
    (sep : Region.Disjoint ⟨p, len⟩ ⟨base, bytes⟩) :
    Spec.Rsa.bytesAt m' p len = Spec.Rsa.bytesAt m p len := by
  unfold Spec.Rsa.bytesAt
  apply List.map_congr_left
  intro i hi
  have hl := List.mem_range.mp hi
  have H := sep (p + BitVec.ofNat 64 i)
    (Offset.contains_base p (by omega) (by omega))
  change ¬ (ofs base (p + BitVec.ofNat 64 i) + 1 ≤ bytes) at H
  exact O _ (.inr (by omega))

end VG.Proof.Bignum
