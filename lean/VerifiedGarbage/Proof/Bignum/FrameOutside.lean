module
public import VerifiedGarbage.Proof.Mont.Words

import VerifiedGarbage.Proof.Framework.Offset

/-! # Translate a byte-region frame back to a workspace offset range -/

@[expose] public section
namespace VG.Proof.Bignum
open VG VG.Proof.Mont

theorem frame_outside {base : Addr} {d len : Nat} {m m' : Mem}
    (F : Frame [⟨off base d, len⟩] m m') (fit : d + len ≤ 2 ^ 64) :
    Outside base d len m m' := by
  intro a ha
  apply F a
  intro r hr hc
  obtain rfl := List.mem_singleton.mp hr
  have I := Offset.lt_iff a base fit
  change (a - off base d).toNat < len ↔ d ≤ ofs base a ∧ ofs base a < d + len at I
  change (a - off base d).toNat + 1 ≤ len at hc
  have := I.mp (by omega)
  omega

end VG.Proof.Bignum
