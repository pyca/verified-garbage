module

public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset

/-! # Convert a single written region to its workspace-relative footprint -/

@[expose] public section
namespace VG.Proof.Mont
open VG

theorem frame_outside {base : Addr} {d len : Nat} {m m' : Mem}
    (F : Frame [⟨off base d, len⟩] m m') (fit : d + len ≤ 2 ^ 64) :
    Outside base d len m m' := by
  intro a outside
  apply F
  intro r mem
  obtain rfl := List.mem_singleton.mp mem
  intro H
  have I := Offset.lt_iff a base fit
  change (a - off base d).toNat + 1 ≤ len at H
  change (a - off base d).toNat < len ↔ d ≤ ofs base a ∧ ofs base a < d + len at I
  have := I.mp (by omega)
  omega

end VG.Proof.Mont
