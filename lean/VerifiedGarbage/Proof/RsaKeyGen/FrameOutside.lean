module

import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.Proof.Mont.Words32

/-! # A single offset frame is also an arithmetic outside-range fact -/

@[expose] public section
namespace VG.Proof.RsaKeyGen
open VG VG.Proof.Mont

theorem frame_outside {base : Addr} {d len : Nat} {m m' : Mem}
    (F : Frame [⟨off base d, len⟩] m m') (fit : d + len ≤ 2 ^ 64) : Outside base d len m m' := by
  intro a outside
  apply F a
  intro r mem
  obtain rfl := List.mem_singleton.mp mem
  have I := Offset.lt_iff a base fit
  change (a - off base d).toNat < len ↔ d ≤ ofs base a ∧ ofs base a < d + len at I
  change ¬ ((a - off base d).toNat + 1 ≤ len)
  omega

theorem frame_outs {base : Addr} {rs : List (Nat × Nat)} {m m' : Mem}
    (F : Frame (rs.map (fun r => ⟨off base r.1, r.2⟩)) m m')
    (fit : ∀ r ∈ rs, r.1 + r.2 ≤ 2 ^ 64) : Outs base rs m m' := by
  intro a outside
  apply F a
  intro R mem
  obtain ⟨r, known, rfl⟩ := List.mem_map.mp mem
  have I := Offset.lt_iff a base (fit r known)
  change (a - off base r.1).toNat < r.2 ↔ r.1 ≤ ofs base a ∧ ofs base a < r.1 + r.2 at I
  have O := outside r known
  change ¬ ((a - off base r.1).toNat + 1 ≤ r.2)
  omega

end VG.Proof.RsaKeyGen
