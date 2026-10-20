module
public import VerifiedGarbage.Proof.Mont.Words32

import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.GetElem

/-! # Convert arithmetic offset ranges into a region frame -/

@[expose] public section
namespace VG.Proof.Bignum
open VG VG.Proof.Mont

theorem outs_frame {base : Addr} {rs : List (Nat × Nat)} {m m' : Mem}
    (O : Outs base rs m m') (fit : ∀ r ∈ rs, r.1 + r.2 ≤ 2 ^ 64) :
    Frame (rs.map fun r => ⟨off base r.1, r.2⟩) m m' := by
  intro a ha
  apply O a
  intro r hr
  have H := ha ⟨off base r.1, r.2⟩ (List.mem_map.mpr ⟨r, hr, rfl⟩)
  have I := Offset.lt_iff a base (fit r hr)
  change ¬ ((a - off base r.1).toNat + 1 ≤ r.2) at H
  change (a - off base r.1).toNat < r.2 ↔ r.1 ≤ ofs base a ∧ ofs base a < r.1 + r.2 at I
  omega

end VG.Proof.Bignum
