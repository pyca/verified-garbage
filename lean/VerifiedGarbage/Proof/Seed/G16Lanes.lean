module

public import VerifiedGarbage.Proof.Seed.G16
meta import VerifiedGarbage.Proof.Seed.G16
public import VerifiedGarbage.Proof.Framework.Bitslice.Lanes
meta import VerifiedGarbage.Proof.Framework.Bitslice.Lanes
public import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Omega

/-!
# G on sixteen words: the lanes of the output layer

Each target's check of `g16Out` (`Proof/Seed/<Target>/G16.lean`) compares
the eight words it computes with `mk 64 (l2 i) 64`, the atoms `l2 i t` of
every bit `t` of output word `i` as lanes. The kernel evaluates `l2` (the
rows of `P0` and `P1`, the masks, the positions: 512 lists) in about ten
times what it takes to run the code, so its lanes are a table here
(`l2Lane`, `materialize_table`), evaluated once for the four targets, and
its atoms are bounded by a proof (`l2_lt`) rather than by evaluating them.
-/

@[expose] public section

namespace VG.Proof.Seed

open VG VG.Bitslice VG.Impl.Seed

/-- The lanes of output word `i`: its atoms `l2 i t`, at every bit `t`. -/
def l2Lane (i : Nat) : Nat := mk 64 (l2 i) 64

/-- The atoms of the output layer are bits of the eight planes of the S-box. -/
theorem l2_lt {i t : Nat} (hi : i < 8) (ht : t < 64) : ∀ a ∈ l2 i t, a < 2 ^ 9 := by
  intro a ha
  simp only [l2, List.mem_flatMap, List.mem_range] at ha
  obtain ⟨b, hb, ha⟩ := ha
  split at ha
  · simp only [List.mem_map] at ha
    obtain ⟨j, hj, rfl⟩ := ha
    have hj8 := rows_getD_lt (pRows_lt _) _ j hj
    have hl := laneOf_lt (n := 8 * i + 4 * (t / 32) + b) (by omega_using [hi, ht, hb])
    omega_using [hj8, hl]
  · cases ha

end VG.Proof.Seed

namespace VG

materialize_table Proof.Seed.l2Lane 8

end VG
