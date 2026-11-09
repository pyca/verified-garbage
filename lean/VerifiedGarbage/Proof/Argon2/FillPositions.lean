module
public import VerifiedGarbage.Spec.Argon2

import VerifiedGarbage.Proof.Argon2.Dimensions
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.InstancePriority
public import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.GetElem

/-! Bounds for every block address used by the filling loop. -/

@[expose] public section

namespace VG.Proof.Argon2

open VG.Spec.Argon2

theorem previous_column_lt (p : Params) (hl : 0 < p.lanes)
    (hm : 8 * p.lanes ≤ p.memory) (column : Nat) :
    (column + p.laneLen - 1) % p.laneLen < p.laneLen := by
  have seg := segmentLen_ge_two p hl hm
  have lanes := laneLen_segments p hl
  exact Nat.mod_lt _ (by omega)

theorem cell_bytes (p : Params) (hl : 0 < p.lanes) {lane column : Nat}
    (hlane : lane < p.lanes) (hcolumn : column < p.laneLen) :
    (lane * p.laneLen + column) * 1024 + 1024 ≤ p.blocks * 1024 := by
  have cell := cell_lt p hl hlane hcolumn
  have scaled := Nat.mul_le_mul_right 1024 (show lane * p.laneLen + column + 1 ≤ p.blocks by omega)
  simpa only [Nat.add_mul, Nat.one_mul] using scaled

theorem current_cell_lt (p : Params) (hl : 0 < p.lanes) {lane slice index : Nat}
    (hlane : lane < p.lanes) (hslice : slice < 4) (hindex : index < p.segmentLen) :
    lane * p.laneLen + (slice * p.segmentLen + index) < p.blocks :=
  cell_lt p hl hlane (column_lt p hl hslice hindex)

theorem previous_cell_lt (p : Params) (hl : 0 < p.lanes)
    (hm : 8 * p.lanes ≤ p.memory) {lane column : Nat} (hlane : lane < p.lanes) :
    lane * p.laneLen + ((column + p.laneLen - 1) % p.laneLen) < p.blocks :=
  cell_lt p hl hlane (previous_column_lt p hl hm column)

theorem reference_cell_lt (p : Params) (hl : 0 < p.lanes)
    (hm : 8 * p.lanes ≤ p.memory) (pass lane slice index : Nat) (random : Word)
    (hlane : lane < p.lanes) :
    let ref := reference p pass lane slice index random
    ref.1 * p.laneLen + ref.2 < p.blocks := by
  obtain ⟨laneBound, columnBound⟩ := reference_bounds p hl hm pass lane slice index random hlane
  exact cell_lt p hl laneBound columnBound

end VG.Proof.Argon2
