import VerifiedGarbage.Spec.Argon2
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Spec.Argon2.Contract
import VerifiedGarbage.Proof.Framework.PowLit

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.Dimensions`. -/
section

/-! # Bounds for Argon2's rounded memory matrix -/

namespace VG.Proof.Argon2

open VG.Spec.Argon2

theorem laneLen_eq (p : Params) (hl : 0 < p.lanes) :
    p.laneLen = 4 * (p.memory / (4 * p.lanes)) := by
  unfold Params.laneLen Params.blocks
  rw [Nat.mul_comm 4 p.lanes, Nat.mul_assoc, Nat.mul_div_cancel_left _ hl]

theorem segmentLen_eq (p : Params) (hl : 0 < p.lanes) :
    p.segmentLen = p.memory / (4 * p.lanes) := by
  unfold Params.segmentLen
  rw [VG.Proof.Argon2.laneLen_eq p hl, Nat.mul_div_cancel_left _ (by decide : 0 < 4)]

theorem laneLen_segments (p : Params) (hl : 0 < p.lanes) :
    p.laneLen = 4 * p.segmentLen := by
  rw [VG.Proof.Argon2.laneLen_eq p hl, VG.Proof.Argon2.segmentLen_eq p hl]

theorem blocks_lanes (p : Params) (hl : 0 < p.lanes) :
    p.blocks = p.lanes * p.laneLen := by
  rw [VG.Proof.Argon2.laneLen_eq p hl]
  unfold Params.blocks
  rw [Nat.mul_comm 4 p.lanes, Nat.mul_assoc]

theorem blocks_le_memory (p : Params) : p.blocks ≤ p.memory :=
  Nat.mul_div_le _ _

theorem segmentLen_ge_two (p : Params) (hl : 0 < p.lanes)
    (hm : 8 * p.lanes ≤ p.memory) : 2 ≤ p.segmentLen := by
  rw [VG.Proof.Argon2.segmentLen_eq p hl, Nat.le_div_iff_mul_le (by omega : 0 < 4 * p.lanes)]
  omega

theorem column_lt (p : Params) (hl : 0 < p.lanes) {slice index : Nat}
    (hs : slice < 4) (hi : index < p.segmentLen) :
    slice * p.segmentLen + index < p.laneLen := by
  have h := Nat.mul_le_mul_right p.segmentLen (show slice + 1 ≤ 4 by omega)
  rw [Nat.add_mul, Nat.one_mul] at h
  rw [VG.Proof.Argon2.laneLen_segments p hl]
  omega

theorem cell_lt (p : Params) (hl : 0 < p.lanes) {lane column : Nat}
    (hlane : lane < p.lanes) (hc : column < p.laneLen) :
    lane * p.laneLen + column < p.blocks := by
  have h := Nat.mul_le_mul_right p.laneLen (show lane + 1 ≤ p.lanes by omega)
  rw [Nat.add_mul, Nat.one_mul] at h
  rw [VG.Proof.Argon2.blocks_lanes p hl]
  omega

theorem reference_bounds (p : Params) (hl : 0 < p.lanes)
    (hm : 8 * p.lanes ≤ p.memory) (pass lane slice index : Nat) (random : Word)
    (hlane : lane < p.lanes) :
    (reference p pass lane slice index random).1 < p.lanes ∧
      (reference p pass lane slice index random).2 < p.laneLen := by
  have hseg := VG.Proof.Argon2.segmentLen_ge_two p hl hm
  have hlen := VG.Proof.Argon2.laneLen_segments p hl
  unfold reference
  constructor
  · split
    · exact hlane
    · exact Nat.mod_lt _ hl
  · exact Nat.mod_lt _ (by omega)

end VG.Proof.Argon2

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.FillPositions`. -/
section

/-! Bounds for every block address used by the filling loop. -/

namespace VG.Proof.Argon2

open VG.Spec.Argon2

theorem previous_column_lt (p : Params) (hl : 0 < p.lanes)
    (hm : 8 * p.lanes ≤ p.memory) (column : Nat) :
    (column + p.laneLen - 1) % p.laneLen < p.laneLen := by
  have seg := VG.Proof.Argon2.segmentLen_ge_two p hl hm
  have lanes := VG.Proof.Argon2.laneLen_segments p hl
  exact Nat.mod_lt _ (by omega)

theorem cell_bytes (p : Params) (hl : 0 < p.lanes) {lane column : Nat}
    (hlane : lane < p.lanes) (hcolumn : column < p.laneLen) :
    (lane * p.laneLen + column) * 1024 + 1024 ≤ p.blocks * 1024 := by
  have cell := VG.Proof.Argon2.cell_lt p hl hlane hcolumn
  have scaled := Nat.mul_le_mul_right 1024 (show lane * p.laneLen + column + 1 ≤ p.blocks by omega)
  simpa only [Nat.add_mul, Nat.one_mul] using scaled

theorem current_cell_lt (p : Params) (hl : 0 < p.lanes) {lane slice index : Nat}
    (hlane : lane < p.lanes) (hslice : slice < 4) (hindex : index < p.segmentLen) :
    lane * p.laneLen + (slice * p.segmentLen + index) < p.blocks :=
  VG.Proof.Argon2.cell_lt p hl hlane (VG.Proof.Argon2.column_lt p hl hslice hindex)

theorem previous_cell_lt (p : Params) (hl : 0 < p.lanes)
    (hm : 8 * p.lanes ≤ p.memory) {lane column : Nat} (hlane : lane < p.lanes) :
    lane * p.laneLen + ((column + p.laneLen - 1) % p.laneLen) < p.blocks :=
  VG.Proof.Argon2.cell_lt p hl hlane (VG.Proof.Argon2.previous_column_lt p hl hm column)

theorem reference_cell_lt (p : Params) (hl : 0 < p.lanes)
    (hm : 8 * p.lanes ≤ p.memory) (pass lane slice index : Nat) (random : Word)
    (hlane : lane < p.lanes) :
    let ref := reference p pass lane slice index random
    ref.1 * p.laneLen + ref.2 < p.blocks := by
  obtain ⟨laneBound, columnBound⟩ := VG.Proof.Argon2.reference_bounds p hl hm pass lane slice index random hlane
  exact VG.Proof.Argon2.cell_lt p hl laneBound columnBound

theorem cell_contains (base : VG.Addr) (p : Params) (hl : 0 < p.lanes)
    (hm : p.memory < 2 ^ 32) {lane column : Nat}
    (hlane : lane < p.lanes) (hcolumn : column < p.laneLen) :
    (⟨base, p.blocks * 1024⟩ : VG.Region).Contains
      (base + BitVec.ofNat 64 ((lane * p.laneLen + column) * 1024)) 1024 := by
  have bytes := VG.Proof.Argon2.cell_bytes p hl hlane hcolumn
  have blocks : p.blocks < 2 ^ 32 := Nat.lt_of_le_of_lt (VG.Proof.Argon2.blocks_le_memory p) hm
  have total : p.blocks * 1024 < 2 ^ 64 :=
    Nat.lt_trans (Nat.mul_lt_mul_of_pos_right blocks (by decide : 0 < 1024)) (by decide +kernel)
  exact VG.Offset.contains_base base
    (d := (lane * p.laneLen + column) * 1024) (n := 1024) (k := p.blocks * 1024)
    bytes (Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_right _ _) bytes) total)

end VG.Proof.Argon2

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.Matrix`. -/
section

/-! Relate the lane-major assembly allocation to the specification's block array. -/

namespace VG.Proof.Argon2

open VG VG.Spec.Argon2

def matrixCell (base : Addr) (k : Nat) : Addr := base + BitVec.ofNat 64 (k * 1024)

structure Represents (m : Mem) (base : Addr) (n : Nat) (blocks : Array Block) : Prop where
  size : blocks.size = n
  block : ∀ k < n, blockAt m (VG.Proof.Argon2.matrixCell base k) = blocks[k]?.getD zeroBlock

theorem Represents.update {m m' : Mem} {base : Addr} {n : Nat} {blocks : Array Block}
    (h : VG.Proof.Argon2.Represents m base n blocks) (k : Nat) (hk : k < n) (value : Block)
    (written : blockAt m' (VG.Proof.Argon2.matrixCell base k) = value)
    (kept : ∀ j < n, j ≠ k → blockAt m' (VG.Proof.Argon2.matrixCell base j) = blockAt m (VG.Proof.Argon2.matrixCell base j)) :
    VG.Proof.Argon2.Represents m' base n (blocks.set! k value) := by
  refine ⟨(Array.size_set! _ _ _).trans h.size, ?_⟩
  intro j hj
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  by_cases equal : k = j
  · rw [ite_eq_left equal, ite_eq_left (by rw [h.size]; exact hk), Option.getD_some]
    rw [← equal]; exact written
  · rw [ite_eq_right equal]
    exact (kept j hj (Ne.symm equal)).trans (h.block j hj)

theorem matrixCell_sub (base : Addr) (n k : Nat) (hk : k < n) :
    Region.Sub ⟨VG.Proof.Argon2.matrixCell base k, 1024⟩ ⟨base, n * 1024⟩ :=
  Offset.sub_base base (by omega)

theorem matrixCell_disjoint (base : Addr) (n i j : Nat) (bound : n * 1024 < 2 ^ 64)
    (hi : i < n) (hj : j < n) (different : i ≠ j) :
    (⟨VG.Proof.Argon2.matrixCell base i, 1024⟩ : Region).Disjoint ⟨VG.Proof.Argon2.matrixCell base j, 1024⟩ :=
  Offset.disjoint base (by omega) (by omega) (by omega)

end VG.Proof.Argon2

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.FinalReduction`. -/
section

/-! The final lane reduction, without changing the reviewed finish specification. -/

namespace VG.Proof.Argon2

open VG VG.Spec.Argon2

def lastIndex (p : Params) (lane : Nat) : Nat := (lane + 1) * p.laneLen - 1

def reduction (p : Params) (memory : Array Block) (start count : Nat) (acc : Block) : Block :=
  (List.range' start count).foldl (fun b lane => xorBlock b (memory[VG.Proof.Argon2.lastIndex p lane]?.getD zeroBlock)) acc

theorem reduction_zero (p : Params) (memory : Array Block) (start : Nat) (acc : Block) :
    VG.Proof.Argon2.reduction p memory start 0 acc = acc := rfl

theorem reduction_succ (p : Params) (memory : Array Block) (start count : Nat) (acc : Block) :
    VG.Proof.Argon2.reduction p memory start (count + 1) acc =
      VG.Proof.Argon2.reduction p memory (start + 1) count (xorBlock acc (memory[VG.Proof.Argon2.lastIndex p start]?.getD zeroBlock)) := by
  simp only [VG.Proof.Argon2.reduction, List.range'_succ, List.foldl_cons]

theorem finish_reduction (p : Params) (memory : Array Block) :
    finish p memory = hPrime p.tagLen (serialize (VG.Proof.Argon2.reduction p memory 0 p.lanes zeroBlock)) := by
  rw [finish, VG.Proof.Argon2.reduction, List.range_eq_range']
  rfl

theorem lastIndex_bounds (p : Params) (positive : 0 < p.lanes) (minimum : 2 ≤ p.segmentLen)
    (lane : Nat) (active : lane < p.lanes) : 0 < VG.Proof.Argon2.lastIndex p lane ∧ VG.Proof.Argon2.lastIndex p lane < p.blocks := by
  have q : 8 ≤ p.laneLen := by
    have eq := VG.Proof.Argon2.laneLen_segments p positive
    omega
  have total := VG.Proof.Argon2.blocks_lanes p positive
  have product : (lane + 1) * p.laneLen ≤ p.lanes * p.laneLen := Nat.mul_le_mul_right _ (by omega)
  have low : p.laneLen ≤ (lane + 1) * p.laneLen := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right p.laneLen (show 1 ≤ lane + 1 by omega)
  unfold VG.Proof.Argon2.lastIndex
  omega

theorem xorBlock_comm (a b : Block) : xorBlock a b = xorBlock b a := by
  apply Vector.ext
  intro i hi
  simp only [xorBlock, Vector.getElem_zipWith, BitVec.xor_comm]

end VG.Proof.Argon2

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.Reference`. -/
section

/-! # Bounds for the quadratic reference-window mapping in RFC 9106 §3.4.2 -/

namespace VG.Proof.Argon2

theorem reference_square_bound (j : Nat) (hj : j < 2 ^ 32) : j * j < 2 ^ 64 := by
  exact Nat.lt_of_lt_of_eq (Nat.mul_self_lt_mul_self hj) (by decide)

theorem reference_scaled_bound (j : Nat) (hj : j < 2 ^ 32) :
    j * j / 2 ^ 32 < 2 ^ 32 := by
  apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 2 ^ 32)).mpr
  exact Nat.lt_of_lt_of_eq (VG.Proof.Argon2.reference_square_bound j hj) (by decide)

theorem reference_product_bound (count j : Nat) (hc : count < 2 ^ 32)
    (hj : j < 2 ^ 32) : count * (j * j / 2 ^ 32) < 2 ^ 64 := by
  exact Nat.lt_of_lt_of_eq (Nat.mul_lt_mul_of_lt_of_lt hc (VG.Proof.Argon2.reference_scaled_bound j hj))
    (by decide)

theorem reference_scale_lt_count (count j : Nat) (hc : 0 < count) (hj : j < 2 ^ 32) :
    count * (j * j / 2 ^ 32) / 2 ^ 32 < count := by
  apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 2 ^ 32)).mpr
  exact Nat.mul_lt_mul_of_pos_left (VG.Proof.Argon2.reference_scaled_bound j hj) hc

theorem reference_relative_bound (count j : Nat) (hc : 0 < count) :
    count - 1 - count * (j * j / 2 ^ 32) / 2 ^ 32 < count := by
  omega

open VG.Spec.Argon2

theorem reference_count_lt_lane (p : Params) (hl : 0 < p.lanes)
    (hm : 8 * p.lanes ≤ p.memory) (pass slice index : Nat) (same : Bool)
    (hs : slice < 4) (hi : index < p.segmentLen) :
    referenceCount p pass slice index same < p.laneLen := by
  have seg := VG.Proof.Argon2.segmentLen_ge_two p hl hm
  have len := VG.Proof.Argon2.laneLen_segments p hl
  have column := VG.Proof.Argon2.column_lt p hl hs hi
  unfold referenceCount
  by_cases first : pass = 0
  · rw [ite_eq_left first]
    cases same
    · simp only [Bool.false_eq_true, ite_false]
      split <;> omega
    · simp only [ite_true]
      omega
  · rw [ite_eq_right first]
    cases same
    · simp only [Bool.false_eq_true, ite_false]
      split <;> omega
    · simp only [ite_true]
      omega

theorem reference_count_positive (p : Params) (hl : 0 < p.lanes)
    (hm : 8 * p.lanes ≤ p.memory) (pass slice index : Nat) (same : Bool)
    (active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ index)
    (firstLane : pass = 0 → slice = 0 → same = true) :
    0 < referenceCount p pass slice index same := by
  have seg := VG.Proof.Argon2.segmentLen_ge_two p hl hm
  have len := VG.Proof.Argon2.laneLen_segments p hl
  unfold referenceCount
  by_cases first : pass = 0
  · rw [ite_eq_left first]
    by_cases zero : slice = 0
    · simp only [firstLane first zero, zero, Nat.zero_mul, ite_true]
      omega
    · have mul := Nat.mul_le_mul_right p.segmentLen (show 1 ≤ slice by omega)
      rw [Nat.one_mul] at mul
      cases same
      · simp only [Bool.false_eq_true, ite_false]
        split <;> omega
      · simp only [ite_true]
        omega
  · rw [ite_eq_right first]
    cases same
    · simp only [Bool.false_eq_true, ite_false]
      split <;> omega
    · simp only [ite_true]
      omega

theorem reference_count_32 (p : Params) (hl : 0 < p.lanes)
    (hm : 8 * p.lanes ≤ p.memory) (memoryBound : p.memory < 2 ^ 32)
    (pass slice index : Nat) (same : Bool) (hs : slice < 4) (hi : index < p.segmentLen) :
    referenceCount p pass slice index same < 2 ^ 32 := by
  have laneBlocks := Nat.le_mul_of_pos_left p.laneLen hl
  rw [← VG.Proof.Argon2.blocks_lanes p hl] at laneBlocks
  exact Nat.lt_of_lt_of_le (VG.Proof.Argon2.reference_count_lt_lane p hl hm pass slice index same hs hi)
    (Nat.le_trans laneBlocks (Nat.le_trans (VG.Proof.Argon2.blocks_le_memory p) (Nat.le_of_lt memoryBound)))

theorem reference_wrap (sum q : Nat) (bound : sum < 2 * q) :
    sum % q = if sum < q then sum else sum - q := by
  by_cases small : sum < q
  · rw [ite_eq_left small, Nat.mod_eq_of_lt small]
  · rw [ite_eq_right small, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

end VG.Proof.Argon2

end
