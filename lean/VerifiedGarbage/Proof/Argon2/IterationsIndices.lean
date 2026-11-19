module

public import VerifiedGarbage.Proof.Argon2.Slices
import VerifiedGarbage.Proof.Argon2.SegmentIndices
public import VerifiedGarbage.Proof.Argon2.SegmentStart
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Spec.Argon2
import VerifiedGarbage.Proof.Argon2.FillStep

/-! ### `Argon2.References`, which the modules that import this one used -/

section

/-! The reviewed flattened reference log determines every lane/column pair. -/

@[expose] public section

namespace VG.Proof.Argon2

open VG.Spec.Argon2

def Columns (q : Nat) (s : FillState) : Prop := ∀ ref ∈ s.indices, ref.2 < q

theorem fold_columns {α : Type} (q : Nat) (f : FillState → α → FillState)
    (step : ∀ s a, Columns q s → Columns q (f s a)) (xs : List α) (s : FillState) (h : Columns q s) :
    Columns q (xs.foldl f s) := by
  induction xs generalizing s with
  | nil => exact h
  | cons x xs ih => exact ih (f s x) (step s x h)

theorem fillBlock_columns (p : Params) (positive : 0 < p.laneLen)
    (pass slice lane index : Nat) (s : FillState) (h : Columns p.laneLen s) :
    Columns p.laneLen (fillBlock p pass slice lane index s) := by
  by_cases skipped : pass = 0 ∧ slice = 0 ∧ index < 2
  · rw [fillBlock, ite_eq_left skipped]; exact h
  · unfold Columns
    rw [FillStep.indices p pass lane slice index s (by omega_using [skipped])]
    split
    · exact h
    · intro ref hr
      simp only [List.mem_cons] at hr
      rcases hr with rfl | hr
      · change _ % p.laneLen < p.laneLen
        exact Nat.mod_lt _ positive
      · exact h ref hr

theorem fillPass_columns (p : Params) (positive : 0 < p.laneLen) (s : FillState) (pass : Nat)
    (h : Columns p.laneLen s) : Columns p.laneLen (fillPass p s pass) := by
  unfold fillPass
  apply fold_columns
  · intro s slice hs
    apply fold_columns
    · intro s lane hs
      exact fold_columns _ _ (fun s index hs => fillBlock_columns p positive pass slice lane index s hs) _ s hs
    · exact hs
  · exact h

theorem fill_columns (p : Params) (positive : 0 < p.laneLen) (password salt secret ad : List Byte) :
    Columns p.laneLen (fill p password salt secret ad) := by
  unfold fill
  apply fold_columns _ _ (fun s pass hs => fillPass_columns p positive s pass hs)
  intro ref hr
  exact False.elim (List.not_mem_nil hr)

def flattenRef (q : Nat) (ref : Nat × Nat) : Nat := ref.1 * q + ref.2

def decodeRef (q n : Nat) : Nat × Nat := (n / q, n % q)

theorem decode_flatten (q : Nat) (positive : 0 < q) (ref : Nat × Nat) (bound : ref.2 < q) :
    decodeRef q (flattenRef q ref) = ref := by
  unfold decodeRef flattenRef
  rw [Nat.mul_comm ref.1 q, Nat.mul_add_div positive,
    Nat.div_eq_of_lt bound, Nat.add_zero, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt bound]

theorem decode_list (q : Nat) (positive : 0 < q) (xs : List (Nat × Nat))
    (bound : ∀ ref ∈ xs, ref.2 < q) : (xs.map (flattenRef q)).map (decodeRef q) = xs := by
  induction xs with
  | nil => rfl
  | cons ref xs ih =>
    simp only [List.map_cons]
    rw [decode_flatten q positive ref (bound ref (List.mem_cons_self ..)),
      ih (fun r hr => bound r (List.mem_cons_of_mem ref hr))]

theorem references_injective (p : Params) (positive : 0 < p.laneLen)
    (password₁ salt₁ secret₁ ad₁ password₂ salt₂ secret₂ ad₂ : List Byte)
    (same : references p password₁ salt₁ secret₁ ad₁ = references p password₂ salt₂ secret₂ ad₂) :
    (fill p password₁ salt₁ secret₁ ad₁).indices = (fill p password₂ salt₂ secret₂ ad₂).indices := by
  apply List.reverse_inj.mp
  have left := fill_columns p positive password₁ salt₁ secret₁ ad₁
  have right := fill_columns p positive password₂ salt₂ secret₂ ad₂
  have decoded := congrArg (List.map (decodeRef p.laneLen)) same
  change ((fill p password₁ salt₁ secret₁ ad₁).indices.reverse.map (flattenRef p.laneLen)).map _ =
    ((fill p password₂ salt₂ secret₂ ad₂).indices.reverse.map (flattenRef p.laneLen)).map _ at decoded
  rw [decode_list p.laneLen positive _ (fun ref hr => left ref (List.mem_reverse.mp hr)),
    decode_list p.laneLen positive _ (fun ref hr => right ref (List.mem_reverse.mp hr))] at decoded
  exact decoded

end VG.Proof.Argon2

end

end

/-! ### `Argon2.SlicesIndices`, which this module and modules that import it used -/

section

/-! ### `Argon2.LanesIndices`, which this module and modules that import it used -/

section

/-! Recover each segment's reference log from the complete lane fold. -/

@[expose] public section

namespace VG.Proof.Argon2

open VG.Spec.Argon2

def segmentReferences (p : Params) (pass slice : Nat) : Nat :=
  if independent p pass slice then 0 else p.segmentLen - segmentStart pass slice

theorem fillBlock_independent_indices (p : Params) (pass lane slice index : Nat) (state : FillState)
    (mode : independent p pass slice = true) : (fillBlock p pass slice lane index state).indices = state.indices := by
  unfold fillBlock
  split
  · rfl
  · simp only [mode, ite_true]

theorem segment_independent_indices (p : Params) (pass lane slice start count : Nat) (state : FillState)
    (mode : independent p pass slice = true) : (segment p pass lane slice start count state).indices = state.indices := by
  induction count generalizing start state with
  | zero => rfl
  | succ n ih =>
    rw [segment_succ, ih, fillBlock_independent_indices p pass lane slice start state mode]

theorem segment_references_drop (p : Params) (pass lane slice : Nat) (state : FillState)
    (minimum : 2 ≤ p.segmentLen) :
    (segment p pass lane slice 0 p.segmentLen state).indices.drop (segmentReferences p pass slice) = state.indices := by
  cases mode : independent p pass slice
  · rw [segment_start p pass lane slice state minimum]
    change (segment p pass lane slice (segmentStart pass slice) (p.segmentLen - segmentStart pass slice) state).indices.drop
      (if independent p pass slice then 0 else p.segmentLen - segmentStart pass slice) = state.indices
    simp only [mode, Bool.false_eq_true, ite_false]
    apply segment_indices_drop _ _ _ _ _ _ _ _ mode
    unfold segmentStart; split <;> omega_arith
  · rw [segment_independent_indices p pass lane slice 0 p.segmentLen state mode]
    simp only [segmentReferences, mode, ite_true, List.drop_zero]

theorem lanes_indices_drop (p : Params) (pass slice start count : Nat) (state : FillState)
    (minimum : 2 ≤ p.segmentLen) :
    (lanes p pass slice start count state).indices.drop (count * segmentReferences p pass slice) = state.indices := by
  induction count generalizing start state with
  | zero => rw [Nat.zero_mul, lanes_zero, List.drop_zero]
  | succ n ih =>
    rw [lanes_succ, Nat.add_mul, Nat.one_mul, ← List.drop_drop,
      ih, segment_references_drop p pass start slice state minimum]

theorem lanes_first_segment (p : Params) (pass slice start count : Nat) (leftState rightState : FillState)
    (minimum : 2 ≤ p.segmentLen)
    (indices : (lanes p pass slice start (count + 1) leftState).indices =
      (lanes p pass slice start (count + 1) rightState).indices) :
    (segment p pass start slice 0 p.segmentLen leftState).indices =
      (segment p pass start slice 0 p.segmentLen rightState).indices := by
  have dropped := congrArg (List.drop (count * segmentReferences p pass slice)) indices
  rw [lanes_succ, lanes_succ, lanes_indices_drop p pass slice (start + 1) count _ minimum,
    lanes_indices_drop p pass slice (start + 1) count _ minimum] at dropped
  exact dropped

end VG.Proof.Argon2

end

end

/-! Reference-log suffixes span slices with different public addressing modes. -/

@[expose] public section

namespace VG.Proof.Argon2

open VG.Spec.Argon2

def sliceReferences (p : Params) (pass slice : Nat) : Nat := p.lanes * segmentReferences p pass slice

def slicesReferences (p : Params) (pass start : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sliceReferences p pass start + slicesReferences p pass (start + 1) n

theorem slices_indices_drop (p : Params) (pass start count : Nat) (state : FillState)
    (minimum : 2 ≤ p.segmentLen) :
    (slices p pass start count state).indices.drop (slicesReferences p pass start count) = state.indices := by
  induction count generalizing start state with
  | zero => rfl
  | succ n ih =>
    rw [slices_succ, slicesReferences,
      show sliceReferences p pass start + slicesReferences p pass (start + 1) n =
        slicesReferences p pass (start + 1) n + sliceReferences p pass start from Nat.add_comm _ _,
      ← List.drop_drop, ih]
    exact lanes_indices_drop p pass start 0 p.lanes state minimum

theorem slices_first_lane_fold (p : Params) (pass start count : Nat) (leftState rightState : FillState)
    (minimum : 2 ≤ p.segmentLen)
    (indices : (slices p pass start (count + 1) leftState).indices =
      (slices p pass start (count + 1) rightState).indices) :
    (lanes p pass start 0 p.lanes leftState).indices = (lanes p pass start 0 p.lanes rightState).indices := by
  have dropped := congrArg (List.drop (slicesReferences p pass (start + 1) count)) indices
  rw [slices_succ, slices_succ, slices_indices_drop p pass (start + 1) count _ minimum,
    slices_indices_drop p pass (start + 1) count _ minimum] at dropped
  exact dropped

end VG.Proof.Argon2

end

end

/-! Recover each pass's reviewed reference log from the complete filling log. -/

@[expose] public section

namespace VG.Proof.Argon2

open VG.Spec.Argon2

def passReferences (p : Params) (pass : Nat) : Nat := slicesReferences p pass 0 4

def iterationsReferences (p : Params) (start : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => passReferences p start + iterationsReferences p (start + 1) n

theorem pass_indices_drop (p : Params) (pass : Nat) (state : FillState) (minimum : 2 ≤ p.segmentLen) :
    (fillPass p state pass).indices.drop (passReferences p pass) = state.indices := by
  rw [← slices_pass p pass state]
  exact slices_indices_drop p pass 0 4 state minimum

theorem iterations_indices_drop (p : Params) (start count : Nat) (state : FillState) (minimum : 2 ≤ p.segmentLen) :
    (iterations p start count state).indices.drop (iterationsReferences p start count) = state.indices := by
  induction count generalizing start state with
  | zero => rfl
  | succ n ih =>
    rw [iterations_succ, iterationsReferences,
      show passReferences p start + iterationsReferences p (start + 1) n =
        iterationsReferences p (start + 1) n + passReferences p start from Nat.add_comm _ _,
      ← List.drop_drop, ih, pass_indices_drop p start state minimum]

theorem iterations_first_pass (p : Params) (start count : Nat) (leftState rightState : FillState)
    (minimum : 2 ≤ p.segmentLen)
    (indices : (iterations p start (count + 1) leftState).indices =
      (iterations p start (count + 1) rightState).indices) :
    (fillPass p leftState start).indices = (fillPass p rightState start).indices := by
  have dropped := congrArg (List.drop (iterationsReferences p (start + 1) count)) indices
  rw [iterations_succ, iterations_succ, iterations_indices_drop p (start + 1) count _ minimum,
    iterations_indices_drop p (start + 1) count _ minimum] at dropped
  exact dropped

end VG.Proof.Argon2
