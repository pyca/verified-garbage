import VerifiedGarbage.Spec.Argon2

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.FillStep`. -/
section

/-! Expose the reviewed filling step's random word, matrix update and leakage log. -/

namespace VG.Proof.Argon2.FillStep

open VG.Spec.Argon2

def random (p : Params) (pass lane slice index : Nat) (blocks : Array Block) : Word :=
  if independent p pass slice then
    (addressBlock p pass lane slice (index / 128 + 1))[index % 128]'(Nat.mod_lt _ (by decide))
  else
    (blocks[lane * p.laneLen + (slice * p.segmentLen + index + p.laneLen - 1) % p.laneLen]?.getD zeroBlock)[0]

def update (p : Params) (pass lane slice index : Nat) (blocks : Array Block) (word : Word) : Array Block :=
  let column := slice * p.segmentLen + index
  let current := lane * p.laneLen + column
  let prev := blocks[lane * p.laneLen + (column + p.laneLen - 1) % p.laneLen]?.getD zeroBlock
  let ref := reference p pass lane slice index word
  let other := blocks[ref.1 * p.laneLen + ref.2]?.getD zeroBlock
  let next := compress prev other
  blocks.set! current (if pass = 0 then next else xorBlock next (blocks[current]?.getD zeroBlock))

theorem not_skipped (pass slice index : Nat) (active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ index) :
    ¬(pass = 0 ∧ slice = 0 ∧ index < 2) := by omega

theorem memory (p : Params) (pass lane slice index : Nat) (s : FillState)
    (active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ index) :
    (fillBlock p pass slice lane index s).memory =
      VG.Proof.Argon2.FillStep.update p pass lane slice index s.memory (VG.Proof.Argon2.FillStep.random p pass lane slice index s.memory) := by
  rw [fillBlock, ite_eq_right (VG.Proof.Argon2.FillStep.not_skipped pass slice index active)]
  rfl

theorem indices (p : Params) (pass lane slice index : Nat) (s : FillState)
    (active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ index) :
    (fillBlock p pass slice lane index s).indices = if independent p pass slice then s.indices
      else reference p pass lane slice index (VG.Proof.Argon2.FillStep.random p pass lane slice index s.memory) :: s.indices := by
  rw [fillBlock, ite_eq_right (VG.Proof.Argon2.FillStep.not_skipped pass slice index active)]
  rfl

end VG.Proof.Argon2.FillStep

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.Iterations`. -/
section

/-! Pass folds used by the outer filling-loop invariant. -/

namespace VG.Proof.Argon2

open VG.Spec.Argon2

def iterations (p : Params) (start count : Nat) (state : FillState) : FillState :=
  (List.range' start count).foldl (fillPass p) state

theorem iterations_zero (p : Params) (start : Nat) (state : FillState) : VG.Proof.Argon2.iterations p start 0 state = state := rfl

theorem iterations_succ (p : Params) (start count : Nat) (state : FillState) :
    VG.Proof.Argon2.iterations p start (count + 1) state = VG.Proof.Argon2.iterations p (start + 1) count (fillPass p state start) := by
  unfold VG.Proof.Argon2.iterations
  rw [List.range'_succ, List.foldl_cons]

theorem iterations_fill (p : Params) (password salt secret ad : List Byte) :
    VG.Proof.Argon2.iterations p 0 p.passes (initMemory p (initialHash p password salt secret ad)) = fill p password salt secret ad := by
  unfold VG.Proof.Argon2.iterations fill
  rw [List.range_eq_range']

end VG.Proof.Argon2

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.Segment`. -/
section

/-! Segment folds used by the filling-loop invariant. -/

namespace VG.Proof.Argon2

open VG.Spec.Argon2

def segment (p : Params) (pass lane slice start count : Nat) (state : FillState) : FillState :=
  (List.range' start count).foldl (fun state index => fillBlock p pass slice lane index state) state

theorem segment_zero (p : Params) (pass lane slice start : Nat) (state : FillState) :
    VG.Proof.Argon2.segment p pass lane slice start 0 state = state := rfl

theorem segment_succ (p : Params) (pass lane slice start count : Nat) (state : FillState) :
    VG.Proof.Argon2.segment p pass lane slice start (count + 1) state =
      VG.Proof.Argon2.segment p pass lane slice (start + 1) count (fillBlock p pass slice lane start state) := by
  unfold VG.Proof.Argon2.segment
  rw [List.range'_succ, List.foldl_cons]

theorem segment_append (p : Params) (pass lane slice start a b : Nat) (state : FillState) :
    VG.Proof.Argon2.segment p pass lane slice start (a + b) state =
      VG.Proof.Argon2.segment p pass lane slice (start + a) b (VG.Proof.Argon2.segment p pass lane slice start a state) := by
  unfold VG.Proof.Argon2.segment
  rw [← List.range'_append_1, List.foldl_append]

end VG.Proof.Argon2

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.Lanes`. -/
section

/-! Lane folds used by the public filling loops. -/

namespace VG.Proof.Argon2

open VG.Spec.Argon2

def lanes (p : Params) (pass slice start count : Nat) (state : FillState) : FillState :=
  (List.range' start count).foldl (fun state lane => VG.Proof.Argon2.segment p pass lane slice 0 p.segmentLen state) state

theorem lanes_zero (p : Params) (pass slice start : Nat) (state : FillState) :
    VG.Proof.Argon2.lanes p pass slice start 0 state = state := rfl

theorem lanes_succ (p : Params) (pass slice start count : Nat) (state : FillState) :
    VG.Proof.Argon2.lanes p pass slice start (count + 1) state =
      VG.Proof.Argon2.lanes p pass slice (start + 1) count (VG.Proof.Argon2.segment p pass start slice 0 p.segmentLen state) := by
  unfold VG.Proof.Argon2.lanes
  rw [List.range'_succ, List.foldl_cons]

end VG.Proof.Argon2

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.Slices`. -/
section

/-! Slice folds expose the reviewed filling pass without changing its specification. -/

namespace VG.Proof.Argon2

open VG.Spec.Argon2

def slices (p : Params) (pass start count : Nat) (state : FillState) : FillState :=
  (List.range' start count).foldl (fun state slice => VG.Proof.Argon2.lanes p pass slice 0 p.lanes state) state

theorem slices_zero (p : Params) (pass start : Nat) (state : FillState) : VG.Proof.Argon2.slices p pass start 0 state = state := rfl

theorem slices_succ (p : Params) (pass start count : Nat) (state : FillState) :
    VG.Proof.Argon2.slices p pass start (count + 1) state = VG.Proof.Argon2.slices p pass (start + 1) count (VG.Proof.Argon2.lanes p pass start 0 p.lanes state) := by
  unfold VG.Proof.Argon2.slices
  rw [List.range'_succ, List.foldl_cons]

theorem slices_pass (p : Params) (pass : Nat) (state : FillState) : VG.Proof.Argon2.slices p pass 0 4 state = fillPass p state pass := by
  unfold VG.Proof.Argon2.slices VG.Proof.Argon2.lanes VG.Proof.Argon2.segment fillPass
  simp only [List.range_eq_range']

end VG.Proof.Argon2

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.SegmentIndices`. -/
section

/-! The reference log exposes exactly one coordinate per dependent active cell. -/

namespace VG.Proof.Argon2

open VG.Spec.Argon2

theorem segment_indices_drop (p : Params) (pass lane slice start count : Nat) (state : FillState)
    (active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ start) (dependent : independent p pass slice = false) :
    (VG.Proof.Argon2.segment p pass lane slice start count state).indices.drop count = state.indices := by
  induction count generalizing start state with
  | zero => rfl
  | succ n ih =>
    rw [VG.Proof.Argon2.segment_succ]
    have next : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ start + 1 := by omega
    rw [← List.drop_drop, ih (start + 1) (fillBlock p pass slice lane start state) next]
    rw [FillStep.indices p pass lane slice start state active]
    simp only [dependent, Bool.false_eq_true, ite_false, List.drop_succ_cons, List.drop_zero]

theorem segment_first_reference (p : Params) (pass lane slice start count : Nat)
    (leftState rightState : FillState) (active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ start)
    (indices : (VG.Proof.Argon2.segment p pass lane slice start (count + 1) leftState).indices =
      (VG.Proof.Argon2.segment p pass lane slice start (count + 1) rightState).indices)
    (dependent : independent p pass slice = false) :
    reference p pass lane slice start (FillStep.random p pass lane slice start leftState.memory) =
      reference p pass lane slice start (FillStep.random p pass lane slice start rightState.memory) := by
  have dropped := congrArg (List.drop count) indices
  rw [VG.Proof.Argon2.segment_succ, VG.Proof.Argon2.segment_succ,
    VG.Proof.Argon2.segment_indices_drop p pass lane slice (start + 1) count _ (by omega) dependent,
    VG.Proof.Argon2.segment_indices_drop p pass lane slice (start + 1) count _ (by omega) dependent,
    FillStep.indices p pass lane slice start leftState active,
    FillStep.indices p pass lane slice start rightState active] at dropped
  simp only [dependent, Bool.false_eq_true, ite_false] at dropped
  exact (List.cons.inj dropped).1

end VG.Proof.Argon2

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.SegmentStart`. -/
section

/-! The first two cells of pass zero's first segment are already initialized. -/

namespace VG.Proof.Argon2

open VG.Spec.Argon2

def segmentStart (pass slice : Nat) : Nat := if pass = 0 ∧ slice = 0 then 2 else 0

theorem segment_first_two (p : Params) (lane : Nat) (state : FillState) :
    VG.Proof.Argon2.segment p 0 lane 0 0 2 state = state := by
  rw [VG.Proof.Argon2.segment_succ, VG.Proof.Argon2.segment_succ, VG.Proof.Argon2.segment_zero]
  simp only [fillBlock, Nat.reduceAdd, and_self, Nat.reduceLT, ite_true]

theorem segment_start (p : Params) (pass lane slice : Nat) (state : FillState) (minimum : 2 ≤ p.segmentLen) :
    VG.Proof.Argon2.segment p pass lane slice 0 p.segmentLen state =
      VG.Proof.Argon2.segment p pass lane slice (VG.Proof.Argon2.segmentStart pass slice) (p.segmentLen - VG.Proof.Argon2.segmentStart pass slice) state := by
  by_cases first : pass = 0 ∧ slice = 0
  · obtain ⟨rfl, rfl⟩ := first
    have append := VG.Proof.Argon2.segment_append p 0 lane 0 0 2 (p.segmentLen - 2) state
    rw [show 2 + (p.segmentLen - 2) = p.segmentLen by omega, VG.Proof.Argon2.segment_first_two] at append
    exact append
  · simp only [VG.Proof.Argon2.segmentStart, first, ite_false, Nat.sub_zero]

end VG.Proof.Argon2

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.LanesIndices`. -/
section

/-! Recover each segment's reference log from the complete lane fold. -/

namespace VG.Proof.Argon2

open VG.Spec.Argon2

def segmentReferences (p : Params) (pass slice : Nat) : Nat :=
  if independent p pass slice then 0 else p.segmentLen - VG.Proof.Argon2.segmentStart pass slice

theorem fillBlock_independent_indices (p : Params) (pass lane slice index : Nat) (state : FillState)
    (mode : independent p pass slice = true) : (fillBlock p pass slice lane index state).indices = state.indices := by
  unfold fillBlock
  split
  · rfl
  · simp only [mode, ite_true]

theorem segment_independent_indices (p : Params) (pass lane slice start count : Nat) (state : FillState)
    (mode : independent p pass slice = true) : (VG.Proof.Argon2.segment p pass lane slice start count state).indices = state.indices := by
  induction count generalizing start state with
  | zero => rfl
  | succ n ih =>
    rw [VG.Proof.Argon2.segment_succ, ih, VG.Proof.Argon2.fillBlock_independent_indices p pass lane slice start state mode]

theorem segment_references_drop (p : Params) (pass lane slice : Nat) (state : FillState)
    (minimum : 2 ≤ p.segmentLen) :
    (VG.Proof.Argon2.segment p pass lane slice 0 p.segmentLen state).indices.drop (VG.Proof.Argon2.segmentReferences p pass slice) = state.indices := by
  cases mode : independent p pass slice
  · rw [VG.Proof.Argon2.segment_start p pass lane slice state minimum]
    change (VG.Proof.Argon2.segment p pass lane slice (VG.Proof.Argon2.segmentStart pass slice) (p.segmentLen - VG.Proof.Argon2.segmentStart pass slice) state).indices.drop
      (if independent p pass slice then 0 else p.segmentLen - VG.Proof.Argon2.segmentStart pass slice) = state.indices
    simp only [mode, Bool.false_eq_true, ite_false]
    apply VG.Proof.Argon2.segment_indices_drop _ _ _ _ _ _ _ _ mode
    unfold VG.Proof.Argon2.segmentStart; split <;> omega
  · rw [VG.Proof.Argon2.segment_independent_indices p pass lane slice 0 p.segmentLen state mode]
    simp only [VG.Proof.Argon2.segmentReferences, mode, ite_true, List.drop_zero]

theorem lanes_indices_drop (p : Params) (pass slice start count : Nat) (state : FillState)
    (minimum : 2 ≤ p.segmentLen) :
    (VG.Proof.Argon2.lanes p pass slice start count state).indices.drop (count * VG.Proof.Argon2.segmentReferences p pass slice) = state.indices := by
  induction count generalizing start state with
  | zero => rw [Nat.zero_mul, VG.Proof.Argon2.lanes_zero, List.drop_zero]
  | succ n ih =>
    rw [VG.Proof.Argon2.lanes_succ, Nat.add_mul, Nat.one_mul, ← List.drop_drop,
      ih, VG.Proof.Argon2.segment_references_drop p pass start slice state minimum]

theorem lanes_first_segment (p : Params) (pass slice start count : Nat) (leftState rightState : FillState)
    (minimum : 2 ≤ p.segmentLen)
    (indices : (VG.Proof.Argon2.lanes p pass slice start (count + 1) leftState).indices =
      (VG.Proof.Argon2.lanes p pass slice start (count + 1) rightState).indices) :
    (VG.Proof.Argon2.segment p pass start slice 0 p.segmentLen leftState).indices =
      (VG.Proof.Argon2.segment p pass start slice 0 p.segmentLen rightState).indices := by
  have dropped := congrArg (List.drop (count * VG.Proof.Argon2.segmentReferences p pass slice)) indices
  rw [VG.Proof.Argon2.lanes_succ, VG.Proof.Argon2.lanes_succ, VG.Proof.Argon2.lanes_indices_drop p pass slice (start + 1) count _ minimum,
    VG.Proof.Argon2.lanes_indices_drop p pass slice (start + 1) count _ minimum] at dropped
  exact dropped

end VG.Proof.Argon2

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.SlicesIndices`. -/
section

/-! Reference-log suffixes span slices with different public addressing modes. -/

namespace VG.Proof.Argon2

open VG.Spec.Argon2

def sliceReferences (p : Params) (pass slice : Nat) : Nat := p.lanes * VG.Proof.Argon2.segmentReferences p pass slice

def slicesReferences (p : Params) (pass start : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => VG.Proof.Argon2.sliceReferences p pass start + VG.Proof.Argon2.slicesReferences p pass (start + 1) n

theorem slices_indices_drop (p : Params) (pass start count : Nat) (state : FillState)
    (minimum : 2 ≤ p.segmentLen) :
    (VG.Proof.Argon2.slices p pass start count state).indices.drop (VG.Proof.Argon2.slicesReferences p pass start count) = state.indices := by
  induction count generalizing start state with
  | zero => rfl
  | succ n ih =>
    rw [VG.Proof.Argon2.slices_succ, VG.Proof.Argon2.slicesReferences,
      show VG.Proof.Argon2.sliceReferences p pass start + VG.Proof.Argon2.slicesReferences p pass (start + 1) n =
        VG.Proof.Argon2.slicesReferences p pass (start + 1) n + VG.Proof.Argon2.sliceReferences p pass start from Nat.add_comm _ _,
      ← List.drop_drop, ih]
    exact VG.Proof.Argon2.lanes_indices_drop p pass start 0 p.lanes state minimum

theorem slices_first_lane_fold (p : Params) (pass start count : Nat) (leftState rightState : FillState)
    (minimum : 2 ≤ p.segmentLen)
    (indices : (VG.Proof.Argon2.slices p pass start (count + 1) leftState).indices =
      (VG.Proof.Argon2.slices p pass start (count + 1) rightState).indices) :
    (VG.Proof.Argon2.lanes p pass start 0 p.lanes leftState).indices = (VG.Proof.Argon2.lanes p pass start 0 p.lanes rightState).indices := by
  have dropped := congrArg (List.drop (VG.Proof.Argon2.slicesReferences p pass (start + 1) count)) indices
  rw [VG.Proof.Argon2.slices_succ, VG.Proof.Argon2.slices_succ, VG.Proof.Argon2.slices_indices_drop p pass (start + 1) count _ minimum,
    VG.Proof.Argon2.slices_indices_drop p pass (start + 1) count _ minimum] at dropped
  exact dropped

end VG.Proof.Argon2

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.IterationsIndices`. -/
section

/-! Recover each pass's reviewed reference log from the complete filling log. -/

namespace VG.Proof.Argon2

open VG.Spec.Argon2

def passReferences (p : Params) (pass : Nat) : Nat := VG.Proof.Argon2.slicesReferences p pass 0 4

def iterationsReferences (p : Params) (start : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => VG.Proof.Argon2.passReferences p start + VG.Proof.Argon2.iterationsReferences p (start + 1) n

theorem pass_indices_drop (p : Params) (pass : Nat) (state : FillState) (minimum : 2 ≤ p.segmentLen) :
    (fillPass p state pass).indices.drop (VG.Proof.Argon2.passReferences p pass) = state.indices := by
  rw [← VG.Proof.Argon2.slices_pass p pass state]
  exact VG.Proof.Argon2.slices_indices_drop p pass 0 4 state minimum

theorem iterations_indices_drop (p : Params) (start count : Nat) (state : FillState) (minimum : 2 ≤ p.segmentLen) :
    (VG.Proof.Argon2.iterations p start count state).indices.drop (VG.Proof.Argon2.iterationsReferences p start count) = state.indices := by
  induction count generalizing start state with
  | zero => rfl
  | succ n ih =>
    rw [VG.Proof.Argon2.iterations_succ, VG.Proof.Argon2.iterationsReferences,
      show VG.Proof.Argon2.passReferences p start + VG.Proof.Argon2.iterationsReferences p (start + 1) n =
        VG.Proof.Argon2.iterationsReferences p (start + 1) n + VG.Proof.Argon2.passReferences p start from Nat.add_comm _ _,
      ← List.drop_drop, ih, VG.Proof.Argon2.pass_indices_drop p start state minimum]

theorem iterations_first_pass (p : Params) (start count : Nat) (leftState rightState : FillState)
    (minimum : 2 ≤ p.segmentLen)
    (indices : (VG.Proof.Argon2.iterations p start (count + 1) leftState).indices =
      (VG.Proof.Argon2.iterations p start (count + 1) rightState).indices) :
    (fillPass p leftState start).indices = (fillPass p rightState start).indices := by
  have dropped := congrArg (List.drop (VG.Proof.Argon2.iterationsReferences p (start + 1) count)) indices
  rw [VG.Proof.Argon2.iterations_succ, VG.Proof.Argon2.iterations_succ, VG.Proof.Argon2.iterations_indices_drop p (start + 1) count _ minimum,
    VG.Proof.Argon2.iterations_indices_drop p (start + 1) count _ minimum] at dropped
  exact dropped

end VG.Proof.Argon2

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.References`. -/
section

/-! The reviewed flattened reference log determines every lane/column pair. -/

namespace VG.Proof.Argon2

open VG.Spec.Argon2

def Columns (q : Nat) (s : FillState) : Prop := ∀ ref ∈ s.indices, ref.2 < q

theorem fold_columns {α : Type} (q : Nat) (f : FillState → α → FillState)
    (step : ∀ s a, VG.Proof.Argon2.Columns q s → VG.Proof.Argon2.Columns q (f s a)) (xs : List α) (s : FillState) (h : VG.Proof.Argon2.Columns q s) :
    VG.Proof.Argon2.Columns q (xs.foldl f s) := by
  induction xs generalizing s with
  | nil => exact h
  | cons x xs ih => exact ih (f s x) (step s x h)

theorem fillBlock_columns (p : Params) (positive : 0 < p.laneLen)
    (pass slice lane index : Nat) (s : FillState) (h : VG.Proof.Argon2.Columns p.laneLen s) :
    VG.Proof.Argon2.Columns p.laneLen (fillBlock p pass slice lane index s) := by
  by_cases skipped : pass = 0 ∧ slice = 0 ∧ index < 2
  · rw [fillBlock, ite_eq_left skipped]; exact h
  · unfold VG.Proof.Argon2.Columns
    rw [FillStep.indices p pass lane slice index s (by omega)]
    split
    · exact h
    · intro ref hr
      simp only [List.mem_cons] at hr
      rcases hr with rfl | hr
      · change _ % p.laneLen < p.laneLen
        exact Nat.mod_lt _ positive
      · exact h ref hr

theorem fillPass_columns (p : Params) (positive : 0 < p.laneLen) (s : FillState) (pass : Nat)
    (h : VG.Proof.Argon2.Columns p.laneLen s) : VG.Proof.Argon2.Columns p.laneLen (fillPass p s pass) := by
  unfold fillPass
  apply VG.Proof.Argon2.fold_columns
  · intro s slice hs
    apply VG.Proof.Argon2.fold_columns
    · intro s lane hs
      exact VG.Proof.Argon2.fold_columns _ _ (fun s index hs => VG.Proof.Argon2.fillBlock_columns p positive pass slice lane index s hs) _ s hs
    · exact hs
  · exact h

theorem fill_columns (p : Params) (positive : 0 < p.laneLen) (password salt secret ad : List Byte) :
    VG.Proof.Argon2.Columns p.laneLen (fill p password salt secret ad) := by
  unfold fill
  apply VG.Proof.Argon2.fold_columns _ _ (fun s pass hs => VG.Proof.Argon2.fillPass_columns p positive s pass hs)
  intro ref hr
  exact False.elim (List.not_mem_nil hr)

def flattenRef (q : Nat) (ref : Nat × Nat) : Nat := ref.1 * q + ref.2

def decodeRef (q n : Nat) : Nat × Nat := (n / q, n % q)

theorem decode_flatten (q : Nat) (positive : 0 < q) (ref : Nat × Nat) (bound : ref.2 < q) :
    VG.Proof.Argon2.decodeRef q (VG.Proof.Argon2.flattenRef q ref) = ref := by
  unfold VG.Proof.Argon2.decodeRef VG.Proof.Argon2.flattenRef
  rw [Nat.mul_comm ref.1 q, Nat.mul_add_div positive,
    Nat.div_eq_of_lt bound, Nat.add_zero, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt bound]

theorem decode_list (q : Nat) (positive : 0 < q) (xs : List (Nat × Nat))
    (bound : ∀ ref ∈ xs, ref.2 < q) : (xs.map (VG.Proof.Argon2.flattenRef q)).map (VG.Proof.Argon2.decodeRef q) = xs := by
  induction xs with
  | nil => rfl
  | cons ref xs ih =>
    simp only [List.map_cons]
    rw [VG.Proof.Argon2.decode_flatten q positive ref (bound ref (List.mem_cons_self ..)),
      ih (fun r hr => bound r (List.mem_cons_of_mem ref hr))]

theorem references_injective (p : Params) (positive : 0 < p.laneLen)
    (password₁ salt₁ secret₁ ad₁ password₂ salt₂ secret₂ ad₂ : List Byte)
    (same : references p password₁ salt₁ secret₁ ad₁ = references p password₂ salt₂ secret₂ ad₂) :
    (fill p password₁ salt₁ secret₁ ad₁).indices = (fill p password₂ salt₂ secret₂ ad₂).indices := by
  apply List.reverse_inj.mp
  have left := VG.Proof.Argon2.fill_columns p positive password₁ salt₁ secret₁ ad₁
  have right := VG.Proof.Argon2.fill_columns p positive password₂ salt₂ secret₂ ad₂
  have decoded := congrArg (List.map (VG.Proof.Argon2.decodeRef p.laneLen)) same
  change ((fill p password₁ salt₁ secret₁ ad₁).indices.reverse.map (VG.Proof.Argon2.flattenRef p.laneLen)).map _ =
    ((fill p password₂ salt₂ secret₂ ad₂).indices.reverse.map (VG.Proof.Argon2.flattenRef p.laneLen)).map _ at decoded
  rw [VG.Proof.Argon2.decode_list p.laneLen positive _ (fun ref hr => left ref (List.mem_reverse.mp hr)),
    VG.Proof.Argon2.decode_list p.laneLen positive _ (fun ref hr => right ref (List.mem_reverse.mp hr))] at decoded
  exact decoded

end VG.Proof.Argon2

end
