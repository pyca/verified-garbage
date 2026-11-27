module

public import VerifiedGarbage.Spec.Argon2
public import VerifiedGarbage.Proof.Argon2.Segment

/-! ### `Argon2.Lanes`, which this module and modules that import it used -/

section

/-! Lane folds used by the public filling loops. -/

@[expose] public section

namespace VG.Proof.Argon2

open VG.Spec.Argon2

def lanes (p : Params) (pass slice start count : Nat) (state : FillState) : FillState :=
  (List.range' start count).foldl (fun state lane => segment p pass lane slice 0 p.segmentLen state) state

theorem lanes_zero (p : Params) (pass slice start : Nat) (state : FillState) :
    lanes p pass slice start 0 state = state := rfl

theorem lanes_succ (p : Params) (pass slice start count : Nat) (state : FillState) :
    lanes p pass slice start (count + 1) state =
      lanes p pass slice (start + 1) count (segment p pass start slice 0 p.segmentLen state) := by
  unfold lanes
  rw [List.range'_succ, List.foldl_cons]

end VG.Proof.Argon2

end

end

/-! ### `Argon2.Iterations`, which the modules that import this one used -/

section

/-! Pass folds used by the outer filling-loop invariant. -/

@[expose] public section

namespace VG.Proof.Argon2

open VG.Spec.Argon2

def iterations (p : Params) (start count : Nat) (state : FillState) : FillState :=
  (List.range' start count).foldl (fillPass p) state

theorem iterations_succ (p : Params) (start count : Nat) (state : FillState) :
    iterations p start (count + 1) state = iterations p (start + 1) count (fillPass p state start) := by
  unfold iterations
  rw [List.range'_succ, List.foldl_cons]

theorem iterations_fill (p : Params) (password salt secret ad : List Byte) :
    iterations p 0 p.passes (initMemory p (initialHash p password salt secret ad)) = fill p password salt secret ad := by
  unfold iterations fill
  rw [List.range_eq_range']

end VG.Proof.Argon2

end

end

/-! Slice folds expose the reviewed filling pass without changing its specification. -/

@[expose] public section

namespace VG.Proof.Argon2

open VG.Spec.Argon2

def slices (p : Params) (pass start count : Nat) (state : FillState) : FillState :=
  (List.range' start count).foldl (fun state slice => lanes p pass slice 0 p.lanes state) state

theorem slices_succ (p : Params) (pass start count : Nat) (state : FillState) :
    slices p pass start (count + 1) state = slices p pass (start + 1) count (lanes p pass start 0 p.lanes state) := by
  unfold slices
  rw [List.range'_succ, List.foldl_cons]

theorem slices_pass (p : Params) (pass : Nat) (state : FillState) : slices p pass 0 4 state = fillPass p state pass := by
  unfold slices lanes segment fillPass
  simp only [List.range_eq_range']

end VG.Proof.Argon2
