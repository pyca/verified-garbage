module

public import VerifiedGarbage.Impl.Dsa.X86.Checks
public import VerifiedGarbage.Proof.Mont.X86.PowerTiming

/-! # Secret-independent traces of DSA comparison masks -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Dsa.X86 VG.Proof.Mont.X86.Dynamic

private theorem check_parts {α : Type} (xs : List α) (f : α → List Instr)
    (h : ∀ x, taint.checkBlock (workspaceTaint false) (f x) = some (workspaceTaint false)) :
    taint.checkBlock (workspaceTaint false) (xs.flatMap f) = some (workspaceTaint false) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.flatMap_cons, exponent_check_append taint (workspaceTaint false), h]
    exact ih

theorem lessThan_check (n a b : Nat) :
    taint.checkBlock (workspaceTaint false) (lessThan n a b) = some (workspaceTaint false) := by
  unfold lessThan
  rw [exponent_check_append taint (workspaceTaint false)]
  have steps : taint.checkBlock (workspaceTaint false)
      ((List.range (2 * n)).flatMap fun j =>
        [.mov .edx (.mem (sc (a + 4 * j))), .alu (if j = 0 then .sub else .sbb) .edx (.mem (sc (b + 4 * j)))]) =
      some (workspaceTaint false) := by
    apply check_parts
    intro j
    rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (workspaceTaint false) = true from rfl)]
    change taint.checkBlock (workspaceTaint false)
      [.mov .edx (.mem (sc 0)), .alu (if j = 0 then .sub else .sbb) .edx (.mem (sc 0))] = _
    by_cases hj : j = 0 <;> simp only [hj, ite_true, ite_false] <;> rfl
  rw [steps]
  rfl

theorem nonzero_check (n a : Nat) :
    taint.checkBlock (workspaceTaint false) (nonzero n a) = some (workspaceTaint false) := by
  unfold nonzero
  rw [List.append_assoc, exponent_check_append taint (workspaceTaint false)]
  have first : taint.checkBlock (workspaceTaint false) [.mov .edx (.mem (sc a))] =
      some (workspaceTaint false) := by
    rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (workspaceTaint false) = true from rfl)]
    change taint.checkBlock (workspaceTaint false) [.mov .edx (.mem (sc 0))] = _
    rfl
  rw [first]
  dsimp only [Option.bind]
  rw [exponent_check_append taint (workspaceTaint false)]
  have middle : taint.checkBlock (workspaceTaint false)
      ((List.range (2 * n - 1)).map fun j => .alu .or .edx (.mem (sc (a + 4 * (j + 1))))) =
      some (workspaceTaint false) := by
    rw [List.map_eq_flatMap]
    apply check_parts
    intro j
    rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (workspaceTaint false) = true from rfl)]
    change taint.checkBlock (workspaceTaint false) [.alu .or .edx (.mem (sc 0))] = _
    rfl
  rw [middle]
  rfl

theorem andFlag_check (flag : Nat) :
    taint.checkBlock (workspaceTaint false) (andFlag flag) = some (workspaceTaint false) := by
  rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (workspaceTaint false) = true from rfl)]
  change taint.checkBlock (workspaceTaint false) (andFlag 0) = _
  rfl

theorem checkRange_check (n a m flag : Nat) :
    taint.checkBlock (workspaceTaint false) (checkRange n a m flag) = some (workspaceTaint false) := by
  unfold checkRange
  simp only [List.append_assoc]
  rw [exponent_check_append taint (workspaceTaint false), lessThan_check]
  dsimp only [Option.bind]
  rw [exponent_check_append taint (workspaceTaint false)]
  have mv : taint.checkBlock (workspaceTaint false) [.mov .ebx (.reg .eax)] = some (workspaceTaint false) := rfl
  rw [mv]
  dsimp only [Option.bind]
  rw [exponent_check_append taint (workspaceTaint false), nonzero_check]
  dsimp only [Option.bind]
  rw [exponent_check_append taint (workspaceTaint false)]
  have band : taint.checkBlock (workspaceTaint false) [.alu .and .edx (.reg .ebx)] = some (workspaceTaint false) := rfl
  rw [band]
  exact andFlag_check flag

theorem equal_check (n a b : Nat) :
    taint.checkBlock (workspaceTaint false) (equal n a b) = some (workspaceTaint false) := by
  unfold equal
  simp only [List.append_assoc]
  rw [exponent_check_append taint (workspaceTaint false), lessThan_check]
  dsimp only [Option.bind]
  rw [exponent_check_append taint (workspaceTaint false)]
  have mv : taint.checkBlock (workspaceTaint false) [.mov .ebx (.reg .eax)] = some (workspaceTaint false) := rfl
  rw [mv]
  dsimp only [Option.bind]
  rw [exponent_check_append taint (workspaceTaint false), lessThan_check]
  rfl

theorem equal_constantTime (n a b : Nat) :
    ConstantTime isa (fun _ => True) (VG.X86.Taint.Agree (workspaceTaint false)) (.block (equal n a b)) := by
  refine VG.Taint.constantTime (A := taint) (workspaceTaint false) (fun _ _ _ _ h => h) (hc := .block []) ?_
  change (taint.checkBlock (workspaceTaint false) (equal n a b)).isSome = true
  rw [equal_check]
  rfl

end VG.Proof.Dsa.X86
