module

public import VerifiedGarbage.Impl.Mont.X86.Dynamic
public import VerifiedGarbage.Impl.Mont.X86.Inverse
public import VerifiedGarbage.Proof.Framework.X86.TaintErase

/-! # Taint checks for runtime-modulus Montgomery arithmetic on x86 -/

@[expose] public section

namespace VG.Proof.Mont.X86.Dynamic
open VG VG.X86 VG.Impl.Mont.X86

/-- Public workspace and row pointers, with all arithmetic values secret. -/
def rowTaint (counter : Bool) : VG.X86.Taint.T := { regs := .ofList ([.edi, .ebp] ++ if counter then [.esi] else []), flags := false }

def rowEndTaint (counter : Bool) : VG.X86.Taint.T := { regs := .ofList ([.edi, .ebp, .edx] ++ if counter then [.esi] else []), flags := true }

variable (counter : Bool)

private theorem check_append {M : ISA} (A : VG.Taint M) (τ : A.T) (a b : List M.Instr) :
    A.checkBlock τ (a ++ b) = (A.checkBlock τ a).bind (A.checkBlock · b) := by
  induction a generalizing τ with
  | nil => rfl
  | cons i is ih =>
    change (A.step τ i).bind (fun t => A.checkBlock t (is ++ b)) =
      ((A.step τ i).bind (fun t => A.checkBlock t is)).bind (A.checkBlock · b)
    rw [Option.bind_assoc]
    simp only [ih]

private theorem check_flatMap {M : ISA} (A : VG.Taint M) (τ : A.T)
    {α : Type} (xs : List α) (f : α → List M.Instr)
    (h : ∀ x, A.checkBlock τ (f x) = some τ) :
    A.checkBlock τ (xs.flatMap f) = some τ := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.flatMap_cons, check_append A τ, h, Option.bind_some, ih]

/-- A word multiply-add preserves public address registers. -/
theorem mulStep_taint (acc b j : Nat) :
    taint.checkBlock (rowTaint counter) (mulStep acc b j) = some (rowTaint counter) := by
  rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (rowTaint counter) = true from rfl)]
  change taint.checkBlock (rowTaint counter) (mulStep 0 0 0) = _
  cases counter <;> rfl

/-- Loading the inverse does not publish the inverse or accumulator. -/
theorem redDigit_taint (acc inv : Nat) :
    taint.checkBlock (rowTaint counter) (VG.Impl.Mont.X86.Dynamic.redDigit acc inv) = some (rowTaint counter) := by
  rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (rowTaint counter) = true from rfl)]
  change taint.checkBlock (rowTaint counter) (VG.Impl.Mont.X86.Dynamic.redDigit 0 0) = _
  cases counter <;> rfl

/-- A complete multiply-add row, including carry propagation. -/
theorem mulRow_taint (acc b : Nat) {N : Nat} (hN : 0 < N) :
    taint.checkBlock (rowTaint counter) (mulRow acc b N) = some (rowTaint counter) := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
  -- The first step consumes the initially public zero carry.
  have first : taint.checkBlock (rowTaint counter)
      ([.mov .ebx (.imm 0)] ++ mulStep acc b 0) = some (rowTaint counter) := by
    rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (rowTaint counter) = true from rfl)]
    change taint.checkBlock (rowTaint counter) ([.mov .ebx (.imm 0)] ++ mulStep 0 0 0) = _
    cases counter <;> rfl
  have shift (k : Nat) : taint.checkBlock (rowTaint counter)
      ((List.range k).flatMap fun j => mulStep acc b (j + 1)) = some (rowTaint counter) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, check_append taint (rowTaint counter), ih]
      exact mulStep_taint counter acc b (k + 1)
  simp only [mulRow, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map,
    ]
  change taint.checkBlock (rowTaint counter)
    (([.mov .ebx (.imm 0)] ++ mulStep acc b 0) ++
      ((List.range k).flatMap fun j => mulStep acc b (j + 1)) ++ carryUp acc (k + 1)) = _
  rw [List.append_assoc, check_append taint (rowTaint counter), first]
  change taint.checkBlock (rowTaint counter) (_ ++ _) = _
  rw [check_append taint (rowTaint counter)]
  change (taint.checkBlock (rowTaint counter) ((List.range k).flatMap fun j => mulStep acc b (j + 1))).bind _ = _
  rw [shift]
  change taint.checkBlock (rowTaint counter) (carryUp acc (k + 1)) = _
  rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (rowTaint counter) = true from rfl)]
  change taint.checkBlock (rowTaint counter) (KList.map Instr.erase (carryUp 0 0)) = _
  cases counter <;> rfl

/-- A row ends with a public loop comparison. The loaded modulus,
inverse, multiplicands, accumulator, and carry are all treated as secret. -/
theorem row_taint (N acc a b mo inv : Nat) (hN : 0 < N) :
    taint.checkBlock (rowTaint counter) (VG.Impl.Mont.X86.Dynamic.row N acc a b mo inv) = some (rowEndTaint counter) := by
  unfold VG.Impl.Mont.X86.Dynamic.row
  simp only [List.append_assoc]
  rw [check_append taint (rowTaint counter)]
  have load : taint.checkBlock (rowTaint counter) [.mov .ecx (.mem (at_ .ebp a))] = some (rowTaint counter) := by
    rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (rowTaint counter) = true from rfl)]
    change taint.checkBlock (rowTaint counter) [.mov .ecx (.mem (at_ .ebp 0))] = _
    cases counter <;> rfl
  rw [load]
  dsimp only [Option.bind]
  rw [check_append taint (rowTaint counter), mulRow_taint counter acc b hN]
  dsimp only [Option.bind]
  rw [check_append taint (rowTaint counter), redDigit_taint counter]
  dsimp only [Option.bind]
  rw [check_append taint (rowTaint counter), mulRow_taint counter acc mo hN]
  dsimp only [Option.bind]
  rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (rowTaint counter) = true from rfl)]
  change taint.checkBlock (rowTaint counter)
    [.alu .add .ebp (.imm 0), .mov .edx (.reg .edi),
     .alu .add .edx (.imm 0), .alu .cmp .ebp (.reg .edx)] = _
  cases counter <;> rfl

/-- Constant-time execution of the multiplication loop for every positive
public width and every workspace layout. -/
theorem loop_constantTime_withCounter (N acc a b mo inv : Nat) (hN : 0 < N) :
    ConstantTime isa (fun _ => True) (VG.X86.Taint.Agree (rowTaint counter))
      (.loop (.block (VG.Impl.Mont.X86.Dynamic.row N acc a b mo inv)) .ne) := by
  refine VG.Taint.constantTime (A := taint) (rowTaint counter) (fun _ _ _ _ h => h)
    (hc := .loop (rowTaint counter) (.block [])) ?_
  change ((if taint.le (rowTaint counter) (rowTaint counter) then
    (taint.checkBlock (rowTaint counter) (VG.Impl.Mont.X86.Dynamic.row N acc a b mo inv)).bind
      (fun t => if taint.le (rowTaint counter) t && taint.condPub t .ne then some t else none)
    else none).isSome) = true
  rw [row_taint counter N acc a b mo inv hN]
  cases counter <;> rfl

/-- Final conditional subtraction and selection do not branch on the borrow. -/
theorem csub_taint (M : VG.Impl.Mont.Mod) (src out : Nat) :
    taint.checkBlock (rowTaint counter) (csub M src out) = some (rowTaint counter) := by
  have df : taint.checkBlock (rowTaint counter) (diffs M src) = some (rowTaint counter) := by
    unfold diffs
    apply check_flatMap taint (rowTaint counter)
    intro j
    split <;>
      rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (rowTaint counter) = true from rfl)] <;>
      change taint.checkBlock (rowTaint counter) _ = some (rowTaint counter)
    · change taint.checkBlock (rowTaint counter)
        [.mov .eax (.mem (sc 0)), .alu .sub .eax (.mem (sc 0)), .store (sc 0) .eax] = _
      cases counter <;> rfl
    · change taint.checkBlock (rowTaint counter)
        [.mov .eax (.mem (sc 0)), .alu .sbb .eax (.mem (sc 0)), .store (sc 0) .eax] = _
      cases counter <;> rfl
  have sl : taint.checkBlock (rowTaint counter) (selects M src out) = some (rowTaint counter) := by
    unfold selects
    apply check_flatMap taint (rowTaint counter)
    intro j
    rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (rowTaint counter) = true from rfl)]
    change taint.checkBlock (rowTaint counter)
      [.mov .ebx (.mem (sc 0)), .mov .edx (.mem (sc 0)), .alu .xor .edx (.reg .ebx),
       .alu .and .edx (.reg .eax), .alu .xor .ebx (.reg .edx), .store (sc 0) .ebx] = _
    cases counter <;> rfl
  unfold csub
  rw [List.append_assoc, check_append taint (rowTaint counter), df]
  dsimp only [Option.bind]
  rw [check_append taint (rowTaint counter)]
  have mask : taint.checkBlock (rowTaint counter)
      [.mov .eax (.mem (sc (src + 4 * words M))), .alu .sbb .eax (.imm 0),
       .alu .sbb .eax (.reg .eax), .alu .xor .eax (.imm (-1))] = some (rowTaint counter) := by
    rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (rowTaint counter) = true from rfl)]
    change taint.checkBlock (rowTaint counter)
      [.mov .eax (.mem (sc 0)), .alu .sbb .eax (.imm 0),
       .alu .sbb .eax (.reg .eax), .alu .xor .eax (.imm 0)] = _
    cases counter <;> rfl
  rw [mask]
  exact sl

/-- Only the workspace pointer is public on entry. -/
def workspaceTaint (counter : Bool) : VG.X86.Taint.T := { regs := .ofList ([.edi] ++ if counter then [.esi] else []), flags := false }

def zeroTaint (counter : Bool) : VG.X86.Taint.T := { regs := .ofList ([.edi, .eax] ++ if counter then [.esi] else []), flags := false }

def initializedTaint (counter : Bool) : VG.X86.Taint.T := { regs := .ofList ([.edi, .eax, .ebp] ++ if counter then [.esi] else []), flags := false }

/-- Zeroing the accumulator publishes its zero register, but no input word. -/
theorem zeros_taint (acc k : Nat) :
    taint.checkBlock (workspaceTaint counter) (zeros acc k) = some (zeroTaint counter) := by
  have stores : taint.checkBlock (zeroTaint counter)
      ((List.range k).map fun j => .store (sc (acc + 4 * j)) .eax) = some (zeroTaint counter) := by
    rw [List.map_eq_flatMap]
    apply check_flatMap taint (zeroTaint counter)
    intro j
    rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (zeroTaint counter) = true from rfl)]
    change taint.checkBlock (zeroTaint counter) [.store (sc 0) .eax] = _
    cases counter <;> rfl
  unfold zeros
  change (taint.step (workspaceTaint counter) (.mov .eax (.imm 0))).bind _ = _
  have h : taint.step (workspaceTaint counter) (.mov .eax (.imm 0)) = some (zeroTaint counter) := by cases counter <;> rfl
  rw [h]
  exact stores

/-- The multiplication prefix sets both pointers independently of all operands. -/
theorem initialize_taint (acc k : Nat) :
    taint.checkBlock (workspaceTaint counter) (zeros acc k ++ ([.mov .ebp (.reg .edi)] : List Instr)) =
      some (initializedTaint counter) := by
  rw [check_append taint (workspaceTaint counter), zeros_taint counter]
  cases counter <;> rfl

/-- A compositional certificate also preserves the public exponent counter. -/
def mulHint (counter : Bool) : VG.Taint.Hint VG.X86.Taint.T :=
  .seq (rowTaint counter) (.block [])
    (.seq (rowTaint counter) (.loop (rowTaint counter) (.block [])) (.block []))

theorem mul_check (M : VG.Impl.Mont.Mod) (inv acc out a b : Nat) (hN : 0 < words M) :
    VG.Taint.check taint (workspaceTaint counter)
      (VG.Impl.Mont.X86.Dynamic.mul M inv acc out a b) (mulHint counter) = some (rowTaint counter) := by
  unfold mulHint
  unfold VG.Impl.Mont.X86.Dynamic.mul
  simp only [VG.Taint.check, VG.Taint.checkChunks]
  rw [initialize_taint counter]
  dsimp only [Option.bind]
  have le₀ : taint.le (rowTaint counter) (initializedTaint counter) = true := by cases counter <;> rfl
  have le₁ : taint.le (rowTaint counter) (rowTaint counter) = true := by cases counter <;> rfl
  rw [le₀, le₁]
  simp only [ite_true]
  rw [row_taint counter (words M) acc a b M.mo inv hN]
  dsimp only [Option.bind]
  have le₂ : taint.le (rowTaint counter) (rowEndTaint counter) = true := by cases counter <;> rfl
  have cond : taint.condPub (rowEndTaint counter) .ne = true := by cases counter <;> rfl
  rw [le₂, cond]
  simp only [Bool.true_and, ite_true]
  rw [le₂]
  simp only [ite_true]
  rw [csub_taint counter]

/-- The full multiplication has secret-independent branches and addresses,
including its initialization and final conditional subtraction. -/
theorem mul_constantTime_withCounter (M : VG.Impl.Mont.Mod) (inv acc out a b : Nat) (hN : 0 < words M) :
    ConstantTime isa (fun _ => True) (VG.X86.Taint.Agree (workspaceTaint counter))
      (VG.Impl.Mont.X86.Dynamic.mul M inv acc out a b) := by
  refine VG.Taint.constantTime (A := taint) (workspaceTaint counter) (fun _ _ _ _ h => h)
    (hc := .seq (rowTaint counter) (.block [])
      (.seq (rowTaint counter) (.loop (rowTaint counter) (.block [])) (.block []))) ?_
  change (VG.Taint.check taint (workspaceTaint counter)
    (VG.Impl.Mont.X86.Dynamic.mul M inv acc out a b) (mulHint counter)).isSome = true
  rw [mul_check counter M inv acc out a b hN]
  rfl

/-- Newton iteration preserves the only public register, the workspace pointer. -/
theorem newton_taint :
    taint.checkBlock (workspaceTaint counter) VG.Impl.Mont.X86.Dynamic.newton = some (workspaceTaint counter) := by
  cases counter <;> rfl

private theorem check_append_of {M : ISA} (A : VG.Taint M) (τ : A.T)
    {a b : List M.Instr} (ha : A.checkBlock τ a = some τ) (hb : A.checkBlock τ b = some τ) :
    A.checkBlock τ (a ++ b) = some τ := by
  rw [check_append A τ, ha, Option.bind_some]
  exact hb

theorem inverse_taint :
    taint.checkBlock (workspaceTaint counter) VG.Impl.Mont.X86.Dynamic.inverse = some (workspaceTaint counter) := by
  have cp : taint.checkBlock (workspaceTaint counter) [.mov .ecx (.reg .ebx)] = some (workspaceTaint counter) := by cases counter <;> rfl
  have neg : taint.checkBlock (workspaceTaint counter) [.mov .eax (.imm 0), .alu .sub .eax (.reg .ecx)] =
      some (workspaceTaint counter) := by cases counter <;> rfl
  exact check_append_of taint (workspaceTaint counter)
    (check_append_of taint (workspaceTaint counter)
      (check_append_of taint (workspaceTaint counter)
        (check_append_of taint (workspaceTaint counter)
          (check_append_of taint (workspaceTaint counter) cp (newton_taint counter)) (newton_taint counter)) (newton_taint counter)) (newton_taint counter)) neg

/-- Inverse initialization never publishes the loaded modulus word. -/
theorem setupInverse_taint (mo inv : Nat) :
    taint.checkBlock (workspaceTaint counter) (VG.Impl.Mont.X86.Dynamic.setupInverse mo inv) =
      some (workspaceTaint counter) := by
  have ld : taint.checkBlock (workspaceTaint counter) [.mov .ebx (.mem (sc mo))] = some (workspaceTaint counter) := by
    rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (workspaceTaint counter) = true from rfl)]
    change taint.checkBlock (workspaceTaint counter) [.mov .ebx (.mem (sc 0))] = _
    cases counter <;> rfl
  have st : taint.checkBlock (workspaceTaint counter) [.store (sc inv) .eax] = some (workspaceTaint counter) := by
    rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (workspaceTaint counter) = true from rfl)]
    change taint.checkBlock (workspaceTaint counter) [.store (sc 0) .eax] = _
    cases counter <;> rfl
  exact check_append_of taint (workspaceTaint counter)
    (check_append_of taint (workspaceTaint counter) ld (inverse_taint counter)) st

/-- Constant-time runtime inverse setup for arbitrary public workspace offsets. -/
theorem setupInverse_constantTime_withCounter (mo inv : Nat) :
    ConstantTime isa (fun _ => True) (VG.X86.Taint.Agree (workspaceTaint counter))
      (.block (VG.Impl.Mont.X86.Dynamic.setupInverse mo inv)) := by
  refine VG.Taint.constantTime (A := taint) (workspaceTaint counter) (fun _ _ _ _ h => h)
    (hc := .block []) ?_
  change (taint.checkBlock (workspaceTaint counter) (VG.Impl.Mont.X86.Dynamic.setupInverse mo inv)).isSome = true
  rw [setupInverse_taint counter]
  cases counter <;> rfl

theorem loop_constantTime (N acc a b mo inv : Nat) (hN : 0 < N) :
    ConstantTime isa (fun _ => True) (VG.X86.Taint.Agree (rowTaint false))
      (.loop (.block (VG.Impl.Mont.X86.Dynamic.row N acc a b mo inv)) .ne) :=
  loop_constantTime_withCounter false N acc a b mo inv hN

theorem mul_constantTime (M : VG.Impl.Mont.Mod) (inv acc out a b : Nat) (hN : 0 < words M) :
    ConstantTime isa (fun _ => True) (VG.X86.Taint.Agree (workspaceTaint false))
      (VG.Impl.Mont.X86.Dynamic.mul M inv acc out a b) :=
  mul_constantTime_withCounter false M inv acc out a b hN

theorem setupInverse_constantTime (mo inv : Nat) :
    ConstantTime isa (fun _ => True) (VG.X86.Taint.Agree (workspaceTaint false))
      (.block (VG.Impl.Mont.X86.Dynamic.setupInverse mo inv)) :=
  setupInverse_constantTime_withCounter false mo inv

end VG.Proof.Mont.X86.Dynamic
