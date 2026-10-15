module

public import VerifiedGarbage.Impl.Mont.X86.Dynamic
public import VerifiedGarbage.Impl.Mont.X86.Inverse
public import VerifiedGarbage.Proof.Framework.X86.TaintErase

/-! # Taint checks for runtime-modulus Montgomery arithmetic on x86 -/

@[expose] public section

namespace VG.Proof.Mont.X86.Dynamic
open VG VG.X86 VG.Impl.Mont.X86

/-- Public workspace and row pointers, with all arithmetic values secret. -/
def rowTaint : VG.X86.Taint.T := { regs := .ofList [.edi, .ebp], flags := false }

def rowEndTaint : VG.X86.Taint.T := { regs := .ofList [.edi, .ebp, .edx], flags := true }

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
    taint.checkBlock rowTaint (mulStep acc b j) = some rowTaint := by
  rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases rowTaint = true from rfl)]
  change taint.checkBlock rowTaint (mulStep 0 0 0) = _
  rfl

/-- Loading the inverse does not publish the inverse or accumulator. -/
theorem redDigit_taint (acc inv : Nat) :
    taint.checkBlock rowTaint (VG.Impl.Mont.X86.Dynamic.redDigit acc inv) = some rowTaint := by
  rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases rowTaint = true from rfl)]
  change taint.checkBlock rowTaint (VG.Impl.Mont.X86.Dynamic.redDigit 0 0) = _
  rfl

/-- A complete multiply-add row, including carry propagation. -/
theorem mulRow_taint (acc b : Nat) {N : Nat} (hN : 0 < N) :
    taint.checkBlock rowTaint (mulRow acc b N) = some rowTaint := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
  -- The first step consumes the initially public zero carry.
  have first : taint.checkBlock rowTaint
      ([.mov .ebx (.imm 0)] ++ mulStep acc b 0) = some rowTaint := by
    rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases rowTaint = true from rfl)]
    change taint.checkBlock rowTaint ([.mov .ebx (.imm 0)] ++ mulStep 0 0 0) = _
    rfl
  have shift (k : Nat) : taint.checkBlock rowTaint
      ((List.range k).flatMap fun j => mulStep acc b (j + 1)) = some rowTaint := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, check_append taint rowTaint, ih]
      exact mulStep_taint acc b (k + 1)
  simp only [mulRow, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map,
    ]
  change taint.checkBlock rowTaint
    (([.mov .ebx (.imm 0)] ++ mulStep acc b 0) ++
      ((List.range k).flatMap fun j => mulStep acc b (j + 1)) ++ carryUp acc (k + 1)) = _
  rw [List.append_assoc, check_append taint rowTaint, first]
  change taint.checkBlock rowTaint (_ ++ _) = _
  rw [check_append taint rowTaint]
  change (taint.checkBlock rowTaint ((List.range k).flatMap fun j => mulStep acc b (j + 1))).bind _ = _
  rw [shift]
  change taint.checkBlock rowTaint (carryUp acc (k + 1)) = _
  rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases rowTaint = true from rfl)]
  change taint.checkBlock rowTaint (KList.map Instr.erase (carryUp 0 0)) = _
  rfl

/-- A row ends with a public loop comparison. The loaded modulus,
inverse, multiplicands, accumulator, and carry are all treated as secret. -/
theorem row_taint (N acc a b mo inv : Nat) (hN : 0 < N) :
    taint.checkBlock rowTaint (VG.Impl.Mont.X86.Dynamic.row N acc a b mo inv) = some rowEndTaint := by
  unfold VG.Impl.Mont.X86.Dynamic.row
  simp only [List.append_assoc]
  rw [check_append taint rowTaint]
  have load : taint.checkBlock rowTaint [.mov .ecx (.mem (at_ .ebp a))] = some rowTaint := by
    rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases rowTaint = true from rfl)]
    change taint.checkBlock rowTaint [.mov .ecx (.mem (at_ .ebp 0))] = _
    rfl
  rw [load]
  dsimp only [Option.bind]
  rw [check_append taint rowTaint, mulRow_taint acc b hN]
  dsimp only [Option.bind]
  rw [check_append taint rowTaint, redDigit_taint]
  dsimp only [Option.bind]
  rw [check_append taint rowTaint, mulRow_taint acc mo hN]
  dsimp only [Option.bind]
  rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases rowTaint = true from rfl)]
  change taint.checkBlock rowTaint
    [.alu .add .ebp (.imm 0), .mov .edx (.reg .edi),
     .alu .add .edx (.imm 0), .alu .cmp .ebp (.reg .edx)] = _
  rfl

/-- Constant-time execution of the multiplication loop for every positive
public width and every workspace layout. -/
theorem loop_constantTime (N acc a b mo inv : Nat) (hN : 0 < N) :
    ConstantTime isa (fun _ => True) (VG.X86.Taint.Agree rowTaint)
      (.loop (.block (VG.Impl.Mont.X86.Dynamic.row N acc a b mo inv)) .ne) := by
  refine VG.Taint.constantTime (A := taint) rowTaint (fun _ _ _ _ h => h)
    (hc := .loop rowTaint (.block [])) ?_
  change ((if taint.le rowTaint rowTaint then
    (taint.checkBlock rowTaint (VG.Impl.Mont.X86.Dynamic.row N acc a b mo inv)).bind
      (fun t => if taint.le rowTaint t && taint.condPub t .ne then some t else none)
    else none).isSome) = true
  rw [row_taint N acc a b mo inv hN]
  rfl

/-- Final conditional subtraction and selection do not branch on the borrow. -/
theorem csub_taint (M : VG.Impl.Mont.Mod) (src out : Nat) :
    taint.checkBlock rowTaint (csub M src out) = some rowTaint := by
  have df : taint.checkBlock rowTaint (diffs M src) = some rowTaint := by
    unfold diffs
    apply check_flatMap taint rowTaint
    intro j
    split <;>
      rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases rowTaint = true from rfl)] <;>
      change taint.checkBlock rowTaint _ = some rowTaint
    · change taint.checkBlock rowTaint
        [.mov .eax (.mem (sc 0)), .alu .sub .eax (.mem (sc 0)), .store (sc 0) .eax] = _
      rfl
    · change taint.checkBlock rowTaint
        [.mov .eax (.mem (sc 0)), .alu .sbb .eax (.mem (sc 0)), .store (sc 0) .eax] = _
      rfl
  have sl : taint.checkBlock rowTaint (selects M src out) = some rowTaint := by
    unfold selects
    apply check_flatMap taint rowTaint
    intro j
    rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases rowTaint = true from rfl)]
    change taint.checkBlock rowTaint
      [.mov .ebx (.mem (sc 0)), .mov .edx (.mem (sc 0)), .alu .xor .edx (.reg .ebx),
       .alu .and .edx (.reg .eax), .alu .xor .ebx (.reg .edx), .store (sc 0) .ebx] = _
    rfl
  unfold csub
  rw [List.append_assoc, check_append taint rowTaint, df]
  dsimp only [Option.bind]
  rw [check_append taint rowTaint]
  have mask : taint.checkBlock rowTaint
      [.mov .eax (.mem (sc (src + 4 * words M))), .alu .sbb .eax (.imm 0),
       .alu .sbb .eax (.reg .eax), .alu .xor .eax (.imm (-1))] = some rowTaint := by
    rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases rowTaint = true from rfl)]
    change taint.checkBlock rowTaint
      [.mov .eax (.mem (sc 0)), .alu .sbb .eax (.imm 0),
       .alu .sbb .eax (.reg .eax), .alu .xor .eax (.imm 0)] = _
    rfl
  rw [mask]
  exact sl

/-- Only the workspace pointer is public on entry. -/
def workspaceTaint : VG.X86.Taint.T := { regs := .ofList [.edi], flags := false }

def zeroTaint : VG.X86.Taint.T := { regs := .ofList [.edi, .eax], flags := false }

def initializedTaint : VG.X86.Taint.T := { regs := .ofList [.edi, .eax, .ebp], flags := false }

/-- Zeroing the accumulator publishes its zero register, but no input word. -/
theorem zeros_taint (acc k : Nat) :
    taint.checkBlock workspaceTaint (zeros acc k) = some zeroTaint := by
  have stores : taint.checkBlock zeroTaint
      ((List.range k).map fun j => .store (sc (acc + 4 * j)) .eax) = some zeroTaint := by
    rw [List.map_eq_flatMap]
    apply check_flatMap taint zeroTaint
    intro j
    rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases zeroTaint = true from rfl)]
    change taint.checkBlock zeroTaint [.store (sc 0) .eax] = _
    rfl
  unfold zeros
  change (taint.step workspaceTaint (.mov .eax (.imm 0))).bind _ = _
  have h : taint.step workspaceTaint (.mov .eax (.imm 0)) = some zeroTaint := by rfl
  rw [h]
  exact stores

/-- The multiplication prefix sets both pointers independently of all operands. -/
theorem initialize_taint (acc k : Nat) :
    taint.checkBlock workspaceTaint (zeros acc k ++ ([.mov .ebp (.reg .edi)] : List Instr)) =
      some initializedTaint := by
  rw [check_append taint workspaceTaint, zeros_taint]
  rfl

/-- The full multiplication has secret-independent branches and addresses,
including its initialization and final conditional subtraction. -/
theorem mul_constantTime (M : VG.Impl.Mont.Mod) (inv acc out a b : Nat) (hN : 0 < words M) :
    ConstantTime isa (fun _ => True) (VG.X86.Taint.Agree workspaceTaint)
      (VG.Impl.Mont.X86.Dynamic.mul M inv acc out a b) := by
  refine VG.Taint.constantTime (A := taint) workspaceTaint (fun _ _ _ _ h => h)
    (hc := .seq rowTaint (.block [])
      (.seq rowTaint (.loop rowTaint (.block [])) (.block []))) ?_
  unfold VG.Impl.Mont.X86.Dynamic.mul
  simp only [VG.Taint.check, VG.Taint.checkChunks]
  rw [initialize_taint]
  dsimp only [Option.bind]
  have le₀ : taint.le rowTaint initializedTaint = true := by rfl
  have le₁ : taint.le rowTaint rowTaint = true := by rfl
  rw [le₀, le₁]
  simp only [ite_true]
  rw [row_taint (words M) acc a b M.mo inv hN]
  dsimp only [Option.bind]
  have le₂ : taint.le rowTaint rowEndTaint = true := by rfl
  have cond : taint.condPub rowEndTaint .ne = true := by rfl
  rw [le₂, cond]
  simp only [Bool.true_and, ite_true]
  rw [le₂]
  simp only [ite_true]
  rw [csub_taint]
  rfl

/-- Newton iteration preserves the only public register, the workspace pointer. -/
theorem newton_taint :
    taint.checkBlock workspaceTaint VG.Impl.Mont.X86.Dynamic.newton = some workspaceTaint := by
  rfl

private theorem check_append_of {M : ISA} (A : VG.Taint M) (τ : A.T)
    {a b : List M.Instr} (ha : A.checkBlock τ a = some τ) (hb : A.checkBlock τ b = some τ) :
    A.checkBlock τ (a ++ b) = some τ := by
  rw [check_append A τ, ha, Option.bind_some]
  exact hb

theorem inverse_taint :
    taint.checkBlock workspaceTaint VG.Impl.Mont.X86.Dynamic.inverse = some workspaceTaint := by
  have cp : taint.checkBlock workspaceTaint [.mov .ecx (.reg .ebx)] = some workspaceTaint := by rfl
  have neg : taint.checkBlock workspaceTaint [.mov .eax (.imm 0), .alu .sub .eax (.reg .ecx)] =
      some workspaceTaint := by rfl
  exact check_append_of taint workspaceTaint
    (check_append_of taint workspaceTaint
      (check_append_of taint workspaceTaint
        (check_append_of taint workspaceTaint
          (check_append_of taint workspaceTaint cp newton_taint) newton_taint) newton_taint) newton_taint) neg

/-- Inverse initialization never publishes the loaded modulus word. -/
theorem setupInverse_taint (mo inv : Nat) :
    taint.checkBlock workspaceTaint (VG.Impl.Mont.X86.Dynamic.setupInverse mo inv) =
      some workspaceTaint := by
  have ld : taint.checkBlock workspaceTaint [.mov .ebx (.mem (sc mo))] = some workspaceTaint := by
    rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases workspaceTaint = true from rfl)]
    change taint.checkBlock workspaceTaint [.mov .ebx (.mem (sc 0))] = _
    rfl
  have st : taint.checkBlock workspaceTaint [.store (sc inv) .eax] = some workspaceTaint := by
    rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases workspaceTaint = true from rfl)]
    change taint.checkBlock workspaceTaint [.store (sc 0) .eax] = _
    rfl
  exact check_append_of taint workspaceTaint
    (check_append_of taint workspaceTaint ld inverse_taint) st

/-- Constant-time runtime inverse setup for arbitrary public workspace offsets. -/
theorem setupInverse_constantTime (mo inv : Nat) :
    ConstantTime isa (fun _ => True) (VG.X86.Taint.Agree workspaceTaint)
      (.block (VG.Impl.Mont.X86.Dynamic.setupInverse mo inv)) := by
  refine VG.Taint.constantTime (A := taint) workspaceTaint (fun _ _ _ _ h => h)
    (hc := .block []) ?_
  change (taint.checkBlock workspaceTaint (VG.Impl.Mont.X86.Dynamic.setupInverse mo inv)).isSome = true
  rw [setupInverse_taint]
  rfl

end VG.Proof.Mont.X86.Dynamic
