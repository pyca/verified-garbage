module

public import VerifiedGarbage.Proof.Mont.X86.ExponentTiming

/-! # Constant-time modular doubling and Montgomery setup -/

@[expose] public section
namespace VG.Proof.Mont.X86.Dynamic
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic

theorem exponent_check_flatMap {M : ISA} (A : VG.Taint M) (τ : A.T) {α : Type}
    (xs : List α) (f : α → List M.Instr) (h : ∀ x, A.checkBlock τ (f x) = some τ) :
    A.checkBlock τ (xs.flatMap f) = some τ := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.flatMap_cons, exponent_check_append A τ, h, Option.bind_some, ih]

theorem csub_counter_taint (M : VG.Impl.Mont.Mod) (src out : Nat) :
    taint.checkBlock (workspaceTaint true) (csub M src out) = some (workspaceTaint true) := by
  have df : taint.checkBlock (workspaceTaint true) (diffs M src) = some (workspaceTaint true) := by
    unfold diffs
    apply exponent_check_flatMap taint (workspaceTaint true)
    intro j
    split <;>
      rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (workspaceTaint true) = true from rfl)]
    · change taint.checkBlock (workspaceTaint true)
        [.mov .eax (.mem (sc 0)), .alu .sub .eax (.mem (sc 0)), .store (sc 0) .eax] = _
      rfl
    · change taint.checkBlock (workspaceTaint true)
        [.mov .eax (.mem (sc 0)), .alu .sbb .eax (.mem (sc 0)), .store (sc 0) .eax] = _
      rfl
  have sl : taint.checkBlock (workspaceTaint true) (selects M src out) = some (workspaceTaint true) := by
    unfold selects
    apply exponent_check_flatMap taint (workspaceTaint true)
    intro j
    rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (workspaceTaint true) = true from rfl)]
    change taint.checkBlock (workspaceTaint true)
      [.mov .ebx (.mem (sc 0)), .mov .edx (.mem (sc 0)), .alu .xor .edx (.reg .ebx),
       .alu .and .edx (.reg .eax), .alu .xor .ebx (.reg .edx), .store (sc 0) .ebx] = _
    rfl
  have mask : taint.checkBlock (workspaceTaint true)
      [.mov .eax (.mem (sc (src + 4 * words M))), .alu .sbb .eax (.imm 0),
        .alu .sbb .eax (.reg .eax), .alu .xor .eax (.imm (-1))] = some (workspaceTaint true) := by
    rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (workspaceTaint true) = true from rfl)]
    change taint.checkBlock (workspaceTaint true)
      [.mov .eax (.mem (sc 0)), .alu .sbb .eax (.imm 0), .alu .sbb .eax (.reg .eax), .alu .xor .eax (.imm 0)] = _
    rfl
  unfold csub
  rw [List.append_assoc, exponent_check_append taint (workspaceTaint true), df]
  dsimp only [Option.bind]
  rw [exponent_check_append taint (workspaceTaint true), mask]
  exact sl

theorem add_counter_taint (M : VG.Impl.Mont.Mod) (acc out a b : Nat) :
    taint.checkBlock (workspaceTaint true) (add M acc out a b) = some (workspaceTaint true) := by
  have ch : taint.checkBlock (workspaceTaint true) (chain M .add .adc acc a b) = some (workspaceTaint true) := by
    unfold chain
    apply exponent_check_flatMap taint (workspaceTaint true)
    intro j
    split <;>
      rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (workspaceTaint true) = true from rfl)]
    · change taint.checkBlock (workspaceTaint true)
        [.mov .eax (.mem (sc 0)), .alu .add .eax (.mem (sc 0)), .store (sc 0) .eax] = _
      rfl
    · change taint.checkBlock (workspaceTaint true)
        [.mov .eax (.mem (sc 0)), .alu .adc .eax (.mem (sc 0)), .store (sc 0) .eax] = _
      rfl
  have top : taint.checkBlock (workspaceTaint true)
      [.mov .eax (.imm 0), .alu .adc .eax (.imm 0), .store (sc (acc + 4 * words M)) .eax] = some (workspaceTaint true) := by
    rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (workspaceTaint true) = true from rfl)]
    change taint.checkBlock (workspaceTaint true) [.mov .eax (.imm 0), .alu .adc .eax (.imm 0), .store (sc 0) .eax] = _
    rfl
  unfold add
  rw [List.append_assoc, exponent_check_append taint (workspaceTaint true), ch]
  dsimp only [Option.bind]
  rw [exponent_check_append taint (workspaceTaint true), top]
  exact csub_counter_taint M acc out

theorem one_taint (counter : Bool) (n out : Nat) :
    taint.checkBlock (workspaceTaint counter) (one n out) = some (zeroTaint counter) := by
  rw [one, exponent_check_append taint (workspaceTaint counter), zeros_taint]
  change taint.checkBlock (zeroTaint counter) [.mov .eax (.imm 1), .store (sc out) .eax] = _
  rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (zeroTaint counter) = true from rfl)]
  change taint.checkBlock (zeroTaint counter) [.mov .eax (.imm 0), .store (sc 0) .eax] = _
  cases counter <;> rfl

def powerHint : VG.Taint.Hint VG.X86.Taint.T :=
  .seq (workspaceTaint true) (.block []) (.loop (workspaceTaint true) (.block []))

theorem powerTwo_check (M : VG.Impl.Mont.Mod) (acc out bits : Nat) :
    VG.Taint.check taint (workspaceTaint false) (powerTwo M acc out bits) powerHint = some counterEndTaint := by
  have pref : taint.checkBlock (workspaceTaint false)
      (one M.n out ++ ([.mov .esi (.imm (BitVec.ofNat 32 bits))] : List Instr)) = some (zeroTaint true) := by
    rw [exponent_check_append taint (workspaceTaint false), one_taint]
    rfl
  have body : taint.checkBlock (workspaceTaint true) (doubleStep M acc out) = some counterEndTaint := by
    rw [doubleStep, exponent_check_append taint (workspaceTaint true), add_counter_taint]
    rfl
  unfold powerTwo powerHint
  refine exponent_check_seq taint pref (by rfl) ?_
  change (if taint.le (workspaceTaint true) (workspaceTaint true) then
    (taint.checkBlock (workspaceTaint true) (doubleStep M acc out)).bind
      (fun t => if taint.le (workspaceTaint true) t && taint.condPub t .ne then some t else none)
    else none) = _
  rw [body]
  rfl

theorem powerTwo_constantTime (M : VG.Impl.Mont.Mod) (acc out bits : Nat) :
    ConstantTime isa (fun _ => True) (VG.X86.Taint.Agree (workspaceTaint false)) (powerTwo M acc out bits) := by
  refine VG.Taint.constantTime (A := taint) (workspaceTaint false) (fun _ _ _ _ h => h) (hc := powerHint) ?_
  rw [powerTwo_check]
  rfl

theorem contextSetup_constantTime (n : Nat) :
    ConstantTime isa (fun _ => True) (VG.X86.Taint.Agree (workspaceTaint false)) (contextSetup n) := by
  have pref : taint.checkBlock (workspaceTaint false)
      (setupInverse (slot n 0) 0 ++ one n (slot n 3)) = some (zeroTaint false) := by
    rw [exponent_check_append taint (workspaceTaint false), setupInverse_taint false]
    exact one_taint false n (slot n 3)
  refine VG.Taint.constantTime (A := taint) (workspaceTaint false) (fun _ _ _ _ h => h)
    (hc := .seq (workspaceTaint false) (.block []) powerHint) ?_
  have check : VG.Taint.check taint (workspaceTaint false) (contextSetup n)
      (.seq (workspaceTaint false) (.block []) powerHint) = some counterEndTaint :=
    exponent_check_seq taint pref (show taint.le (workspaceTaint false) (zeroTaint false) = true from rfl)
    (powerTwo_check (contextMod n) (slot n 2) (slot n 4) (128 * n))
  change (VG.Taint.check taint (workspaceTaint false) (contextSetup n)
    (.seq (workspaceTaint false) (.block []) powerHint)).isSome = true
  rw [check]
  rfl

end VG.Proof.Mont.X86.Dynamic
