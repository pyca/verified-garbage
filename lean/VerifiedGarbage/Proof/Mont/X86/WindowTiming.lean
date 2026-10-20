module

public import VerifiedGarbage.Impl.Mont.X86.Window
public import VerifiedGarbage.Proof.Mont.X86.ExponentTiming

/-! # Secret-independent branches and addresses for windowed exponentiation

The window's bits are read only as data: into the masks of the table's scan,
whose every entry is read whatever the window.
-/

@[expose] public section
namespace VG.Proof.Mont.X86.Dynamic
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic

def shiftHint (counter : Bool) : VG.Taint.Hint VG.X86.Taint.T :=
  VG.Taint.hintOf taint (workspaceTaint counter) (Code.erase (shiftUp 1 0))

theorem shiftUp_check (counter : Bool) (k o : Nat) :
    VG.Taint.check taint (workspaceTaint counter) (shiftUp k o) (shiftHint counter) =
      some (rowTaint counter) :=
  (check_of_erase_eq (shiftUp k o) (shiftUp 1 0) (workspaceTaint counter) (shiftHint counter)
    rfl (by cases counter <;> rfl) (by cases counter <;> rfl)).trans (by cases counter <;> rfl)

theorem topWindow_taint (exp k : Nat) :
    taint.checkBlock (workspaceTaint true) (topWindow exp k) = some (workspaceTaint true) := by
  rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (workspaceTaint true) = true from rfl)]
  change taint.checkBlock (workspaceTaint true)
    [.mov .eax (.mem (sc 0)), .shift .shr .eax 28, .store (sc 0) .eax] = _
  rfl

def selectEntryHint : VG.Taint.Hint VG.X86.Taint.T :=
  VG.Taint.hintOf taint (workspaceTaint true) (Code.erase (selectEntry 1 0 0 0))

theorem selectEntry_check (n tab dst j : Nat) :
    VG.Taint.check taint (workspaceTaint true) (selectEntry n tab dst j) selectEntryHint =
      some (rowTaint true) :=
  (check_of_erase_eq (selectEntry n tab dst j) (selectEntry 1 0 0 0) (workspaceTaint true) selectEntryHint
    rfl rfl rfl).trans rfl

def selectEntriesHint : Nat → VG.Taint.Hint VG.X86.Taint.T
  | 0 => .block []
  | k + 1 => .seq (workspaceTaint true) (selectEntriesHint k) selectEntryHint

theorem selectEntries_check (n tab dst : Nat) : ∀ k,
    VG.Taint.check taint (workspaceTaint true) (selectEntries n tab dst k) (selectEntriesHint k) =
      some (if k = 0 then workspaceTaint true else rowTaint true)
  | 0 => rfl
  | k + 1 => by
    rw [selectEntries, selectEntriesHint]
    refine exponent_check_seq taint (selectEntries_check n tab dst k) ?_ (selectEntry_check n tab dst _)
    cases k with
    | zero => rfl
    | succ k => simp only [Nat.add_one_ne_zero, ↓reduceIte]; rfl

/-- After a copy: a loop's taint, and the zero mask in `ecx`. -/
def copyTaint (counter : Bool) : VG.X86.Taint.T :=
  { regs := .ofList ([.edi, .ebp, .edx, .ecx] ++ if counter then [.esi] else []), flags := true }

def copyHint (counter : Bool) : VG.Taint.Hint VG.X86.Taint.T :=
  VG.Taint.hintOf taint (workspaceTaint counter) (Code.erase (copyWords 1 0 0))

theorem copyWords_check (counter : Bool) (n src dst : Nat) :
    VG.Taint.check taint (workspaceTaint counter) (copyWords n src dst) (copyHint counter) =
      some (copyTaint counter) := by
  exact (check_of_erase_eq (copyWords n src dst) (copyWords 1 0 0) (workspaceTaint counter) (copyHint counter)
    rfl (by cases counter <;> rfl) (by cases counter <;> rfl)).trans (by cases counter <;> rfl)

def selectWindowHint : VG.Taint.Hint VG.X86.Taint.T :=
  .seq (workspaceTaint true) (copyHint true) (selectEntriesHint 15)

theorem selectWindow_check (n tab dst : Nat) :
    VG.Taint.check taint (workspaceTaint true) (selectWindow n tab dst) selectWindowHint =
      some (rowTaint true) :=
  exponent_check_seq taint (copyWords_check true _ _ _) (by rfl) (selectEntries_check n tab dst 15)

def squaresHint : VG.Taint.Hint VG.X86.Taint.T :=
  .seq (workspaceTaint true) (mulHint true)
    (.seq (workspaceTaint true) (mulHint true) (.seq (workspaceTaint true) (mulHint true) (mulHint true)))

theorem squares_check (n : Nat) :
    VG.Taint.check taint (workspaceTaint true) (squares n) squaresHint = some (rowTaint true) := by
  unfold squares square squaresHint
  exact exponent_check_seq taint (mul_check true _ _ _ _ _ _) (by rfl)
    (exponent_check_seq taint (mul_check true _ _ _ _ _ _) (by rfl)
      (exponent_check_seq taint (mul_check true _ _ _ _ _ _) (by rfl) (mul_check true _ _ _ _ _ _)))

def windowBodyHint : VG.Taint.Hint VG.X86.Taint.T :=
  .seq (workspaceTaint true) squaresHint
    (.seq (workspaceTaint true) (.seq (workspaceTaint true) (.block []) (shiftHint true))
      (.seq (workspaceTaint true) selectWindowHint (mulHint true)))

theorem windowBody_check (n expWords tab : Nat) :
    VG.Taint.check taint (workspaceTaint true) (windowBody n expWords tab) windowBodyHint =
      some (rowTaint true) := by
  unfold windowBody windowBodyHint nextWindow
  refine exponent_check_seq taint (squares_check n) (by rfl) ?_
  refine exponent_check_seq taint
    (exponent_check_seq taint (u := workspaceTaint true) (topWindow_taint _ _) (by rfl)
      (shiftUp_check true _ _)) (by rfl)
    (exponent_check_seq taint (selectWindow_check n tab _) (by rfl) (mul_check true _ _ _ _ _ _))

def windowStepHint : VG.Taint.Hint VG.X86.Taint.T :=
  .seq (workspaceTaint true) windowBodyHint (.block [])

theorem windowStep_check (n expWords tab : Nat) :
    VG.Taint.check taint (workspaceTaint true) (windowStep n expWords tab) windowStepHint =
      some counterEndTaint := by
  unfold windowStep windowStepHint
  exact exponent_check_seq taint (windowBody_check n expWords tab) (by rfl) (by rfl)

def copyOutHint : VG.Taint.Hint VG.X86.Taint.T :=
  VG.Taint.hintOf taint (workspaceTaint true) (Code.erase (copyOut 1 0))

theorem copyOut_check (k src : Nat) :
    VG.Taint.check taint (workspaceTaint true) (copyOut k src) copyOutHint = some (rowTaint true) :=
  (check_of_erase_eq (copyOut k src) (copyOut 1 0) (workspaceTaint true) copyOutHint
    rfl rfl rfl).trans rfl

def tableStepHint : VG.Taint.Hint VG.X86.Taint.T :=
  .seq (workspaceTaint true) (mulHint true) (.seq (rowTaint true) copyOutHint (.block []))

theorem tableStep_check (n tab : Nat) :
    VG.Taint.check taint (workspaceTaint true) (tableStep n tab) tableStepHint = some (rowTaint true) := by
  unfold tableStep tableStepHint
  refine exponent_check_seq taint (mul_check true _ _ _ _ _ _) (by rfl)
    (exponent_check_seq taint (copyOut_check _ _) (by rfl) ?_)
  rw [← VG.X86.Taint.check_erase _ _ _ (show VG.X86.Taint.noBases (rowTaint true) = true from rfl) rfl]
  change taint.check (rowTaint true) (.block [.mov .edx (.reg .edi), .alu .add .edx (.imm 0),
    .alu .cmp .esi (.reg .edx)]) (.block []) = _
  rfl

def tablePowersHint : VG.Taint.Hint VG.X86.Taint.T :=
  .seq (workspaceTaint true) (.block []) (.loop (workspaceTaint true) tableStepHint)

theorem tablePowers_check (n tab : Nat) :
    VG.Taint.check taint (workspaceTaint false) (tablePowers n tab) tablePowersHint =
      some (rowTaint true) := by
  have loop : VG.Taint.check taint (workspaceTaint true) (.loop (tableStep n tab) .ne)
      (.loop (workspaceTaint true) tableStepHint) = some (rowTaint true) := by
    change (if taint.le (workspaceTaint true) (workspaceTaint true) then
      (VG.Taint.check taint (workspaceTaint true) (tableStep n tab) tableStepHint).bind
        (fun t => if taint.le (workspaceTaint true) t && taint.condPub t .ne then some t else none)
      else none) = _
    rw [tableStep_check n tab]
    rfl
  unfold tablePowers tablePowersHint
  refine exponent_check_seq taint (u := { regs := .ofList [.edi, .esi], flags := true }) ?_ (by rfl) loop
  rw [← VG.X86.Taint.check_erase _ _ _ (show VG.X86.Taint.noBases (workspaceTaint false) = true from rfl) rfl]
  change taint.check (workspaceTaint false) (.block [.mov .esi (.reg .edi), .alu .add .esi (.imm 0)])
    (.block []) = _
  rfl

def buildTableHint : VG.Taint.Hint VG.X86.Taint.T :=
  .seq (workspaceTaint false) (copyHint false) <|
  .seq (workspaceTaint false) (copyHint false) <|
  .seq (workspaceTaint false) (copyHint false) tablePowersHint

theorem buildTable_check (n tab : Nat) :
    VG.Taint.check taint (workspaceTaint false) (buildTable n tab) buildTableHint =
      some (rowTaint true) := by
  unfold buildTable buildTableHint
  exact exponent_check_seq taint (copyWords_check false _ _ _) (by rfl)
    (exponent_check_seq taint (copyWords_check false _ _ _) (by rfl)
      (exponent_check_seq taint (copyWords_check false _ _ _) (by rfl) (tablePowers_check n tab)))

def windowExponentiateHint : VG.Taint.Hint VG.X86.Taint.T :=
  .seq (workspaceTaint false) (mulHint false)
    (.seq (workspaceTaint false) (mulHint false)
      (.seq (workspaceTaint false) buildTableHint
        (.seq (workspaceTaint true) (.block [])
          (.seq (workspaceTaint false) (.loop (workspaceTaint true) windowStepHint) (mulHint false)))))

theorem windowExponentiate_check (n expWords tab : Nat) :
    VG.Taint.check taint (workspaceTaint false) (windowExponentiate n expWords tab) windowExponentiateHint =
      some (rowTaint false) := by
  have loop : VG.Taint.check taint (workspaceTaint true) (.loop (windowStep n expWords tab) .ne)
      (.loop (workspaceTaint true) windowStepHint) = some counterEndTaint := by
    change (if taint.le (workspaceTaint true) (workspaceTaint true) then
      (VG.Taint.check taint (workspaceTaint true) (windowStep n expWords tab) windowStepHint).bind
        (fun t => if taint.le (workspaceTaint true) t && taint.condPub t .ne then some t else none)
      else none) = _
    rw [windowStep_check n expWords tab]
    rfl
  unfold windowExponentiate windowExponentiateHint
  refine exponent_check_seq taint (mul_check false _ _ _ _ _ _) (by rfl) ?_
  refine exponent_check_seq taint (mul_check false _ _ _ _ _ _) (by rfl) ?_
  refine exponent_check_seq taint (buildTable_check n tab) (by rfl) ?_
  refine exponent_check_seq taint (u := workspaceTaint true) (by rfl) (by rfl) ?_
  exact exponent_check_seq taint loop (by rfl) (mul_check false _ _ _ _ _ _)

end VG.Proof.Mont.X86.Dynamic
