module

public import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi

/-!
# The ABI checks of the curve functions on AArch64, matching on each instruction once

`abiPreserved_of` asks three checks of a function's code, each a walk of it
by the kernel: `CallsKeep`, `KeepsUntouched` and `Code.allInstrs keepsV`.
The first two ask of an instruction whether it writes a register of
`untouched` through `dsts`, two matches on the instruction (`dsts`,
`dstOf`), `keepsV` is a third, and `restores` and `restoresMid` match on the
instruction at every cell of a called function's code. A match on an `Instr`
costs the kernel a tenth of a millisecond or more, wherever it cannot find
its result again.

`AbiOk` is the three in one statement, which `abiPreserved_ofK` takes: one
walk of the code outside the functions it calls, with one match for each
instruction (`topTestK`: `keepsUntouchedK` and `keepsV`, their cases closed,
`inline_match%`), and for each function it calls the same walk, which is
all that is asked of a function that writes no register of `untouched`, or
else `keepsV` and `restoresK`, which is `restores` reading each instruction
once (`laneViewK`). `AbiOk.callsKeep`, `AbiOk.untouched` and `AbiOk.keepsV`
give the three statements; `callsKeep_ofK` and `keepsUntouched_ofK` give one
of them alone, for a part of a function's code.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.AArch64

open VG VG.AArch64

/-- Whether an instruction writes no register of `untouched`. -/
def keepsUntouched (i : Instr) : Bool := (dsts i).all fun r => !untouched.contains r

/-- `keepsUntouched`, with its cases closed (`inline_match%`). -/
def keepsUntouchedK : Instr → Bool := inline_match% keepsUntouched dsts dstOf Option.toList

theorem keepsUntouchedK_eq : keepsUntouchedK = fun i => (dsts i).all fun r => !untouched.contains r := by
  funext i; cases i <;> rfl

/-- `KeepsUntouched`, with `keepsUntouchedK`. -/
theorem keepsUntouched_ofK {c : Prog isa} (h : topAll keepsUntouchedK c = true) : KeepsUntouched c := by
  rw [keepsUntouchedK_eq] at h; exact h

/-! ## `restores`, reading each instruction once

`restores` and `restoresMid` match on the instruction at every cell of a
called function's code, for each register of `untouched`: the kernel cannot
find the match again, since its alternatives hold the rest of the list.
`restoresK` and `restoresMidK` ask what the two match for through
`laneViewK`, one match for each instruction, which the kernel finds again at
every later cell that holds the instruction. -/

/-- What `restores` and `keepsLane` ask of an instruction: whether it is
`umov r, v.d[l]` (64 bits), `ins v.d[l], r`, and the vector register it
writes. -/
structure LaneView where
  umov : Option (Reg × VReg × Nat)
  ins : Option (VReg × Nat × Reg)
  vd : Option VReg

/-- An instruction's `LaneView`. -/
def laneViewFn : Instr → LaneView
  | .umov .x r v l => ⟨some (r, v, l), none, none⟩
  | .vop (.ins .d2 v l r) => ⟨none, some (v, l, r), some v⟩
  | i => ⟨none, none, vdstOf i⟩

/-- `laneViewFn`, with its cases closed (`inline_match%`). -/
def laneViewK : Instr → LaneView := inline_match% laneViewFn vdstOf VOp.dst

theorem laneViewK_eq (i : Instr) : laneViewK i = laneViewFn i := by
  cases i with
  | vop op => cases op with
    | ins a d k n => cases a <;> rfl
    | _ => rfl
  | umov sz d n k => cases sz <;> rfl
  | _ => rfl

/-- `keepsLane`, from the instruction's `LaneView`. -/
def keepsLaneV (v : VReg) (l : Nat) (w : LaneView) : Bool :=
  match w.ins with
  | some (d, l', _) => d != v || l' != l
  | none => w.vd.all (· != v)

theorem keepsLaneV_eq (v : VReg) (l : Nat) (i : Instr) : keepsLaneV v l (laneViewK i) = keepsLane v l i := by
  rw [laneViewK_eq]
  cases i with
  | vop op => cases op with
    | ins a d k n => cases a <;> rfl
    | _ => rfl
  | umov sz d n k => cases sz <;> rfl
  | _ => rfl

/-- `restoresMid`, with `laneViewK`. -/
def restoresMidK (r : Reg) (v : VReg) (l : Nat) : List Instr → Bool
  | [] => false
  | i :: is =>
    match (laneViewK i).umov with
    | some (r', v', l') =>
      if r' = r ∧ v' = v ∧ l' = l then is.all (keepsReg r)
      else keepsLaneV v l (laneViewK i) && restoresMidK r v l is
    | none => keepsLaneV v l (laneViewK i) && restoresMidK r v l is

theorem restoresMidK_eq (r : Reg) (v : VReg) (l : Nat) : ∀ is, restoresMidK r v l is = restoresMid r v l is
  | [] => rfl
  | i :: is => by
    have ih := restoresMidK_eq r v l is
    have hk := keepsLaneV_eq v l i
    rw [restoresMidK, hk, ih]
    rw [laneViewK_eq]
    cases i with
    | vop op => cases op with
      | ins a d k n => cases a <;> rfl
      | _ => rfl
    | umov sz d n k => cases sz <;> rfl
    | _ => rfl

/-- `restores`, with `laneViewK`. -/
def restoresK (r : Reg) : List Instr → Bool
  | [] => true
  | i :: is =>
    match (laneViewK i).ins with
    | some (v, l, r') => if r' = r ∧ l < 2 then restoresMidK r v l is else restoresK r is
    | none => keepsReg r i && restoresK r is

theorem restoresK_eq (r : Reg) : ∀ is, restoresK r is = restores r is
  | [] => rfl
  | i :: is => by
    have ih := restoresK_eq r is
    rw [restoresK, laneViewK_eq]
    simp only [restoresMidK_eq, ih]
    cases i with
    | vop op => cases op with
      | ins a d k n => cases a <;> rfl
      | _ => rfl
    | umov sz d n k => cases sz <;> rfl
    | _ => rfl

/-- `CallsKeep`, with `keepsUntouchedK` and `restoresK`. -/
abbrev CallsKeepK (c : Prog isa) : Prop :=
  (c.calls.all fun nb => nb.2.allInstrs keepsUntouchedK ||
    (((straight nb.2).any fun is => untouched.all fun r => restoresK r is) ||
      untouched.all fun r => nb.2.allInstrs (keepsReg r))) = true

theorem callsKeep_ofK {c : Prog isa} (h : CallsKeepK c) : CallsKeep c := by
  rw [CallsKeepK, keepsUntouchedK_eq, show restoresK = restores from funext fun r => funext (restoresK_eq r)] at h
  exact h

/-- `keepsUntouched` and `keepsV`. -/
def topTest (i : Instr) : Bool := keepsUntouched i && keepsV i

/-- `topTest`, as one match on the instruction with its cases closed (`inline_match%`). -/
def topTestK : Instr → Bool := inline_match% topTest keepsUntouched dsts dstOf Option.toList keepsV vdstOf

theorem topTestK_eq (i : Instr) : topTestK i = (keepsUntouchedK i && keepsV i) := by
  rw [keepsUntouchedK_eq]; cases i <;> rfl

theorem topAll_mono {p q : Instr → Bool} (hpq : ∀ i, p i = true → q i = true) (c : Prog isa) :
    topAll p c = true → topAll q c = true := by
  induction c with
  | icall i _ _ n _ ihn =>
    simp only [topAll, Bool.and_eq_true]; exact fun h => ⟨hpq i h.1, ihn h.2⟩
  | block is =>
    rw [topAll_block, topAll_block, List.all_eq_true, List.all_eq_true]
    exact fun h i hi => hpq i (h i hi)
  | seq a b iha ihb | ite _ a b iha ihb =>
    simp only [topAll, Bool.and_eq_true]; exact fun h => ⟨iha h.1, ihb h.2⟩
  | loop b _ ih => exact ih
  | call _ _ _ => intro _; rfl
  | frame i b j ih =>
    simp only [topAll, Bool.and_eq_true]; exact fun h => ⟨⟨hpq i h.1.1, ih h.1.2⟩, hpq j h.2⟩

/-- What holds of every instruction of code outside the functions it calls,
and of theirs, holds of every instruction. -/
theorem allInstrs_of_top (p : Instr → Bool) (c : Prog isa) (h : topAll p c = true)
    (hc : (c.calls.all fun nb => topAll p nb.2) = true) : c.allInstrs p = true := by
  induction c with
  | block is => exact h
  | seq a b iha ihb | ite _ a b iha ihb =>
    simp only [topAll, Bool.and_eq_true] at h
    simp only [Code.calls, List.all_append, Bool.and_eq_true] at hc
    simp only [Code.allInstrs, Bool.and_eq_true]
    exact ⟨iha h.1 hc.1, ihb h.2 hc.2⟩
  | loop b _ ih => exact ih h hc
  | call _ b ih =>
    simp only [Code.calls, List.all_cons, Bool.and_eq_true] at hc
    exact ih hc.1 hc.2
  | frame i b j ih =>
    simp only [topAll, Bool.and_eq_true] at h
    simp only [Code.calls] at hc
    simp only [Code.allInstrs, Bool.and_eq_true]
    exact ⟨⟨h.1.1, ih h.1.2 hc⟩, h.2⟩
  | icall i _ b n ihb ihn =>
    simp only [topAll, Bool.and_eq_true] at h
    simp only [Code.calls, List.all_cons, List.all_append, Bool.and_eq_true] at hc
    simp only [Code.allInstrs, Bool.and_eq_true]
    exact ⟨⟨h.1, ihb hc.1.1 hc.1.2⟩, ihn h.2 hc.2⟩

theorem topAll_of_allInstrs (p : Instr → Bool) (c : Prog isa) (h : c.allInstrs p = true) : topAll p c = true := by
  induction c with
  | block is => exact h
  | seq a b iha ihb | ite _ a b iha ihb =>
    simp only [Code.allInstrs, Bool.and_eq_true] at h
    simp only [topAll, Bool.and_eq_true]
    exact ⟨iha h.1, ihb h.2⟩
  | loop b _ ih => exact ih h
  | call _ b ih => rfl
  | frame i b j ih =>
    simp only [Code.allInstrs, Bool.and_eq_true] at h
    simp only [topAll, Bool.and_eq_true]
    exact ⟨⟨h.1.1, ih h.1.2⟩, h.2⟩
  | icall i _ b n ihb ihn =>
    simp only [Code.allInstrs, Bool.and_eq_true] at h
    simp only [topAll, Bool.and_eq_true]
    exact ⟨h.1.1, ihn h.2⟩

theorem allInstrs_mono {p q : Instr → Bool} (hpq : ∀ i, p i = true → q i = true) (c : Prog isa)
    (h : c.allInstrs p = true) : c.allInstrs q = true := by
  rw [Code.allInstrs_eq, List.all_eq_true] at h ⊢
  exact fun i hi => hpq i (h i hi)

/-- All of what `abiPreserved_of` asks of code, in one statement. Outside the
functions `c` calls, no instruction writes a register of `untouched` or a
callee-saved SIMD register (one walk, one match for each instruction). Each
function it calls either is such code itself, the functions it calls
included (one walk again: the usual case, which is then all that is asked of
that function), or writes no callee-saved SIMD register and restores the
registers of `untouched` (`restoresK`) or keeps each of them. -/
abbrev AbiOk (c : Prog isa) : Prop :=
  (topAll topTestK c && c.calls.all fun nb => nb.2.allInstrs topTestK ||
    (topAll keepsV nb.2 && (((straight nb.2).any fun is => untouched.all fun r => restoresK r is) ||
      untouched.all fun r => nb.2.allInstrs (keepsReg r)))) = true

theorem topTestK_untouched {i : Instr} (h : topTestK i = true) : keepsUntouchedK i = true := by
  rw [topTestK_eq, Bool.and_eq_true] at h; exact h.1

theorem topTestK_keepsV {i : Instr} (h : topTestK i = true) : keepsV i = true := by
  rw [topTestK_eq, Bool.and_eq_true] at h; exact h.2

theorem AbiOk.untouched {c : Prog isa} (h : AbiOk c) : KeepsUntouched c :=
  keepsUntouched_ofK (topAll_mono (fun _ => topTestK_untouched) c (Bool.and_eq_true_iff.mp h).1)

theorem AbiOk.keepsV {c : Prog isa} (h : AbiOk c) : c.allInstrs keepsV = true :=
  allInstrs_of_top _ c (topAll_mono (fun _ => topTestK_keepsV) c (Bool.and_eq_true_iff.mp h).1)
    (List.all_eq_true.mpr fun nb hnb => by
      rcases Bool.or_eq_true_iff.mp (List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).2 nb hnb) with h' | h'
      · exact topAll_of_allInstrs _ _ (allInstrs_mono (fun _ => topTestK_keepsV) _ h')
      · exact (Bool.and_eq_true_iff.mp h').1)

theorem AbiOk.callsKeep {c : Prog isa} (h : AbiOk c) : CallsKeep c :=
  callsKeep_ofK (List.all_eq_true.mpr fun nb hnb => by
    rcases Bool.or_eq_true_iff.mp (List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).2 nb hnb) with h' | h'
    · exact Bool.or_eq_true_iff.mpr (.inl (allInstrs_mono (fun _ => topTestK_untouched) _ h'))
    · exact Bool.or_eq_true_iff.mpr (.inr (Bool.and_eq_true_iff.mp h').2))

/-- `abiPreserved_of`, from the one check. -/
theorem abiPreserved_ofK {c : Prog isa} {s s' : State} {t : List Leak} (he : Exec isa c s t s') (h : AbiOk c)
    (hsv : ∀ r ∈ [Reg.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x30], s'.gpr r = s.gpr r) :
    abiPreserved s s' :=
  abiPreserved_of he h.callsKeep h.untouched h.keepsV hsv

end VG.Proof.Ecdsa.AArch64
