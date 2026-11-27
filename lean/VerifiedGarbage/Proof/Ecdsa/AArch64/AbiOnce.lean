module

public import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
public import VerifiedGarbage.Proof.Framework.CodeWalk
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved

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

`abiK` is the three in one check, which `abiPreserved_ofK` takes: one walk of
the code and of the functions it calls, with one match for each instruction
(`topTestK`: `keepsUntouchedK` and `keepsV`, their cases closed,
`inline_match%`), but for functions that write registers of `untouched` and
restore them, of which it asks `keepsV` and `restoresK`, which is `restores`
reading each instruction once (`laneViewK`). `abiK_callsKeep`,
`abiK_untouched` and `abiK_keepsV` give the three statements;
`callsKeep_ofK` and `keepsUntouched_ofK` give one of them alone, for a part
of a function's code.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.AArch64

open VG VG.AArch64 VG.CodeWalk

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

theorem topTestK_untouched {i : Instr} (h : topTestK i = true) : keepsUntouchedK i = true := by
  rw [topTestK_eq, Bool.and_eq_true] at h; exact h.1

theorem topTestK_keepsV {i : Instr} (h : topTestK i = true) : keepsV i = true := by
  rw [topTestK_eq, Bool.and_eq_true] at h; exact h.2

/-- `CallsKeep`, which also accepts a function none of whose own instructions
(outside the functions it calls, which it checks too) writes `untouched`. -/
abbrev CallsKeepN (c : Prog isa) : Prop :=
  (c.calls.all fun nb => nb.2.allInstrs (fun i => (dsts i).all fun r => !untouched.contains r) ||
    (((straight nb.2).any fun is => untouched.all fun r => restores r is) ||
      (untouched.all fun r => nb.2.allInstrs (keepsReg r)) ||
      topAll (fun i => (dsts i).all fun r => !untouched.contains r) nb.2)) = true

/-- `gpr_top`, for functions that keep the register in their own instructions
too. -/
theorem gpr_topN {r : Reg} (hr : r ∉ linkRegs) {c : Prog isa} {s s' : State} {t : List Leak}
    (h : Exec isa c s t s') (hc : topAll (keepsReg r) c = true)
    (hb : (c.calls.all fun nb => (straight nb.2).any (restores r) || nb.2.allInstrs (keepsReg r) ||
      topAll (keepsReg r) nb.2) = true) :
    s'.gpr r = s.gpr r := by
  induction h with
  | icall _ hc₁ e hr' ih =>
    simp only [Code.calls, List.all_append, List.all_cons, Bool.and_eq_true, Bool.or_eq_true] at hb
    rcases hb.1.1 with (hb' | hb') | hb'
    · obtain ⟨is, his, hres⟩ := (Option.any_eq_true _ _).mp hb'
      obtain ⟨_, eb⟩ := straight_exec his e
      rw [ret_eq hr', restores_ok hres eb, (call_eq hc₁).2.2.2.2 r hr]
    · rw [ret_eq hr', Exec.gpr (fun i hi => by
          have := List.all_eq_true.mp ((Code.allInstrs_eq _ _) ▸ hb') i hi
          simpa [keepsReg] using this) e (.inr hr), (call_eq hc₁).2.2.2.2 r hr]
    · rw [ret_eq hr', ih hb' hb.1.2, (call_eq hc₁).2.2.2.2 r hr]
  | icallNext _ _ _ ih =>
    exact ih (by simp only [topAll, Bool.and_eq_true] at hc ⊢; exact hc.2)
      (by simp only [Code.calls, List.all_append, List.all_cons, Bool.and_eq_true] at hb ⊢; exact hb.2)
  | block h =>
    exact execBlock_keep (fun s : State => s.gpr r) (ok := fun i => keepsReg r i = true)
      (fun hi he => exec_gpr (by simpa [keepsReg] using hi) he)
      (List.all_eq_true.mp (by rwa [topAll_block] at hc)) h
  | seq _ _ ih₁ ih₂ =>
    simp only [topAll, Bool.and_eq_true] at hc
    simp only [Code.calls, List.all_append, Bool.and_eq_true] at hb
    rw [ih₂ hc.2 hb.2, ih₁ hc.1 hb.1]
  | iteT _ _ ih =>
    simp only [topAll, Bool.and_eq_true] at hc
    simp only [Code.calls, List.all_append, Bool.and_eq_true] at hb
    exact ih hc.1 hb.1
  | iteF _ _ ih =>
    simp only [topAll, Bool.and_eq_true] at hc
    simp only [Code.calls, List.all_append, Bool.and_eq_true] at hb
    exact ih hc.2 hb.2
  | loopExit _ _ ih => exact ih hc hb
  | loopNext _ _ _ ih₁ ih₂ => rw [ih₂ hc hb, ih₁ hc hb]
  | call hc₁ e hr' ih =>
    simp only [Code.calls, List.all_cons, Bool.and_eq_true, Bool.or_eq_true] at hb
    rcases hb.1 with (hb' | hb') | hb'
    · obtain ⟨is, his, hres⟩ := (Option.any_eq_true _ _).mp hb'
      obtain ⟨_, eb⟩ := straight_exec his e
      rw [ret_eq hr', restores_ok hres eb, (call_eq hc₁).2.2.2.2 r hr]
    · rw [ret_eq hr', Exec.gpr (fun i hi => by
          have := List.all_eq_true.mp ((Code.allInstrs_eq _ _) ▸ hb') i hi
          simpa [keepsReg] using this) e (.inr hr), (call_eq hc₁).2.2.2.2 r hr]
    · rw [ret_eq hr', ih hb' hb.2, (call_eq hc₁).2.2.2.2 r hr]
  | frame hp _ hq ih =>
    simp only [topAll, Bool.and_eq_true] at hc
    simp only [Code.calls] at hb
    obtain ⟨-, -, -, hg, -⟩ := push_eq hp
    rw [(pop_eq hq).2.2.2.1 r (dstOf_ne_of_clobbers (by simpa [keepsReg] using hc.2)), ih hc.1.2 hb, hg]

theorem untouched_keepN {c : Prog isa} {s s' : State} {t : List Leak} (he : Exec isa c s t s')
    (hn : CallsKeepN c) (hu : KeepsUntouched c) : ∀ r ∈ untouched, s'.gpr r = s.gpr r := by
  intro r h
  refine gpr_topN (by revert h; revert r; decide) he
    (topAll_mono (fun i hi => keepsReg_of_untouched h hi) c hu) ?_
  refine List.all_eq_true.mpr fun nb hnb => ?_
  rcases Bool.or_eq_true_iff.mp (List.all_eq_true.mp hn nb hnb) with h' | h'
  · refine Bool.or_eq_true_iff.mpr (.inl (Bool.or_eq_true_iff.mpr (.inr ?_)))
    rw [Code.allInstrs_eq] at h' ⊢
    exact List.all_eq_true.mpr fun i hi => keepsReg_of_untouched h (List.all_eq_true.mp h' i hi)
  rcases Bool.or_eq_true_iff.mp h' with h' | h'
  · rcases Bool.or_eq_true_iff.mp h' with h' | h'
    · obtain ⟨is, his, hres⟩ := (Option.any_eq_true _ _).mp h'
      exact Bool.or_eq_true_iff.mpr (.inl (Bool.or_eq_true_iff.mpr
        (.inl ((Option.any_eq_true _ _).mpr ⟨is, his, List.all_eq_true.mp hres r h⟩))))
    · exact Bool.or_eq_true_iff.mpr (.inl (Bool.or_eq_true_iff.mpr (.inr (List.all_eq_true.mp h' r h))))
  · exact Bool.or_eq_true_iff.mpr (.inr
      (topAll_mono (fun i hi => keepsReg_of_untouched h hi) nb.2 h'))

/-- `abiPreserved_of`, with `CallsKeepN`. -/
theorem abiPreserved_ofN {c : Prog isa} {s s' : State} {t : List Leak} (he : Exec isa c s t s')
    (hn : CallsKeepN c) (hu : KeepsUntouched c) (hv : c.allInstrs keepsV = true)
    (hsv : ∀ r ∈ [Reg.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x30], s'.gpr r = s.gpr r) :
    abiPreserved s s' := by
  refine ⟨fun r hr => ?_, Exec.sp he, Exec.preservedV he hv⟩
  by_cases h : r ∈ untouched
  · exact untouched_keepN he hn hu r h
  · refine hsv r ?_
    revert h
    revert r
    decide

/-! ## All three, in one walk -/

/-- `a && b`. (What a recursor gives in tail position the kernel evaluates deeper in its
stack, and what a definition unfolds to it does not: long code would be too deep.) -/
noncomputable def andK (a b : Bool) : Bool := Bool.rec false b a

theorem andK_eq (a b : Bool) : andK a b = (a && b) := rec_and a b

/-- `is.all topTestK`, by the recursor. -/
noncomputable def topBlock (is : List Instr) : Bool := List.rec true (fun i _ ih => andK (topTestK i) ih) is

/-- `keepsV` of each instruction of straight-line code, which restores the registers of `untouched`. -/
def restoresAll (b : Prog isa) : Bool :=
  topAll keepsV b && (straight b).any fun is => untouched.all fun r => restoresK r is

/-- All of what `abiPreserved_of` asks of code, as the kernel walks it: no
instruction writes a register of `untouched` or a callee-saved SIMD register,
in the code or in the functions it calls, but in those that restore the
registers of `untouched` (`restoresAll`). -/
noncomputable def abiK (c : Prog isa) : Bool :=
  Code.rec (motive := fun _ => Bool) (fun is => ask (topBlock is)) (fun _ _ a b => andK a b)
    (fun _ _ _ t e => andK t e) (fun _ _ b => b) (fun _ b ih => ask (Bool.rec (restoresAll b) true ih))
    (fun i _ j b => andK (topTestK i) (andK (topTestK j) b))
    (fun i _ b _ ih nx => andK (topTestK i) (andK (ask (Bool.rec (restoresAll b) true ih)) nx)) c

theorem topBlock_eq (is : List Instr) : topBlock is = topAll topTestK (.block is) := by
  rw [topAll_block]
  induction is with
  | nil => rfl
  | cons i is ih =>
    rw [List.all_cons, ← ih]
    exact rec_and _ _

/-- What a called function needs, after `abiK`. -/
def CalleeOk (b : Prog isa) : Prop := topAll topTestK b = true ∨ restoresAll b = true

theorem straight_calls : ∀ {c : Prog isa} {is : List Instr}, straight c = some is → c.calls = []
  | .block _, _, _ => rfl
  | .seq a b, is, h => by
    simp only [straight, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, y, hy, rfl⟩ := h
    rw [Code.calls, straight_calls hx, straight_calls hy]; rfl
  | .ite .., _, h | .loop .., _, h | .call .., _, h | .frame .., _, h | .icall .., _, h => by simp [straight] at h

private theorem callee_ok {n : String} {b : Prog isa} {x : Bool}
    (ih : x = true → topAll topTestK b = true ∧ ∀ nb ∈ b.calls, CalleeOk nb.2)
    (h : ask (Bool.rec (motive := fun _ => Bool) (restoresAll b) true x) = true) : ∀ nb ∈ (n, b) :: b.calls, CalleeOk nb.2 := by
  rw [ask_eq] at h
  intro nb hnb
  cases x with
  | true =>
    rcases List.mem_cons.mp hnb with rfl | hnb
    · exact .inl (ih rfl).1
    · exact (ih rfl).2 nb hnb
  | false =>
    have h : restoresAll b = true := h
    obtain ⟨is, his, _⟩ := (Option.any_eq_true _ _).mp (Bool.and_eq_true_iff.mp h).2
    rw [straight_calls his, List.mem_singleton] at hnb
    exact hnb ▸ .inr h

private theorem abiK_frame (i : Instr) (b : Prog isa) (j : Instr) :
    abiK (.frame i b j) = (topTestK i && (topTestK j && abiK b)) :=
  (rec_and _ _).trans (congrArg _ (rec_and _ _))

private theorem abiK_icall (i : Instr) (n : String) (b nx : Prog isa) :
    abiK (.icall i n b nx) =
      (topTestK i && (ask (Bool.rec (motive := fun _ => Bool) (restoresAll b) true (abiK b)) && abiK nx)) :=
  (rec_and _ _).trans (congrArg _ (rec_and _ _))

theorem abiK_ok : ∀ (c : Prog isa), abiK c = true → topAll topTestK c = true ∧ ∀ nb ∈ c.calls, CalleeOk nb.2
  | .block is, h => by
    have h : ask (topBlock is) = true := h
    rw [ask_eq, topBlock_eq] at h
    exact ⟨h, fun _ hn => absurd hn List.not_mem_nil⟩
  | .seq a b, h | .ite _ a b, h => by
    have h := (rec_and (abiK a) (abiK b)).symm.trans h
    rw [Bool.and_eq_true] at h
    have ha := abiK_ok a h.1
    have hb := abiK_ok b h.2
    refine ⟨Bool.and_eq_true_iff.mpr ⟨ha.1, hb.1⟩, fun nb hn => ?_⟩
    rcases List.mem_append.mp hn with hn | hn
    · exact ha.2 nb hn
    · exact hb.2 nb hn
  | .loop b _, h => abiK_ok b h
  | .call n b, h => ⟨rfl, callee_ok (abiK_ok b) h⟩
  | .frame i b j, h => by
    have h := (abiK_frame i b j).symm.trans h
    simp only [Bool.and_eq_true] at h
    have hb := abiK_ok b h.2.2
    exact ⟨by simp only [topAll, Bool.and_eq_true]; exact ⟨⟨h.1, hb.1⟩, h.2.1⟩, hb.2⟩
  | .icall i n b nx, h => by
    have h := (abiK_icall i n b nx).symm.trans h
    simp only [Bool.and_eq_true] at h
    have hx := abiK_ok nx h.2.2
    refine ⟨by simp only [topAll, Bool.and_eq_true]; exact ⟨h.1, hx.1⟩, fun nb hn => ?_⟩
    rcases List.mem_append.mp hn with hn | hn
    · exact callee_ok (abiK_ok b) h.2.1 nb hn
    · exact hx.2 nb hn

theorem abiK_untouched {c : Prog isa} (h : abiK c = true) : KeepsUntouched c :=
  keepsUntouched_ofK (topAll_mono (fun _ => topTestK_untouched) c (abiK_ok c h).1)

theorem abiK_keepsV {c : Prog isa} (h : abiK c = true) : c.allInstrs keepsV = true :=
  allInstrs_of_top _ c (topAll_mono (fun _ => topTestK_keepsV) c (abiK_ok c h).1)
    (List.all_eq_true.mpr fun nb hnb => by
      rcases (abiK_ok c h).2 nb hnb with h' | h'
      · exact topAll_mono (fun _ => topTestK_keepsV) _ h'
      · exact (Bool.and_eq_true_iff.mp h').1)

theorem abiK_callsKeep {c : Prog isa} (h : abiK c = true) : CallsKeepN c :=
  List.all_eq_true.mpr fun nb hnb => by
    rcases (abiK_ok c h).2 nb hnb with h' | h'
    · exact Bool.or_eq_true_iff.mpr (.inr (Bool.or_eq_true_iff.mpr (.inr
        (keepsUntouched_ofK (topAll_mono (fun _ => topTestK_untouched) _ h')))))
    · refine Bool.or_eq_true_iff.mpr (.inr (Bool.or_eq_true_iff.mpr (.inl (Bool.or_eq_true_iff.mpr (.inl ?_)))))
      have := (Bool.and_eq_true_iff.mp h').2
      rwa [show restoresK = restores from funext fun r => funext (restoresK_eq r)] at this

/-- `abiPreserved_of`, from the one check. -/
theorem abiPreserved_ofK {c : Prog isa} {s s' : State} {t : List Leak} (he : Exec isa c s t s') (h : abiK c = true)
    (hsv : ∀ r ∈ [Reg.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x30], s'.gpr r = s.gpr r) :
    abiPreserved s s' :=
  abiPreserved_ofN he (abiK_callsKeep h) (abiK_untouched h) (abiK_keepsV h) hsv

end VG.Proof.Ecdsa.AArch64
