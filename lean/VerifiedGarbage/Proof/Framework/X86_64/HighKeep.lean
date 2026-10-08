import VerifiedGarbage.Proof.Framework.X86_64.HighRegs
import VerifiedGarbage.Proof.Framework.X86_64.LaneSse

/-! # Preservation of cached high registers by GCM's loop instructions -/

namespace VG.X86_64

/-- Instructions covered by the high-register preservation lemma. -/
def Instr.keepsH : Instr → Bool
  | .vop _ | .zop _ | .mov .. | .alu .. | .shift ..
  | .vmovdquLoad .. | .vmovdquStore .. | .vmovdqu32Load .. | .vmovdqu32Store ..
  | .vbroadcasti128 .. | .vbroadcasti32x4 .. => true
  | _ => false

theorem HKeep.of_map {α : Type} {x : Option α} {f : α → State} {s t : State}
    (h : x.map f = some t) (hf : ∀ a, HKeep s (f a)) : HKeep s t := by
  obtain ⟨a, _, rfl⟩ := Option.map_eq_some_iff.mp h
  exact hf a

theorem HKeep.alu (op : AluOp) (d : Reg) (a : Src) {s t : State}
    (h : execAlu op d a s = some t) : HKeep s t := by
  simp only [execAlu] at h
  cases he : readSrc s a with
  | none => simp [he] at h
  | some v =>
    simp only [he, Option.bind_some] at h
    cases op
    all_goals first
      | (cases h <;> exact ⟨rfl, rfl⟩)
      | exact HKeep.of_map h (fun _ => ⟨rfl, rfl⟩)

theorem HKeep.shift (op : ShiftOp) (d : Reg) (n : Nat) {s t : State}
    (h : execShift op d n s = some t) : HKeep s t := by
  cases op <;> simp only [execShift] at h
  all_goals split at h
  all_goals cases h <;> exact ⟨rfl, rfl⟩

theorem HKeep.instr {i : Instr} (hi : i.keepsH = true) {s t : State}
    (he : exec i s = some t) : HKeep s t := by
  cases i <;> simp only [Instr.keepsH, Bool.false_eq_true] at hi
  case mov d a => exact HKeep.of_map he (fun _ => ⟨rfl, rfl⟩)
  case alu op d a => exact HKeep.alu op d a he
  case shift op d n => exact HKeep.shift op d n he
  case vop op =>
    simp only [exec, Option.some.injEq] at he
    subst t
    cases op <;> first
      | exact ⟨rfl, rfl⟩
      | (simp only [VOp.exec]; split <;> exact ⟨rfl, rfl⟩)
  case zop op =>
    simp only [exec, Option.some.injEq] at he
    subst t
    exact HKeep.zop op s
  case vmovdquLoad len d m =>
    cases len <;> exact HKeep.of_map he (fun _ => ⟨rfl, rfl⟩)
  case vmovdquStore len m r =>
    cases len <;> simp only [exec, State.store128, State.store256] at he
    all_goals split at he
    all_goals cases he <;> exact ⟨rfl, rfl⟩
  case vmovdqu32Load d m => exact HKeep.of_map he (fun _ => ⟨rfl, rfl⟩)
  case vmovdqu32Store m r =>
    simp only [exec, State.store512] at he
    split at he <;> cases he
    exact ⟨rfl, rfl⟩
  case vbroadcasti128 d m => exact HKeep.of_map he (fun _ => ⟨rfl, rfl⟩)
  case vbroadcasti32x4 d m => exact HKeep.of_map he (fun _ => ⟨rfl, rfl⟩)

theorem HKeep.block : ∀ {is : List Instr} {s t : State}, is.all Instr.keepsH = true →
    runBlock isa is s = some t → HKeep s t
  | [], _, _, _, he => by cases he; exact HKeep.refl _
  | i :: is, s, t, hi, he => by
    simp only [List.all_cons, Bool.and_eq_true] at hi
    rw [runBlock_cons] at he
    cases hs : exec i s with
    | none => simp [hs, runStep] at he
    | some u =>
      rw [hs, runStep_some] at he
      exact (HKeep.instr hi.1 hs).trans (HKeep.block hi.2 he)

theorem WP.hkeep {is : List Instr} {s : State} {Q : State → Prop}
    (hi : is.all Instr.keepsH = true) (h : WP isa (.block is) s Q) :
    WP isa (.block is) s fun t => Q t ∧ HKeep s t := by
  obtain ⟨t, he, hq⟩ := WP.runBlock_of h
  exact WP.of_runBlock ⟨t, he, hq, HKeep.block hi he⟩

/-- Calls and frames are excluded: this is the invariant rule for the local loops. -/
theorem HKeep.code {c : Prog isa} {s t : State} {tr : List Leak} (he : Exec isa c s tr t)
    (hn : c.noCalls = true) (hi : c.all Instr.keepsH = true) : HKeep s t := by
  induction he with
  | block hb =>
    rename_i is s t tr
    have hw : WP isa (.block is) s (fun u => u = t) := ⟨tr, t, .block hb, rfl⟩
    obtain ⟨u, hu, rfl⟩ := WP.runBlock_of hw
    exact HKeep.block hi hu
  | seq _ _ ih₁ ih₂ =>
    simp only [Code.noCalls, Code.all, Bool.and_eq_true] at hn hi
    exact (ih₁ hn.1 hi.1).trans (ih₂ hn.2 hi.2)
  | iteT _ _ ih =>
    simp only [Code.noCalls, Code.all, Bool.and_eq_true] at hn hi
    exact ih hn.1 hi.1
  | iteF _ _ ih =>
    simp only [Code.noCalls, Code.all, Bool.and_eq_true] at hn hi
    exact ih hn.2 hi.2
  | loopExit _ _ ih => exact ih hn hi
  | loopNext _ _ _ ih₁ ih₂ => exact (ih₁ hn hi).trans (ih₂ hn hi)
  | call => simp [Code.noCalls] at hn
  | frame => simp [Code.noCalls] at hn

theorem WP.hkeepCode {c : Prog isa} {s : State} {Q : State → Prop}
    (hn : c.noCalls = true) (hi : c.all Instr.keepsH = true) (h : WP isa c s Q) :
    WP isa c s fun t => Q t ∧ HKeep s t := by
  obtain ⟨tr, t, he, hq⟩ := h
  exact ⟨tr, t, he, hq, HKeep.code he hn hi⟩

end VG.X86_64
