import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Domain

namespace VG.Proof.Weierstrass.AArch64.Forward
open VG VG.AArch64

/-- The slot written by a decoded instruction, if any. -/
def Decoded.writeSlot : Decoded → Option Nat
  | .store _ off => some off
  | _ => none

/-- Slot addresses that this instruction sequence may write. -/
def writeSlots (is : List Instr) : List Nat :=
  is.filterMap fun i => (decode i).bind fun v => v.val.writeSlot

theorem decodedStep_slot_unchanged {α : Type} {D : Dom α} {size off : Nat}
    {e e' : Env α} {i : Decoded} (h : decodedStep D size e i = some e')
    (hn : i.writeSlot ≠ some off) : e'.slot off = e.slot off := by
  cases i with
  | scalar op d a b c =>
    simp only [decodedStep] at h
    split at h
    · contradiction
    · simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨va, _, vb, _, vc, _, vd, _, cf, _, vr, _, rfl⟩ := h
      rfl
  | load d j =>
    simp only [decodedStep] at h
    split at h
    · contradiction
    · cases h; rfl
  | store r j =>
    simp only [decodedStep] at h
    split at h
    · contradiction
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨v, _, rfl⟩ := h
      have hne : off ≠ j := by intro h; subst off; exact hn rfl
      exact ite_eq_right hne

theorem eval_slot_unchanged {α : Type} {D : Dom α} {size off : Nat}
    {is : List Instr} {e e' : Env α} (h : eval D size is e = some e')
    (hn : off ∉ writeSlots is) : e'.slot off = e.slot off := by
  induction is generalizing e with
  | nil => cases h; rfl
  | cons i is ih =>
    simp only [eval, Option.bind_eq_some_iff] at h
    obtain ⟨mid, hs, ht⟩ := h
    have nt : off ∉ writeSlots is := by
      intro hm
      exact hn (by simp only [writeSlots, List.filterMap_cons]; split <;> simp_all [writeSlots])
    rw [ih ht nt]
    cases hd : decode i with
    | none => simp [step, hd] at hs
    | some view =>
      apply decodedStep_slot_unchanged (by simpa [step, hd] using hs)
      intro hw
      apply hn
      simp [writeSlots, hd, hw]

/-- Check equality only at the slots either execution can write. All other slots
retain their common initial value. -/
theorem slots_eq_of_written {D : Dom Nat} {size : Nat} {is js : List Instr}
    {e left right : Env Nat} (hl : eval D size is e = some left)
    (hr : eval D size js e = some right)
    (h : (writeSlots is ++ writeSlots js).eraseDups.all
      (fun off => decide (left.slot off = right.slot off)) = true) :
    ∀ off, left.slot off = right.slot off := by
  intro off
  by_cases hm : off ∈ (writeSlots is ++ writeSlots js).eraseDups
  · exact of_decide_eq_true (List.all_eq_true.mp h off hm)
  · have hn : off ∉ writeSlots is ∧ off ∉ writeSlots js := by
      simpa only [List.mem_eraseDups, List.mem_append, not_or] using hm
    exact (eval_slot_unchanged hl hn.1).trans (eval_slot_unchanged hr hn.2).symm

/-- Restrict the written-slot check to the observations required by the caller. -/
theorem slots_eq_of_written_where {D : Dom Nat} {size : Nat} {is js : List Instr}
    {e left right : Env Nat} (observe : Nat → Prop) [DecidablePred observe]
    (hl : eval D size is e = some left) (hr : eval D size js e = some right)
    (h : (writeSlots is ++ writeSlots js).eraseDups.all
      (fun off => decide (observe off → left.slot off = right.slot off)) = true) :
    ∀ off, observe off → left.slot off = right.slot off := by
  intro off ho
  by_cases hm : off ∈ (writeSlots is ++ writeSlots js).eraseDups
  · exact of_decide_eq_true (List.all_eq_true.mp h off hm) ho
  · have hn : off ∉ writeSlots is ∧ off ∉ writeSlots js := by
      simpa only [List.mem_eraseDups, List.mem_append, not_or] using hm
    exact (eval_slot_unchanged hl hn.1).trans (eval_slot_unchanged hr hn.2).symm

end VG.Proof.Weierstrass.AArch64.Forward
