module
public import VerifiedGarbage.Impl.Dsa.X86.Generate
public import VerifiedGarbage.Proof.Dsa.X86.DispatchTiming

/-! # Constant-time dispatch over the public generation widths -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Mont.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem checkDispatch_relCT (widths : List (Nat × Nat)) (pLen qLen : Nat)
    (base : Addr) (size : Nat) (R Q : State → State → Prop)
    (I : CompareInvariant base size R) (hz : Layout.saved ≤ size)
    (member : (pLen, qLen) ∈ widths) (bound : ∀ w ∈ widths, w.1 < 2 ^ 32 ∧ w.2 < 2 ^ 32)
    (P : ∀ s t, R s t → (pointerValue base s (.input .pLen)).toNat = pLen ∧
      (pointerValue base t (.input .pLen)).toNat = pLen)
    (Qlen : ∀ s t, R s t → (pointerValue base s (.input .qLen)).toNat = qLen ∧
      (pointerValue base t (.input .qLen)).toNat = qLen)
    (body : RelCT isa R (Generate.checkSized pLen qLen) Q) :
    RelCT isa R (Generate.checkDispatch widths) Q := by
  induction widths with
  | nil => simp only [List.not_mem_nil] at member
  | cons w rest ih =>
    obtain ⟨wp, wq⟩ := w
    have B := bound (wp, wq) List.mem_cons_self
    have Brest : ∀ w ∈ rest, w.1 < 2 ^ 32 ∧ w.2 < 2 ^ 32 :=
      fun w hw => bound w (List.mem_cons_of_mem _ hw)
    unfold Generate.checkDispatch
    refine RelCT.seq (widthMatch_relCT base size pLen qLen wp wq R I hz P Qlen B.1 B.2)
      (fixedChoice_relCT (decide (pLen = wp ∧ qLen = wq)) ?_)
    by_cases Both : pLen = wp ∧ qLen = wq
    · simp only [Both, true_and, decide_true, ite_true]
      rw [← Both.1, ← Both.2]
      exact body
    · simp only [Both, decide_false]
      exact ih (by simpa only [List.mem_cons, Prod.mk.injEq, Both, false_or] using member) Brest

end VG.Proof.Dsa.X86
