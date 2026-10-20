module

public import VerifiedGarbage.Proof.Rsa.X86.KeyTiming
public import VerifiedGarbage.Impl.Rsa.X86.MulMod
public import VerifiedGarbage.Proof.Mont.X86.ExponentTiming

/-! # Public schedules for binary modular multiplication on i686 -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Keys
open VG VG.X86 VG.Impl.Rsa.X86.Keys VG.Proof.Mont.X86.Dynamic

theorem addMod_public (w o a b m z t : Nat) : KeyPublic (seqs (addMod w o a b m z t)) := by
  apply KeyPublic.seqs
  intro c hc
  simp only [addMod, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl
  · exact sub3_public ..
  · exact sub3_public ..
  · exact sub3_public ..
  · exact store_public _
  · exact sel_public ..

theorem mulHead_public (w z y x t : Nat) : KeyPublic (mulHead w z y x t) :=
  (bitOf_public ..).seq (sel_public ..)

theorem mulMod_check (w z y x a m t : Nat) : ∃ hint,
    VG.Taint.check taint (workspaceTaint true) (mulMod w z y x a m t) hint = some counterEndTaint := by
  obtain ⟨h1, o1, c1, l1⟩ := mulHead_public w z y x t
  obtain ⟨h2, o2, c2, l2⟩ := addMod_public w a a t m z (t + 1)
  obtain ⟨h3, o3, c3, l3⟩ := addMod_public w x x x m z (t + 1)
  obtain ⟨h4, o4, c4, l4⟩ := zeroCarry_public
  obtain ⟨h5, o5, c5, l5⟩ := half_public w y
  let tailHint : VG.Taint.Hint VG.X86.Taint.T :=
    .seq (workspaceTaint true) h4 (.seq (workspaceTaint true) h5 (.block []))
  have tail : VG.Taint.check taint (workspaceTaint true) (mulTail w y) tailHint = some counterEndTaint :=
    exponent_check_seq taint c4 l4 (exponent_check_seq taint c5 l5 (by rfl))
  let bodyHint : VG.Taint.Hint VG.X86.Taint.T := .seq (workspaceTaint true) h1
    (.seq (workspaceTaint true) h2 (.seq (workspaceTaint true) h3 tailHint))
  have body : VG.Taint.check taint (workspaceTaint true) (mulModStep w z y x a m t) bodyHint =
      some counterEndTaint :=
    exponent_check_seq taint c1 l1 (exponent_check_seq taint c2 l2 (exponent_check_seq taint c3 l3 tail))
  refine ⟨.loop (workspaceTaint true) bodyHint, ?_⟩
  change (if taint.le (workspaceTaint true) (workspaceTaint true) then
    (VG.Taint.check taint (workspaceTaint true) _ bodyHint).bind
      (fun u => if taint.le (workspaceTaint true) u && taint.condPub u .ne then some u else none)
    else none) = _
  rw [body]
  rfl

theorem mulMod_public (w z y x a m t : Nat) : KeyPublic (mulMod w z y x a m t) := by
  obtain ⟨hint, checked⟩ := mulMod_check w z y x a m t
  exact ⟨hint, counterEndTaint, checked, rfl⟩

theorem mulMod_constantTime (w z y x a m t : Nat) :
    ConstantTime isa (fun _ => True) (VG.X86.Taint.Agree (workspaceTaint true)) (mulMod w z y x a m t) := by
  obtain ⟨hint, checked⟩ := mulMod_check w z y x a m t
  exact VG.Taint.constantTime (A := taint) (workspaceTaint true) (fun _ _ _ _ h => h)
    (hc := hint) (by rw [checked]; rfl)
end VG.Proof.Rsa.X86.Keys
