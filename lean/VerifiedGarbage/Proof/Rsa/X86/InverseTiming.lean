module

public import VerifiedGarbage.Proof.Rsa.X86.KeyTiming
public import VerifiedGarbage.Proof.Mont.X86.ExponentTiming

/-! # Binary inversion has a value-independent instruction and address schedule -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Keys
open VG VG.X86 VG.Impl.Rsa.X86.Keys VG.Proof.Mont.X86.Dynamic

theorem invStep_public (n a b : Nat) : KeyPublic (invStep n a b) := by
  unfold invStep
  apply KeyPublic.seqs
  intro c hc
  simp only [subModP, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  simp only [or_assoc] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact bitOf_public .. | exact sub3_public .. | exact sel_public .. |
      exact store_public _ | exact masks_public | exact zeroCarry_public | exact xorCarry_public |
      exact half_public ..

theorem inverse_check (n : Nat) (counter : Bool) : ∃ hint,
    VG.Taint.check taint (workspaceTaint counter) (inverse n) hint = some counterEndTaint := by
  obtain ⟨h1, o1, c1, l1⟩ := invStep_public n 0 4
  obtain ⟨h2, o2, c2, l2⟩ := invStep_public n 4 0
  let bodyHint : VG.Taint.Hint VG.X86.Taint.T :=
    .seq (workspaceTaint true) h1 (.seq (workspaceTaint true) h2 (.block []))
  have body : VG.Taint.check taint (workspaceTaint true)
      (.seq (invStep n 0 4) (.seq (invStep n 4 0)
        (.block [.alu .sub .esi (.imm 1), .alu .cmp .esi (.imm 0)]))) bodyHint = some counterEndTaint :=
    exponent_check_seq taint c1 l1 (exponent_check_seq taint c2 l2 (by rfl))
  have loop : VG.Taint.check taint (workspaceTaint true)
      (.loop (.seq (invStep n 0 4) (.seq (invStep n 4 0)
        (.block [.alu .sub .esi (.imm 1), .alu .cmp .esi (.imm 0)]))) .ne)
      (.loop (workspaceTaint true) bodyHint) = some counterEndTaint := by
    change (if taint.le (workspaceTaint true) (workspaceTaint true) then
      (VG.Taint.check taint (workspaceTaint true) _ bodyHint).bind
        (fun t => if taint.le (workspaceTaint true) t && taint.condPub t .ne then some t else none)
      else none) = _
    rw [body]
    rfl
  have checked : VG.Taint.check taint (workspaceTaint counter) (inverse n)
      (.seq (workspaceTaint true) (.block []) (.loop (workspaceTaint true) bodyHint)) = some counterEndTaint := by
    unfold inverse
    exact exponent_check_seq taint (u := workspaceTaint true) (by cases counter <;> rfl) (by rfl) loop
  exact ⟨_, checked⟩

theorem inverse_public (n : Nat) : KeyPublic (inverse n) := by
  obtain ⟨hint, checked⟩ := inverse_check n true
  exact ⟨hint, counterEndTaint, checked, rfl⟩

theorem inverse_constantTime (n : Nat) :
    ConstantTime isa (fun _ => True) (VG.X86.Taint.Agree (workspaceTaint false)) (inverse n) := by
  obtain ⟨hint, checked⟩ := inverse_check n false
  exact VG.Taint.constantTime (A := taint) (workspaceTaint false) (fun _ _ _ _ h => h)
    (hc := hint) (by rw [checked]; rfl)
end VG.Proof.Rsa.X86.Keys
