module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyInverse
public import VerifiedGarbage.Proof.Rsa.X86.KeyTiming

import VerifiedGarbage.Proof.Rsa.X86.CvHelperTiming
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Mont.X86.ExponentTiming
/-! # The inverse wrapper's complete schedule is independent of its inputs -/

-- Formerly `VerifiedGarbage/Proof/Rsa/X86/InverseTiming.lean`, which only this module imported.
section

/-! # Binary inversion has a value-independent instruction and address schedule -/

section
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
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Rsa.X86.Keys VG.Proof.Mont.X86.Dynamic
open VG.Impl.Rsa.X86.Keys VG.Impl.RsaKeyGen.X86.Key

theorem copyWords_public (n src dst : Nat) : KeyPublic (VG.Impl.Rsa.X86.Div.copyWords n src dst) := by
  refine ⟨(VG.Taint.hintOf taint (workspaceTaint true) (Code.erase (VG.Impl.Rsa.X86.Div.copyWords 1 0 0))),
      ({ regs := .ofList [.edi, .esi, .ebp, .edx, .ecx], flags := true } : VG.X86.Taint.T), ?_, by decide +kernel⟩
  exact (check_of_erase_eq (VG.Impl.Rsa.X86.Div.copyWords n src dst) (VG.Impl.Rsa.X86.Div.copyWords 1 0 0)
    (workspaceTaint true) (VG.Taint.hintOf taint (workspaceTaint true) (Code.erase (VG.Impl.Rsa.X86.Div.copyWords 1 0 0))) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)).trans (by kernel_rfl)

theorem setOne_public (n j : Nat) : KeyPublic (.block (setOne n j)) := by
  refine ⟨(VG.Taint.hintOf taint (workspaceTaint true) (.block [.mov .eax (.imm 0),
      .store (VG.Impl.Mont.X86.sc 0) .eax] : Prog isa)), ({ regs := .ofList [.edi, .esi, .eax], flags := false } : VG.X86.Taint.T), ?_, by decide +kernel⟩
  exact (check_of_erase_eq (.block (setOne n j)) (.block [.mov .eax (.imm 0), .store (VG.Impl.Mont.X86.sc 0) .eax] : Prog isa)
    (workspaceTaint true) (VG.Taint.hintOf taint (workspaceTaint true) (.block [.mov .eax (.imm 0),
        .store (VG.Impl.Mont.X86.sc 0) .eax] : Prog isa)) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)).trans (by kernel_rfl)

theorem inverseBank_public (n : Nat) : KeyPublic (inverseBank n) := by
  unfold inverseBank
  apply KeyPublic.seqs
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact copy_public ..
  · exact setOne_public ..
  · exact sub3_public ..

theorem inverseLoad_public (n src mo : Nat) : KeyPublic (inverseLoad n src mo) := by
  unfold inverseLoad
  apply KeyPublic.seqs
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact ⟨zerosHint true, zerosTaint true, zeros_check true _ _, rfl⟩
  · exact copyWords_public ..
  · exact copyWords_public ..

theorem inverseFrom_public (n src mo : Nat) : KeyPublic (inverseFrom n src mo) := by
  exact ((inverseLoad_public n src mo).seq (inverseBank_public n)).seq (inverse_public n)

theorem inverseFrom_constantTime (n src mo : Nat) :
    ConstantTime isa (fun _ => True) (VG.X86.Taint.Agree (workspaceTaint true)) (inverseFrom n src mo) := by
  obtain ⟨hint, out, checked, _⟩ := inverseFrom_public n src mo
  exact VG.Taint.constantTime (A := taint) (workspaceTaint true) (fun _ _ _ _ H => H)
    (hc := hint) (by rw [checked]; rfl)

end VG.Proof.RsaKeyGen.X86.Key
