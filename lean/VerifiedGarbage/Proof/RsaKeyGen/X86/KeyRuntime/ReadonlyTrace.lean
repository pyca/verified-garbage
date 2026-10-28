module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.LoadInputsPublic
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Readonly
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyArgContext
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.InputTiming

/-! # Workspace code whose taint check starts with `esi` secret has public timing -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86
open VG.Proof.RsaKeyGen.X86.KeyArgs (Context)

/-- The check of `c` from `inputTaint` succeeds, at least as public as `τ`. -/
def FromInputs (c : Prog isa) (τ : VG.X86.Taint.T) : Prop := ∃ hint out,
  VG.Taint.check sseTaint inputTaint c hint = some out ∧ sseTaint.le τ out = true

theorem fromInputs_of_any {c : Prog isa} {τ : VG.X86.Taint.T} {hint : VG.Taint.Hint VG.X86.Taint.T}
    (checked : (VG.Taint.check sseTaint inputTaint c hint).any (sseTaint.le τ) = true) : FromInputs c τ := by
  cases result : VG.Taint.check sseTaint inputTaint c hint with
  | none => rw [result] at checked; cases checked
  | some out => exact ⟨hint, out, result, by simpa only [result, Option.any_some] using checked⟩

/-- Two runs of workspace code that also runs on the read-only views have one trace, and agree on
the registers `τ` makes public. -/
theorem readonly_trace {c : Prog isa} {τ : VG.X86.Taint.T} (H : FromInputs c τ)
    {B : Addr} {Z n : Nat} {sp : BitVec 32} {args : Nat → BitVec 32} {s t u v : State} {tr ur : List Leak}
    (Hs : Ws s B Z n 32) (Ht : Ws t B Z n 32) (Cs : Context B Z sp args s) (Ct : Context B Z sp args t)
    (runS : WP isa c (readonly s B Z) fun _ => True) (runT : WP isa c (readonly t B Z) fun _ => True)
    (A : Exec isa c s tr u) (C : Exec isa c t ur v) :
    tr = ur ∧ ∀ r, VG.X86.Taint.pub τ r = true → u.gpr r = v.gpr r := by
  obtain ⟨u', AS⟩ := trace_readonly_of_wp Hs runS A
  obtain ⟨v', CT⟩ := trace_readonly_of_wp Ht runT C
  obtain ⟨hint, out, checked, lower⟩ := H
  obtain ⟨trace, agreeOut⟩ := VG.Taint.check_sound checked (input_agree Cs Ct Hs.hdr_le) AS CT
  have agree := sseTaint.le_sound lower agreeOut
  obtain ⟨sRead, sWrite⟩ := readonly_covers Hs
  obtain ⟨tRead, tWrite⟩ := readonly_covers Ht
  have widenedS := VG.X86.Exec.widen AS sRead sWrite
  have widenedT := VG.X86.Exec.widen CT tRead tWrite
  simp only [readonly, State.withRegions_withRegions, State.withRegions_self] at widenedS widenedT
  have endS := (Exec.det A widenedS).2
  have endT := (Exec.det C widenedT).2
  refine ⟨trace, fun r hr => ?_⟩
  rw [endS, endT]
  exact agree.reg hr

end VG.Proof.RsaKeyGen.X86.KeyRuntime
