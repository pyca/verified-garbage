module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyRuntime

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Public
meta import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyRuntime
meta import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Public
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint

/-! # The inputs are read through the public argument pointers and lengths. -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86
open VG.Impl.RsaKeyGen.X86.KeyRuntime

/-- `runtimeTaint` with `esi` secret: the inputs' start, where only the arguments, `edi` and `esp` agree. -/
def inputTaint : VG.X86.Taint.T := { runtimeTaint with regs := .ofList [.edi, .esp] }

/-- The inputs, from `inputTaint`, end at least as public as `runtimeTaint`: they set `esi` from the arguments. -/
def InputsPublic : Prop := ∃ hint out,
  VG.Taint.check sseTaint inputTaint loadInputs hint = some out ∧ sseTaint.le runtimeTaint out = true

theorem inputs_of_any {hint : VG.Taint.Hint VG.X86.Taint.T}
    (checked : (VG.Taint.check sseTaint inputTaint loadInputs hint).any (sseTaint.le runtimeTaint) = true) :
    InputsPublic := by
  cases result : VG.Taint.check sseTaint inputTaint loadInputs hint with
  | none => rw [result] at checked; cases checked
  | some out => exact ⟨hint, out, result, by simpa only [result, Option.any_some] using checked⟩

theorem loadInputs_public : InputsPublic := by
  refine inputs_of_any (hint := ?hint) ?check
  case check => taint_decide

end VG.Proof.RsaKeyGen.X86.KeyRuntime
