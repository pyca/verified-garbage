module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyRuntime
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.ReadonlyTrace
public import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyRuntime
meta import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.ReadonlyTrace
meta import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Public
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Framework.X86.RelCT

/-! # The outputs' addresses and counts come from the public arguments -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Impl.RsaKeyGen.X86.Key (outputIndex)

/-- The zero array cleared, from the outputs' start. -/
theorem zeroOutputs_public : FromInputs (zero .modulus (arr VG.Impl.Rsa.X86.Keys.aZero)) inputTaint := by
  refine fromInputs_of_any (hint := ?hint) ?check
  case check => taint_decide

/-- After a port's setup, the workspace, the stack, and the destination, count and source of its
copy are public. -/
def portTaint : VG.X86.Taint.T := { runtimeTaint with regs := .ofList [.edi, .esp, .ebx, .ecx, .esi] }

theorem setup0_public : FromInputs (arraySetup (outputIndex 0) 0 1) portTaint := by
  refine fromInputs_of_any (hint := ?hint) ?check
  case check => taint_decide

theorem setup1_public : FromInputs (arraySetup (outputIndex 1) 2 3) portTaint := by
  refine fromInputs_of_any (hint := ?hint) ?check
  case check => taint_decide

theorem setup2_public : FromInputs (arraySetup (outputIndex 2) 4 5) portTaint := by
  refine fromInputs_of_any (hint := ?hint) ?check
  case check => taint_decide

theorem setup3_public : FromInputs (arraySetup (outputIndex 3) 6 7) portTaint := by
  refine fromInputs_of_any (hint := ?hint) ?check
  case check => taint_decide

theorem setup4_public : FromInputs (arraySetup (outputIndex 4) 8 9) portTaint := by
  refine fromInputs_of_any (hint := ?hint) ?check
  case check => taint_decide

theorem setup5_public : FromInputs (arraySetup (outputIndex 5) 10 11) portTaint := by
  refine fromInputs_of_any (hint := ?hint) ?check
  case check => taint_decide

theorem setup6_public : FromInputs (arraySetup (outputIndex 6) 12 13) portTaint := by
  refine fromInputs_of_any (hint := ?hint) ?check
  case check => taint_decide

/-- The copy reads the array's bytes only as data. -/
def ReverseChecked : Prop := ∃ hint out,
  VG.Taint.check sseTaint (τr [.edi, .esp, .ebx, .ecx, .esi]) VG.Impl.Bignum.X86.reverseBytes hint = some out ∧
    sseTaint.le (τr [.edi, .esp, .esi]) out = true

theorem reverse_public : ReverseChecked := by
  have H {hint : VG.Taint.Hint VG.X86.Taint.T}
      (checked : (VG.Taint.check sseTaint (τr [.edi, .esp, .ebx, .ecx, .esi]) VG.Impl.Bignum.X86.reverseBytes
        hint).any (sseTaint.le (τr [.edi, .esp, .esi])) = true) : ReverseChecked := by
    cases result : VG.Taint.check sseTaint (τr [.edi, .esp, .ebx, .ecx, .esi]) VG.Impl.Bignum.X86.reverseBytes hint with
    | none => rw [result] at checked; cases checked
    | some out => exact ⟨hint, out, result, by simpa only [result, Option.any_some] using checked⟩
  refine H (hint := ?hint) ?check
  case check => taint_decide

end VG.Proof.RsaKeyGen.X86.KeyRuntime
