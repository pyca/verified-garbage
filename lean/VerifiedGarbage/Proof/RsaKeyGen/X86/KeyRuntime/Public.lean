module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyRuntime
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Mont.X86.ExponentTiming

/-! # Shared arithmetic reads the public cdecl widths without exposing the factors -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86
open VG.Impl.RsaKeyGen.X86.KeyRuntime

/-- Four private saved words precede the original return address and arguments. -/
def runtimeTaint : VG.X86.Taint.T := {
  regs := .ofList [.edi, .esi, .esp], flags := false
  argLen := 76, stk := [none, none, none, none] }

def Public (c : Prog isa) : Prop := ∃ hint out,
  VG.Taint.check taint runtimeTaint c hint = some out ∧ taint.le runtimeTaint out = true

theorem of_check {c : Prog isa} {hint : VG.Taint.Hint VG.X86.Taint.T}
    (checked : (VG.Taint.check taint runtimeTaint c hint).isSome = true)
    (lower : (VG.Taint.check taint runtimeTaint c hint).all (taint.le runtimeTaint) = true) : Public c := by
  cases result : VG.Taint.check taint runtimeTaint c hint with
  | none => rw [result] at checked; cases checked
  | some out => exact ⟨hint, out, result, by simpa only [result, Option.all_some] using lower⟩

theorem Public.seq {a b : Prog isa} (ha : Public a) (hb : Public b) : Public (.seq a b) := by
  obtain ⟨ah, ao, ac, al⟩ := ha
  obtain ⟨bh, bo, bc, bl⟩ := hb
  exact ⟨.seq runtimeTaint ah bh, bo,
    VG.Proof.Mont.X86.Dynamic.exponent_check_seq taint ac al bc, bl⟩

theorem public_trace {c : Prog isa} (H : Public c) :
    RelCT isa (VG.X86.Taint.Agree runtimeTaint) c (VG.X86.Taint.Agree runtimeTaint) := by
  obtain ⟨hint, out, checked, lower⟩ := H
  exact VG.Proof.Dsa.X86.checkedProgramChange checked lower

end VG.Proof.RsaKeyGen.X86.KeyRuntime
