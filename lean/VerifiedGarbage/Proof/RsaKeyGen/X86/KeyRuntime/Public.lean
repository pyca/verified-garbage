module

import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyRuntime
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Mont.X86.ExponentTiming
public import VerifiedGarbage.TCB.X86.Isa
public import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.Framework.X86.SseTaint

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
  VG.Taint.check sseTaint runtimeTaint c hint = some out ∧ sseTaint.le runtimeTaint out = true

theorem of_check {c : Prog isa} {hint : VG.Taint.Hint VG.X86.Taint.T}
    (checked : (VG.Taint.check sseTaint runtimeTaint c hint).isSome = true)
    (lower : (VG.Taint.check sseTaint runtimeTaint c hint).all (sseTaint.le runtimeTaint) = true) : Public c := by
  cases result : VG.Taint.check sseTaint runtimeTaint c hint with
  | none => rw [result] at checked; cases checked
  | some out => exact ⟨hint, out, result, by simpa only [result, Option.all_some] using lower⟩

theorem Public.seq {a b : Prog isa} (ha : Public a) (hb : Public b) : Public (.seq a b) := by
  obtain ⟨ah, ao, ac, al⟩ := ha
  obtain ⟨bh, bo, bc, bl⟩ := hb
  exact ⟨.seq runtimeTaint ah bh, bo,
    VG.Proof.Mont.X86.Dynamic.exponent_check_seq sseTaint ac al bc, bl⟩

theorem public_trace {c : Prog isa} (H : Public c) :
    RelCT isa (VG.X86.Taint.Agree runtimeTaint) c (VG.X86.Taint.Agree runtimeTaint) := by
  obtain ⟨hint, out, checked, lower⟩ := H
  intro s t tr ur sf tf A E F
  obtain ⟨T, B⟩ := VG.Taint.check_sound checked A E F
  exact ⟨T, sseTaint.le_sound lower B⟩

end VG.Proof.RsaKeyGen.X86.KeyRuntime
