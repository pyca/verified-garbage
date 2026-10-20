module

public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming

/-! # Secret arithmetic blocks preserve the public exponent counter -/

@[expose] public section
namespace VG.Proof.Mont.X86.Dynamic
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic

theorem exponent_check_append {M : ISA} (A : VG.Taint M) (τ : A.T) (a b : List M.Instr) :
    A.checkBlock τ (a ++ b) = (A.checkBlock τ a).bind (A.checkBlock · b) := by
  induction a generalizing τ with
  | nil => rfl
  | cons i is ih =>
    change (A.step τ i).bind (fun t => A.checkBlock t (is ++ b)) =
      ((A.step τ i).bind (fun t => A.checkBlock t is)).bind (A.checkBlock · b)
    rw [Option.bind_assoc]
    simp only [ih]

theorem exponentMask_taint (exp mask : Nat) :
    taint.checkBlock (workspaceTaint true) (exponentMask exp mask) = some (workspaceTaint true) := by
  rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (workspaceTaint true) = true from rfl)]
  change taint.checkBlock (workspaceTaint true)
    [.mov .ecx (.mem (sc 0)), .alu .and .ecx (.imm 0), .mov .eax (.imm 0),
      .alu .sub .eax (.reg .ecx), .store (sc 0) .eax] = _
  rfl

theorem shiftWord_taint (out : Nat) (last : Bool) :
    taint.checkBlock (workspaceTaint true) (shiftWord out last) = some (if last then zeroTaint true else workspaceTaint true) := by
  cases last <;>
    rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (workspaceTaint true) = true from rfl)]
  · change taint.checkBlock (workspaceTaint true)
      [.mov .eax (.mem (sc 0)), .alu .and .eax (.imm 0), .shift .ror .eax 0,
       .mov .edx (.mem (sc 0)), .shift .shr .edx 0, .alu .add .edx (.reg .eax), .store (sc 0) .edx] = _
    rfl
  · change taint.checkBlock (workspaceTaint true)
      [.mov .eax (.imm 0), .alu .and .eax (.imm 0), .shift .ror .eax 0,
       .mov .edx (.mem (sc 0)), .shift .shr .edx 0, .alu .add .edx (.reg .eax), .store (sc 0) .edx] = _
    rfl

theorem shiftExponent_taint (n out : Nat) :
    taint.checkBlock (workspaceTaint true) (shiftExponent n out) =
      some (if n = 0 then workspaceTaint true else zeroTaint true) := by
  induction n generalizing out with
  | zero => rfl
  | succ n ih =>
    rw [shiftExponent, exponent_check_append taint (workspaceTaint true), shiftWord_taint]
    cases n with
    | zero => rfl
    | succ n =>
      change taint.checkBlock (workspaceTaint true) (shiftExponent (n + 1) (out + 4)) = _
      exact ih (out + 4)

end VG.Proof.Mont.X86.Dynamic
