module
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Continue
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Reject
public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Zero
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.TaintSumGeneric
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Continue
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Reject
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Zero
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.TaintSumGeneric


/-! # Constant-time scalar wrappers around the public rejection loop -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.MlKem.AArch64

theorem rejectEntry_ct (buf out : Nat) : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [])) (.block (rejectEntry buf out)) := by
  unfold rejectEntry ptrTo
  split <;> exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [])
    (fun _ _ _ _ h => h) (hc := .block []) rfl

theorem continueEntry_ct : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [])) (.block continueEntry) := by
  unfold continueEntry
  exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [])
    (fun _ _ _ _ h => h) (hc := .block []) rfl

theorem moveFlag_ct (flag : Reg) : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [])) (.block [mov flag .x0]) := by
  cases flag <;> exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [])
    (fun _ _ _ _ h => h) (hc := .block []) rfl

theorem loadCheckpoint_ct (slot : Nat) : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [.x19]))
    (.block [.ldr .x .x3 .x19 slot,.ldr .x .x4 .x19 (slot+8)]) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x19]) (fun _ _ _ _ h => h) (hc := .block []) rfl

/-- Loading and storing a cursor at `x1`, whose address is public. -/
theorem cursor_ct : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [.x1])) (.block [.ldr .x .x3 .x1 0,.ldr .x .x4 .x1 8]) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x1]) (fun _ _ _ _ h => h) (hc := .block []) rfl

theorem storeCursor_ct : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [.x1])) (.block [.str .x .x3 .x1 0,.str .x .x4 .x1 8]) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x1]) (fun _ _ _ _ h => h) (hc := .block []) rfl

theorem zeroSuffix_ct (w16 : Bool) : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [.x3,.x4])) (Rej8.zeroSuffix w16) := by
  cases w16 <;> exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x3,.x4]) (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.MlKem.AArch64.Paired
