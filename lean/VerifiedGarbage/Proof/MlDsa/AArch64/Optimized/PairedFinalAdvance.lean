import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFinalCheck
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedCallFrame
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def finalAdvance : List Instr :=
  [.addImm .x .x2 .x2 16,.addImm .x .x15 .x15 16,.addImm .x .x16 .x16 16,.subImm .x .x12 .x12 1]

theorem finalAdvance_ok (s : State) : WP isa (.block finalAdvance) s fun t =>
    ((t.gpr .x2=s.gpr .x2+16 ∧ t.gpr .x15=s.gpr .x15+16 ∧
      t.gpr .x16=s.gpr .x16+16 ∧ t.gpr .x12=s.gpr .x12-1 ∧ t.mem=s.mem) ∧
      Keep [.x2,.x12,.x15,.x16] s t) ∧ t.v=s.v := by
  apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv:=rfl)
  unfold finalAdvance
  arun
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem final_z_eq (g : Nat) : VG.Impl.MlDsa.AArch64.Optimized.Paired.final .z g=
    finalCheckCode false++finalAdvance := by
  unfold VG.Impl.MlDsa.AArch64.Optimized.Paired.final finalCheckCode
  rw [finalPrefix_eq]
  have he : ([0,1].flatMap fun p => (List.range 8).flatMap fun j =>
      VG.Impl.MlDsa.AArch64.Optimized.Paired.check .z g p j)=checkRunCode false allChecks := by
    simp only [zCheck_eq]
    rfl
  rw [he]
  simp only [List.append_assoc]
  rfl

theorem final_h_eq (g : Nat) : VG.Impl.MlDsa.AArch64.Optimized.Paired.final .h g=
    finalCheckCode true++finalAdvance := by
  unfold VG.Impl.MlDsa.AArch64.Optimized.Paired.final finalCheckCode
  rw [finalPrefix_eq]
  have he : ([0,1].flatMap fun p => (List.range 8).flatMap fun j =>
      VG.Impl.MlDsa.AArch64.Optimized.Paired.check .h g p j)=checkRunCode true allChecks := by
    simp only [hCheck_eq]
    decide +kernel
  rw [he]
  simp only [List.append_assoc]
  rfl

end VG.Proof.MlDsa.AArch64.Optimized.Paired
