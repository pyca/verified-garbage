import VerifiedGarbage.Proof.P384.X86_64.JacTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableTiming

/-! Baseline and ADX taint checks for P-384's verifier's odd-multiple table.

The field arithmetic is checked without its displacements, as the
templates of its operations (`FieldTmpl`), each analysed once; so is the
addition that keeps `rbx` (`KeepReg.keepsN`, which the kernel evaluates
once for each template from the same state). -/
namespace VG.Proof.P384.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Proof.Weierstrass.X86_64

theorem nafTable_checks : NafTableChecks nafJacWin := by
  have hT : p384T.Ok nafJacWin.M := p384T_ok
  constructor
  · exact hT.constantTime (Taint.ofRegs [.rdi]) rfl (fun _ _ _ _ h => h) _ (by taint_decide)
  iterate 3 exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)
  · constructor
    iterate 6 exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)
    iterate 3 exact hT.constantTime (Taint.ofRegs [.rdi]) rfl (fun _ _ _ _ h => h) _ (by taint_decide)
    exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi])
      (fun _ _ _ _ h => h) (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi,.rbx])
      (fun _ _ _ _ h => h) (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rbx])
      (fun _ _ _ _ h => h) (by taint_decide)
  · rw [← KeepReg.keeps_erase, ← KeepReg.keepsN_eq]
    simp only [Jacobian.jacAdd, Code.inline, Code.erase, Code.mapBlocks, hT.fprogB_mapBlocks]
    lit_decide
  · exact instrs_noClobber (by decide +kernel)

theorem nafTable_adx_checks : NafTableChecks nafJacWinAdx := by
  have hT : p384XT.Ok nafJacWinAdx.M := p384XT_ok
  constructor
  · exact hT.constantTime (Taint.ofRegs [.rdi]) rfl (fun _ _ _ _ h => h) _ (by taint_decide)
  iterate 3 exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)
  · constructor
    iterate 6 exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)
    iterate 3 exact hT.constantTime (Taint.ofRegs [.rdi]) rfl (fun _ _ _ _ h => h) _ (by taint_decide)
    exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi])
      (fun _ _ _ _ h => h) (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi,.rbx])
      (fun _ _ _ _ h => h) (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rbx])
      (fun _ _ _ _ h => h) (by taint_decide)
  · rw [← KeepReg.keeps_erase, ← KeepReg.keepsN_eq]
    simp only [Jacobian.jacAdd, Code.inline, Code.erase, Code.mapBlocks, hT.fprogB_mapBlocks]
    lit_decide
  · exact instrs_noClobber (by decide +kernel)

end VG.Proof.P384.X86_64
