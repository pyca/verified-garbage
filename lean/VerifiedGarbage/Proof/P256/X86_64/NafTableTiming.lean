module

public import VerifiedGarbage.Proof.P256.X86_64.JacTiming
public import VerifiedGarbage.Proof.P256.X86_64.JacTimingAdx
import VerifiedGarbage.Proof.P256.X86_64.FieldTmpl
public import VerifiedGarbage.Proof.Framework.TaintMap
public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableTimingInit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Mont.X86_64.MulPX
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.Weierstrass.CombLay
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombDigit
meta import VerifiedGarbage.Proof.P256.X86_64.JacTiming
meta import VerifiedGarbage.Proof.P256.X86_64.JacTimingAdx
meta import VerifiedGarbage.Proof.P256.X86_64.FieldTmpl
meta import VerifiedGarbage.Proof.Framework.TaintMap
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableTimingInit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Mont.X86_64.MulPX
meta import VerifiedGarbage.Proof.Mont.X86_64.Wide
meta import VerifiedGarbage.Proof.Weierstrass.CombLay
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombDigit

/-! Baseline and ADX taint checks for the verifier's odd-multiple table. -/

@[expose] public section

namespace VG.Proof.P256.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64 VG.Proof.Weierstrass.X86_64

theorem nafTable_checks : NafTableChecks nafJacWin := by
  have hT : p256T.Ok nafJacWin.M := p256T_ok
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
  have hT : p256XT.Ok nafJacWinAdx.M := p256XT_ok
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

end VG.Proof.P256.X86_64
