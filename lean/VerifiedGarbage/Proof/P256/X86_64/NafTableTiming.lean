module

public import VerifiedGarbage.Proof.P256.X86_64.JacTiming
public import VerifiedGarbage.Proof.P256.X86_64.JacTimingAdx
import VerifiedGarbage.Proof.P256.X86_64.FieldTmpl
public import VerifiedGarbage.Proof.Framework.TaintMap
public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableTimingInit
public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableCoZTiming
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
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableCoZTiming
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

theorem nafTableCoZ_checks : NafTableCoZChecks nafJacWin := by
  have hT : p256T.Ok nafJacWin.M := p256T_ok
  constructor
  iterate 2 exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)
  iterate 2 exact hT.constantTime (Taint.ofRegs [.rdi]) rfl (fun _ _ _ _ h => h) _ (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi,.rbx])
      (fun _ _ _ _ h => h) (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rbx])
      (fun _ _ _ _ h => h) (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)

theorem nafTableCoZ_adx_checks : NafTableCoZChecks nafJacWinAdx := by
  have hT : p256XT.Ok nafJacWinAdx.M := p256XT_ok
  constructor
  iterate 2 exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)
  iterate 2 exact hT.constantTime (Taint.ofRegs [.rdi]) rfl (fun _ _ _ _ h => h) _ (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi,.rbx])
      (fun _ _ _ _ h => h) (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rbx])
      (fun _ _ _ _ h => h) (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.P256.X86_64
