module

public import VerifiedGarbage.Impl.Secp256k1.X86_64.Joint
public import VerifiedGarbage.Proof.Weierstrass.X86_64.CachedJacTiming
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JacMixedTiming
import VerifiedGarbage.Proof.Secp256k1.X86_64.FieldTmpl
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Mont.X86_64.MulPX
import VerifiedGarbage.Proof.Mont.X86_64.Wide
meta import VerifiedGarbage.Impl.Secp256k1.X86_64.Joint
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.CachedJacTiming
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.JacMixedTiming
meta import VerifiedGarbage.Proof.Secp256k1.X86_64.FieldTmpl
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Mont.X86_64.MulPX
meta import VerifiedGarbage.Proof.Mont.X86_64.Wide

/-! Taint checks of secp256k1's joint verifier's point additions. -/

@[expose] public section

namespace VG.Proof.Secp256k1.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.Secp256k1.X86_64
open VG.Proof.Weierstrass.X86_64

/-- The window of the joint verifier. -/
def nafJacWin := publicJoint.K

theorem nafCachedJac_checks :
    CachedJacChecks nafJacWin nafJacWin.R nafJacWin.E nafJacWin.D 5408 Impl.Weierstrass.dblJ0 := by
  have hT : secp256k1T.Ok nafJacWin.M := secp256k1T_ok
  constructor
  iterate 6 exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)
  iterate 3 exact hT.constantTimeB4 rfl rfl secp256k1D_ok (Taint.ofRegs [.rdi]) rfl (fun _ _ _ _ h => h) _ (by taint_decide)
  exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)

theorem nafMixedJac_checks :
    JacMixedChecks nafJacWin nafJacWin.R nafJacWin.E nafJacWin.D Impl.Weierstrass.dblJ0 := by
  have hT : secp256k1T.Ok nafJacWin.M := secp256k1T_ok
  constructor
  iterate 5 exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)
  iterate 3 exact hT.constantTimeB4 rfl rfl secp256k1D_ok (Taint.ofRegs [.rdi]) rfl (fun _ _ _ _ h => h) _ (by taint_decide)
  exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.Secp256k1.X86_64
