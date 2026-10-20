module

public import VerifiedGarbage.Proof.Sha256.AArch64.Variant
public import VerifiedGarbage.Proof.Sha256.AArch64.Compress
import VerifiedGarbage.Proof.Sha256.AArch64.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Sha256.AArch64.Variant
meta import VerifiedGarbage.Proof.Sha256.AArch64.Compress
meta import VerifiedGarbage.Proof.Sha256.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

@[expose] public section

namespace VG.Proof.Sha256.AArch64.Scalar

open VG.AArch64

/-- The scalar compression backend and the checked facts its streaming callers need. -/
def backend : Compress where
  name := "vg_sha256_compress"
  code := Impl.Sha256.AArch64.compress
  verified := Proof.Sha256.AArch64.compress_verified
  noFrames := by lit_decide
  keepsV := by lit_decide
  suffix := ""
  features := []
  updateCT := by exact (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    (fun _ _ _ _ hp => MdStream.AArch64.Update.agree₀ hp) (by taint_decide))
  finalizeCT := by exact (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3])
    (fun _ _ _ _ hp => MdStream.AArch64.Finalize.agree₀ hp) (by taint_decide))
  updateKeeps := instrs_keeps (by lit_decide)
  finalizeKeeps := instrs_keeps (by lit_decide)
  updateDepth := by lit_decide
  finalizeDepth := by lit_decide
  finalize224CT := by exact (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3])
    (fun _ _ _ _ hp => MdStream.AArch64.Finalize.agree₀D hp) (by taint_decide))
  finalize224Keeps := instrs_keeps (by lit_decide)
  finalize224Depth := by lit_decide
  oneShot256 := by exact (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2])
    (fun _ _ _ _ hp => MdStream.AArch64.OneShot.agree₀ hp) (by taint_decide))
  oneShot224 := by exact (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2])
    (fun _ _ _ _ hp => MdStream.AArch64.OneShot.agree₀ hp) (by taint_decide))

end VG.Proof.Sha256.AArch64.Scalar
