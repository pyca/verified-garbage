module

public import VerifiedGarbage.Proof.Sm3.AArch64.Stream.Md
public import VerifiedGarbage.Proof.Sm3.AArch64.Compress
import VerifiedGarbage.Proof.Sm3.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Sm3.AArch64.Stream.Md
meta import VerifiedGarbage.Proof.Sm3.AArch64.Compress
meta import VerifiedGarbage.Proof.Sm3.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # SM3's compression function on AArch64: the implementation for the baseline ISA -/

@[expose] public section

namespace VG.Proof.Sm3.AArch64.Scalar

open VG.AArch64

/-- The compression function of the baseline ISA, and the checked facts its
streaming callers need. -/
def backend : Compress where
  name := "vg_sm3_compress"
  code := Impl.Sm3.AArch64.compress
  verified := Proof.Sm3.AArch64.compress_verified
  noFrames := by lit_decide
  keepsV := by lit_decide
  suffix := ""
  updateCT := by exact (VG.Taint.constantTime (A := taint) (c := Impl.Sm3.AArch64.Stream.update)
    (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    (fun _ _ _ _ hp => MdStream.AArch64.Update.agree₀ hp) (by taint_decide))
  finalizeCT := by exact (VG.Taint.constantTime (A := taint) (c := Impl.Sm3.AArch64.Stream.finalize)
    (Taint.ofRegs [.x0, .x1, .x2, .x3])
    (fun _ _ _ _ hp => MdStream.AArch64.Finalize.agree₀ hp) (by taint_decide))
  updateDepth := by lit_decide
  finalizeDepth := by lit_decide

end VG.Proof.Sm3.AArch64.Scalar
