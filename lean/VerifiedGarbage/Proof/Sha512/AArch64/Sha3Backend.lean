module

public import VerifiedGarbage.Proof.Sha512.AArch64.Variant
meta import VerifiedGarbage.Proof.Sha512.AArch64.Variant
public import VerifiedGarbage.Proof.Sha512.AArch64.Sha3.Compress
meta import VerifiedGarbage.Proof.Sha512.AArch64.Sha3.Compress
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

@[expose] public section

namespace VG.Proof.Sha512.AArch64.Sha3

open VG.AArch64

/-- The sha3 compression backend and the checked facts its streaming callers need. -/
def backend : Compress where
  code := Impl.Sha512.AArch64.Sha3.compress
  verified := Proof.Sha512.AArch64.Sha3.compress_verified
  noFrames := by lit_decide
  keepsV := by lit_decide
  suffix := "_sha3"
  features := ["sha3"]
  updateCT := by exact (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    (fun _ _ _ _ hp => MdStream.AArch64.Update.agree₀ hp) (by taint_decide))
  finalizeCT := by exact (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3])
    (fun _ _ _ _ hp => MdStream.AArch64.Finalize.agree₀ hp) (by taint_decide))
  updateKeeps := instrs_keeps (by lit_decide)
  finalizeKeeps := instrs_keeps (by lit_decide)
  updateDepth := by lit_decide
  finalizeDepth := by lit_decide
  digest384 := by exact (⟨VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3])
      (fun _ _ _ _ hp => MdStream.AArch64.Finalize.agree₀D hp) (by taint_decide),
    instrs_keeps (by lit_decide), by lit_decide⟩)
  digest512_256 := by exact (⟨VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3])
      (fun _ _ _ _ hp => MdStream.AArch64.Finalize.agree₀D hp) (by taint_decide),
    instrs_keeps (by lit_decide), by lit_decide⟩)
  digest512_224 := by exact (⟨VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3])
      (fun _ _ _ _ hp => MdStream.AArch64.Finalize.agree₀D hp) (by taint_decide),
    instrs_keeps (by lit_decide), by lit_decide⟩)

end VG.Proof.Sha512.AArch64.Sha3
