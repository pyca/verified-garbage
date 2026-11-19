module

public import VerifiedGarbage.Proof.Sha256.AArch64.Variant
public import VerifiedGarbage.Proof.Sha256.AArch64.Sha2.Compress
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sha256.AArch64.Sha2.Lit
meta import VerifiedGarbage.Proof.Sha256.AArch64.Variant
meta import VerifiedGarbage.Proof.Sha256.AArch64.Sha2.Compress
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Sha256.AArch64.Sha2.Lit
public import VerifiedGarbage.Proof.Sha256.AArch64.Compress
import VerifiedGarbage.Proof.Sha256.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.LaneCaller
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Sha256.AArch64.Compress
meta import VerifiedGarbage.Proof.Sha256.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.LaneCaller
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-! ### `Sha256.AArch64.ScalarBackend`, which the modules that import this one used -/

section

@[expose] public section

namespace VG.Proof.Sha256.AArch64.Scalar

open VG.AArch64

open VG.Proof.MdStream.AArch64 (updK finK finKD) in
open VG.Impl.MdStream.AArch64 (update finalize out32) in
/-- The checks of the code of `backend`'s streaming functions, in one kernel evaluation
(`taint_decide_all`): each contains the compression function, whose analysis the kernel then
finds again where it starts from the same taint. -/
theorem backend_checks :
    (ConstantTime isa (updK (P := Stream.params) md).pre (updK (P := Stream.params) md).pub
        (update Stream.params "vg_sha256_compress" Impl.Sha256.AArch64.compress) ∧
      ConstantTime isa (finK (P := Stream.params) md).pre (finK (P := Stream.params) md).pub
        (finalize Stream.params "vg_sha256_compress" Impl.Sha256.AArch64.compress)) ∧
    ConstantTime isa (finKD (P := Impl.Sha256.AArch64.Stream.params224) md 28).pre
      (finKD (P := Impl.Sha256.AArch64.Stream.params224) md 28).pub
      (finalize Impl.Sha256.AArch64.Stream.params224 "vg_sha256_compress" Impl.Sha256.AArch64.compress) ∧
    OneShotCT Impl.Sha256.AArch64.Stream.out256 32 Spec.Sha256.H0 "vg_sha256_compress"
      Impl.Sha256.AArch64.compress ∧
    OneShotCT (out32 7 true) 28 Spec.Sha256.H0_224 "vg_sha256_compress" Impl.Sha256.AArch64.compress := by
  refine ⟨⟨LaneTaint.constantTime (hc := ?_) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4])
        (fun _ _ _ _ hp => MdStream.AArch64.Update.agree₀ hp) ?_,
      LaneTaint.constantTime (hc := ?_) (Taint.ofRegs [.x0, .x1, .x2, .x3])
        (fun _ _ _ _ hp => MdStream.AArch64.Finalize.agree₀ hp) ?_⟩,
    LaneTaint.constantTime (hc := ?_) (Taint.ofRegs [.x0, .x1, .x2, .x3])
      (fun _ _ _ _ hp => MdStream.AArch64.Finalize.agree₀D hp) ?_,
    LaneTaint.constantTime (hc := ?_) (Taint.ofRegs [.x0, .x1, .x2])
      (fun _ _ _ _ hp => MdStream.AArch64.OneShot.agree₀ hp) ?_,
    LaneTaint.constantTime (hc := ?_) (Taint.ofRegs [.x0, .x1, .x2])
      (fun _ _ _ _ hp => MdStream.AArch64.OneShot.agree₀ hp) ?_⟩
  taint_decide_all

/-- The scalar compression backend and the checked facts its streaming callers
need. Its code keeps the pointers, the count and the callee-saved registers
in lanes of vector registers, so the analyses are those that follow the
lanes (`LaneTaint`). -/
def backend : Compress where
  name := "vg_sha256_compress"
  code := Impl.Sha256.AArch64.compress
  verified := Proof.Sha256.AArch64.compress_verified
  noFrames := by lit_decide
  keepsV := by lit_decide
  noDit := by lit_decide
  suffix := ""
  features := []
  clear := ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
    [.v16, .v17, .v18, .v19, .v20, .v21, .v22], []⟩
  updateCT := backend_checks.1.1
  finalizeCT := backend_checks.1.2
  updateDepth := by lit_decide
  finalizeDepth := by lit_decide
  finalize224CT := backend_checks.2.1
  finalize224Depth := by lit_decide
  oneShot256 := backend_checks.2.2.1
  oneShot224 := backend_checks.2.2.2

end VG.Proof.Sha256.AArch64.Scalar

end

end

@[expose] public section

namespace VG.Proof.Sha256.AArch64.Sha2

open VG.AArch64

/-- The sha2 compression backend and the checked facts its streaming callers need. -/
def backend : Compress where
  name := "vg_sha256_compress_sha2"
  code := Impl.Sha256.AArch64.Sha2.compress
  verified := Proof.Sha256.AArch64.Sha2.compress_verified
  noFrames := by lit_decide
  keepsV := by lit_decide
  noDit := by lit_decide
  suffix := "_sha2"
  features := ["sha2"]
  clear := ⟨[.x1, .x2, .x4],
    [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26,
     .v27, .v28, .v29, .v30, .v31],
    []⟩
  updateCT := by exact (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    (fun _ _ _ _ hp => MdStream.AArch64.Update.agree₀ hp) (by taint_decide))
  finalizeCT := by exact (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3])
    (fun _ _ _ _ hp => MdStream.AArch64.Finalize.agree₀ hp) (by taint_decide))
  updateDepth := by lit_decide
  finalizeDepth := by lit_decide
  finalize224CT := by exact (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3])
    (fun _ _ _ _ hp => MdStream.AArch64.Finalize.agree₀D hp) (by taint_decide))
  finalize224Depth := by lit_decide
  oneShot256 := by exact (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2])
    (fun _ _ _ _ hp => MdStream.AArch64.OneShot.agree₀ hp) (by taint_decide))
  oneShot224 := by exact (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2])
    (fun _ _ _ _ hp => MdStream.AArch64.OneShot.agree₀ hp) (by taint_decide))

end VG.Proof.Sha256.AArch64.Sha2
