module

public import VerifiedGarbage.Proof.Sha512.AArch64.Variant
import VerifiedGarbage.Proof.Sha512.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.LaneCaller
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Sha512.AArch64.Variant
meta import VerifiedGarbage.Proof.Sha512.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.LaneCaller
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

@[expose] public section

namespace VG.Proof.Sha512.AArch64.Scalar

open VG.AArch64

open VG.Proof.MdStream.AArch64 (updK finK) in
open VG.Impl.Sha512.AArch64.Stream (updateWith finalizeWith) in
open VG.Impl.MdStream.AArch64 (out64) in
/-- The checks of the code of `backend`'s streaming functions, in one kernel evaluation
(`taint_decide_all`): each contains the compression function, whose analysis the kernel then
finds again where it starts from the same taint. -/
theorem backend_checks :
    (ConstantTime isa (updK (P := Stream.params) md).pre (updK (P := Stream.params) md).pub
        (updateWith "" Impl.Sha512.AArch64.compress) ∧
      ConstantTime isa (finK (P := Stream.params) md).pre (finK (P := Stream.params) md).pub
        (finalizeWith "" Impl.Sha512.AArch64.compress)) ∧
    (DigestOk (out64 6) 48 "" Impl.Sha512.AArch64.compress ∧
      DigestOk (out64 4) 32 "" Impl.Sha512.AArch64.compress ∧
      DigestOk (out64 3 ++ Impl.Sha512.AArch64.Stream.outHi 3) 28 "" Impl.Sha512.AArch64.compress) ∧
    (OneShotCT (out64 8) 64 Spec.Sha512.H0_512 "" Impl.Sha512.AArch64.compress ∧
      OneShotCT (out64 6) 48 Spec.Sha512.H0_384 "" Impl.Sha512.AArch64.compress) ∧
    OneShotCT (out64 4) 32 Spec.Sha512.H0_512_256 "" Impl.Sha512.AArch64.compress ∧
    OneShotCT (out64 3 ++ Impl.Sha512.AArch64.Stream.outHi 3) 28 Spec.Sha512.H0_512_224 ""
      Impl.Sha512.AArch64.compress := by
  refine ⟨⟨LaneTaint.constantTime (hc := ?_) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4])
        (fun _ _ _ _ hp => MdStream.AArch64.Update.agree₀ hp) ?_,
      LaneTaint.constantTime (hc := ?_) (Taint.ofRegs [.x0, .x1, .x2, .x3])
        (fun _ _ _ _ hp => MdStream.AArch64.Finalize.agree₀ hp) ?_⟩,
    ⟨⟨LaneTaint.constantTime (hc := ?_) (Taint.ofRegs [.x0, .x1, .x2, .x3])
        (fun _ _ _ _ hp => MdStream.AArch64.Finalize.agree₀D hp) ?_, ?_⟩,
      ⟨LaneTaint.constantTime (hc := ?_) (Taint.ofRegs [.x0, .x1, .x2, .x3])
        (fun _ _ _ _ hp => MdStream.AArch64.Finalize.agree₀D hp) ?_, ?_⟩,
      ⟨LaneTaint.constantTime (hc := ?_) (Taint.ofRegs [.x0, .x1, .x2, .x3])
        (fun _ _ _ _ hp => MdStream.AArch64.Finalize.agree₀D hp) ?_, ?_⟩⟩,
    ⟨LaneTaint.constantTime (hc := ?_) (Taint.ofRegs [.x0, .x1, .x2])
        (fun _ _ _ _ hp => MdStream.AArch64.OneShot.agree₀ hp) ?_,
      LaneTaint.constantTime (hc := ?_) (Taint.ofRegs [.x0, .x1, .x2])
        (fun _ _ _ _ hp => MdStream.AArch64.OneShot.agree₀ hp) ?_⟩,
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
  code := Impl.Sha512.AArch64.compress
  verified := Proof.Sha512.AArch64.compress_verified
  noFrames := by lit_decide
  keepsV := by lit_decide
  noDit := by lit_decide
  suffix := ""
  features := []
  updateCT := backend_checks.1.1
  finalizeCT := backend_checks.1.2
  updateDepth := by lit_decide
  finalizeDepth := by lit_decide
  digest384 := backend_checks.2.1.1
  digest512_256 := backend_checks.2.1.2.1
  digest512_224 := backend_checks.2.1.2.2
  oneShot512 := backend_checks.2.2.1.1
  oneShot384 := backend_checks.2.2.1.2
  oneShot512_256 := backend_checks.2.2.2.1
  oneShot512_224 := backend_checks.2.2.2.2

end VG.Proof.Sha512.AArch64.Scalar
