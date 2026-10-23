module

public import VerifiedGarbage.Impl.Rsa.X86.GcdDispatch
public import VerifiedGarbage.Impl.Rsa.X86.RecoverRt
public import VerifiedGarbage.Proof.Rsa.X86.RvTaint
public import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Impl.Rsa.X86.GcdDispatch
meta import VerifiedGarbage.Impl.Rsa.X86.RecoverRt
meta import VerifiedGarbage.Proof.Rsa.X86.RvTaint
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint

/-! # Public-argument checks surrounding batched recovery GCD -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86

theorem batchChoice256Check : (VG.Taint.check sseTaint τA (.block (VG.Impl.Rsa.X86.GcdBatch.choice 256))
    (VG.Taint.hintOf sseTaint τA (.block (VG.Impl.Rsa.X86.GcdBatch.choice 256)))).isSome=true := by
  taint_decide

theorem batchChoice384Check : (VG.Taint.check sseTaint τA (.block (VG.Impl.Rsa.X86.GcdBatch.choice 384))
    (VG.Taint.hintOf sseTaint τA (.block (VG.Impl.Rsa.X86.GcdBatch.choice 384)))).isSome=true := by
  taint_decide

theorem batchChoice512Check : (VG.Taint.check sseTaint τA (.block (VG.Impl.Rsa.X86.GcdBatch.choice 512))
    (VG.Taint.hintOf sseTaint τA (.block (VG.Impl.Rsa.X86.GcdBatch.choice 512)))).isSome=true := by
  taint_decide

theorem scalarGcdCheck : (VG.Taint.check sseTaint τA (VG.Impl.Rsa.X86.KeyRt.gcd VG.Impl.Rsa.X86.RecoverRt.nar)
    (VG.Taint.hintOf sseTaint τA (VG.Impl.Rsa.X86.KeyRt.gcd VG.Impl.Rsa.X86.RecoverRt.nar))).isSome=true := by
  taint_decide

theorem gcdSetCheck : (VG.Taint.check sseTaint τA (VG.Impl.Rsa.X86.RecoverRt.gcdSet)
    (VG.Taint.hintOf sseTaint τA (VG.Impl.Rsa.X86.RecoverRt.gcdSet))).isSome=true := by
  taint_decide

theorem factorTailCheck : (VG.Taint.check sseTaint τA (VG.Impl.Rsa.X86.Keys.seqs [VG.Impl.Rsa.X86.RecoverRt.divSet, VG.Impl.Rsa.X86.KeyRt.div VG.Impl.Rsa.X86.RecoverRt.nar VG.Impl.Rsa.X86.Recover.aQ VG.Impl.Rsa.X86.Recover.aRm VG.Impl.Rsa.X86.Recover.aDv VG.Impl.Rsa.X86.Recover.aDt, VG.Impl.Rsa.X86.RecoverRt.order])
    (VG.Taint.hintOf sseTaint τA (VG.Impl.Rsa.X86.Keys.seqs [VG.Impl.Rsa.X86.RecoverRt.divSet, VG.Impl.Rsa.X86.KeyRt.div VG.Impl.Rsa.X86.RecoverRt.nar VG.Impl.Rsa.X86.Recover.aQ VG.Impl.Rsa.X86.Recover.aRm VG.Impl.Rsa.X86.Recover.aDv VG.Impl.Rsa.X86.Recover.aDt, VG.Impl.Rsa.X86.RecoverRt.order]))).isSome=true := by
  taint_decide

end VG.Proof.Rsa.X86.Recover
