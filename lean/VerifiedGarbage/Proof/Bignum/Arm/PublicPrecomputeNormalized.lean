module

public import VerifiedGarbage.Proof.Bignum.Arm.PublicPrecomputeKernel
public import VerifiedGarbage.Impl.Bignum.Arm.R2Normalized
import VerifiedGarbage.Proof.Bignum.Arm.R2Public
import VerifiedGarbage.Proof.Bignum.Arm.R2PublicCT
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputePublicCT

/-! Public normalized setup supplies the same kernel interface as the original setup. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

def normalizedPublicPrecomputeKernel : PublicPrecomputeKernel where
  code := precomputeWith r2Public
  correct := by exact precomputeWith_ok ⟨r2Public, r2Public_ok⟩
  ct := by exact precomputePublic_ct ⟨r2Public, r2Public_ok⟩ r2Public_ct

end VG.Proof.Bignum.Arm
