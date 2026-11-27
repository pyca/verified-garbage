module

public import VerifiedGarbage.Impl.Weierstrass.X86_64.PointOps
public import VerifiedGarbage.Impl.Ecdsa.Verify.X86_64.Joint
public import VerifiedGarbage.Impl.P256.X86_64.Joint

@[expose] public section

namespace VG.Impl.Ecdsa.Verify.X86_64
open VG.X86_64 VG.Impl.P256.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Weierstrass.X86_64

/-- The cached and affine additions share their original ending, in one leaf. -/
def jointVerifyP256 : Prog isa :=
  Cfg.jointVerify p256v publicJoint (jointDouble publicJoint.K)
    (.call "vg_p256_jac_add_tail" (PointOps.tailBody publicJoint.K publicJoint.dbl))

def jointVerifyP256Adx : Prog isa :=
  Cfg.jointVerify p256vx publicJointAdx (jointDouble publicJointAdx.K)
    (.call "vg_p256_jac_add_tail_adx" (PointOps.tailBody publicJointAdx.K publicJointAdx.dbl))

end VG.Impl.Ecdsa.Verify.X86_64
