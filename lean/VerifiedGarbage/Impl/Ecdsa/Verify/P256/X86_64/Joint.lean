module

public import VerifiedGarbage.Impl.Ecdsa.Verify.X86_64.Joint
public import VerifiedGarbage.Impl.P256.X86_64.Joint

@[expose] public section

namespace VG.Impl.Ecdsa.Verify.X86_64
open VG.X86_64 VG.Impl.P256.X86_64 VG.Impl.Ecdsa.X86_64

def jointVerifyP256 : Prog isa := Cfg.jointVerify p256 publicJoint (jointDouble publicJoint.K)

def jointVerifyP256Adx : Prog isa := Cfg.jointVerify p256x publicJointAdx (jointDouble publicJointAdx.K)

end VG.Impl.Ecdsa.Verify.X86_64
