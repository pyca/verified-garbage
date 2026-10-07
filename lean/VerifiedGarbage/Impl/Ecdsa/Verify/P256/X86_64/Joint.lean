import VerifiedGarbage.Impl.Ecdsa.Verify.X86_64.Joint

namespace VG.Impl.Ecdsa.Verify.X86_64
open VG.X86_64 VG.Impl.P256.X86_64 VG.Impl.Ecdsa.X86_64

def jointVerifyP256 : Prog isa := Cfg.jointVerify p256 publicJoint

def jointVerifyP256Adx : Prog isa := Cfg.jointVerify p256x publicJointAdx

end VG.Impl.Ecdsa.Verify.X86_64
