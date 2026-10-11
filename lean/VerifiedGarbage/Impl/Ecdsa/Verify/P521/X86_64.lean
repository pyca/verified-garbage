module

public import VerifiedGarbage.Impl.Ecdsa.Verify.X86_64.Joint
public import VerifiedGarbage.Impl.P521.X86_64.Joint

/-! # ECDSA verification over P-521 on x86-64: nine-word field elements and scalars

By the public joint method (`Cfg.jointVerify`), with the doubler of any
number of words (`Joint.jacDouble`). -/

@[expose] public section

namespace VG.Impl.Ecdsa.Verify.X86_64
open VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.P521.X86_64 VG.Impl.Weierstrass.X86_64

/-- `vg_ecdsa_p521_verify`. -/
def jointVerifyP521 : Prog isa := Cfg.jointVerify p521 publicJoint (Joint.jacDouble publicJoint.K)

/-- `vg_ecdsa_p521_verify_adx`. -/
def jointVerifyP521Adx : Prog isa :=
  Cfg.jointVerify p521x publicJointAdx (Joint.jacDouble publicJointAdx.K)

end VG.Impl.Ecdsa.Verify.X86_64
