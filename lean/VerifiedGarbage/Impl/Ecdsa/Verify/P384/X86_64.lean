module

public import VerifiedGarbage.Impl.Ecdsa.Verify.X86_64.Joint
public import VerifiedGarbage.Impl.P384.X86_64.Joint

/-! # ECDSA verification over P-384 on x86-64: six-word field elements and scalars

By the public joint method (`Cfg.jointVerify`), with the doubler of any
number of words (`Joint.jacDouble`). -/

@[expose] public section

namespace VG.Impl.Ecdsa.Verify.X86_64
open VG.X86_64 VG.Impl.P384.X86_64 VG.Impl.Weierstrass.X86_64

/-- `vg_ecdsa_p384_verify`. -/
def jointVerifyP384 : Prog isa := Cfg.jointVerify p384v publicJoint (Joint.jacDouble publicJoint.K)

/-- `vg_ecdsa_p384_verify_adx`. -/
def jointVerifyP384Adx : Prog isa :=
  Cfg.jointVerify p384vx publicJointAdx (Joint.jacDouble publicJointAdx.K)

end VG.Impl.Ecdsa.Verify.X86_64
