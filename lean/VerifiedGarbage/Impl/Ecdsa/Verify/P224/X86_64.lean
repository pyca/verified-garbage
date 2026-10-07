import VerifiedGarbage.Impl.Ecdsa.Verify.X86_64.Joint
import VerifiedGarbage.Impl.P224.X86_64.Joint

/-! # ECDSA verification over P-224 on x86-64: four-word field elements and scalars

By the public joint method (`Cfg.jointVerify`), with the doubler of any
number of words (`Joint.jacDouble`). -/

namespace VG.Impl.Ecdsa.Verify.X86_64
open VG.X86_64 VG.Impl.P224.X86_64 VG.Impl.Weierstrass.X86_64

/-- `vg_ecdsa_p224_verify`. -/
def jointVerifyP224 : Prog isa := Cfg.jointVerify p224v publicJoint (Joint.jacDouble publicJoint.K)

end VG.Impl.Ecdsa.Verify.X86_64
