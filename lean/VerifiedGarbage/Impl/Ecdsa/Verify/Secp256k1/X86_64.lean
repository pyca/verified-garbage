module

public import VerifiedGarbage.Impl.Ecdsa.Verify.X86_64.Joint
public import VerifiedGarbage.Impl.Secp256k1.X86_64.Joint

/-! # ECDSA verification over secp256k1 on x86-64: four-word field elements and scalars

By the public joint method (`Cfg.jointVerify`), its doublings and additions
calls of `vg_secp256k1_jac_double`, `vg_secp256k1_jac_add_cached` and
`vg_secp256k1_jac_add_affine` (for `a = 0`). -/

@[expose] public section

namespace VG.Impl.Ecdsa.Verify.X86_64
open VG.X86_64 VG.Impl.Secp256k1.X86_64 VG.Impl.Weierstrass.X86_64

/-- `vg_ecdsa_secp256k1_verify`. -/
def verifySecp256k1 : Prog isa := Cfg.jointVerify secp256k1v publicJoint (jointDouble publicJoint.K)

end VG.Impl.Ecdsa.Verify.X86_64
