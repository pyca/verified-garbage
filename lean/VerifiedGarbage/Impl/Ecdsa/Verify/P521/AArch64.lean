module

public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.P521Joint

/-! # ECDSA verification over P-521 on AArch64: nine-word field elements and scalars.

The joint public multiplication interleaves width-seven generator digits and
width-five peer digits, sharing one Jacobian doubling chain. The peer table
and cached Z powers fit within the existing scratch space. -/

@[expose] public section

namespace VG.Impl.Ecdsa.Verify.AArch64

open VG.AArch64

/-- `vg_ecdsa_p521_verify`. -/
def verifyP521 : Prog isa := P521Joint.verify

end VG.Impl.Ecdsa.Verify.AArch64
