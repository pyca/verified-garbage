module

public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.P521Joint
public import VerifiedGarbage.Impl.Ecdsa.AArch64.VerifyHash
public import VerifiedGarbage.Spec.Ecdsa.P521
public import VerifiedGarbage.Impl.Residue.AArch64.Scrub

/-! # ECDSA verification over P-521 on AArch64: nine-word field elements and scalars.

The joint public multiplication interleaves width-seven generator digits and
width-five peer digits, sharing one Jacobian doubling chain. The peer table
and cached Z powers fit within the existing scratch space. -/

@[expose] public section

namespace VG.Impl.Ecdsa.Verify.AArch64

open VG.AArch64

/-- `vg_ecdsa_p521_verify`. -/
def verifyP521 : Prog isa := P521Joint.verify

namespace Fn

/-- `vg_ecdsa_p521_verify` as emitted: `VerifyHash.verifyHash` around `verifyP521`, then
its cleanup, which clears the registers it writes that the calling convention
does not preserve, but the 32 bits of its result, and zeroes its 80 bytes of
stack (`Impl.Residue.AArch64.scrubAll`), so that it returns without secret
residue. -/
def verifyHashP521 : Prog isa :=
  Residue.AArch64.scrubAll 80 32
    ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
     [.v16, .v17, .v18, .v19, .v20, .v21, .v22, .v24, .v25, .v26, .v28, .v29],
     []⟩
    (Impl.Ecdsa.AArch64.VerifyHash.verifyHash Spec.Ecdsa.P521.inst.curve.len true verifyP521)

end Fn

end VG.Impl.Ecdsa.Verify.AArch64
