module

public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64
public import VerifiedGarbage.Impl.Ecdsa.P224.AArch64
public import VerifiedGarbage.Impl.Ecdsa.AArch64.VerifyHash
public import VerifiedGarbage.Spec.Ecdsa.P224
public import VerifiedGarbage.Impl.Scrub.AArch64.Scrub

/-! # ECDSA verification over P-224 on AArch64: four-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdsa.Verify.AArch64

open VG.AArch64

/-- `vg_ecdsa_p224_verify`. -/
def verifyP224 : Prog isa := Cfg.verify Impl.Ecdsa.AArch64.p224

namespace Fn

/-- `vg_ecdsa_p224_verify` as emitted: `VerifyHash.verifyHash` around `verifyP224`, then
its cleanup, which clears the registers it writes that the calling convention
does not preserve, but the 32 bits of its result, and zeroes its 80 bytes of
stack (`Impl.Scrub.AArch64.scrubAll`), so that it returns without secret
residue. -/
def verifyHashP224 : Prog isa :=
  Scrub.AArch64.scrubAll 80 32
    ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x16, .x17],
     [.v28, .v29],
     []⟩
    (Impl.Ecdsa.AArch64.VerifyHash.verifyHash Spec.Ecdsa.P224.inst.curve.len false verifyP224)

end Fn

end VG.Impl.Ecdsa.Verify.AArch64
