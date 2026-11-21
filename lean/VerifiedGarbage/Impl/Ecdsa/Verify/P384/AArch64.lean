module

public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.P384Joint
public import VerifiedGarbage.Impl.Ecdsa.AArch64.VerifyHash
public import VerifiedGarbage.Spec.Ecdsa.P384
public import VerifiedGarbage.Impl.Scrub.AArch64.Scrub

/-! # ECDSA verification over P-384 on AArch64: six-word field elements and scalars

`[u]G + [v]Q` by one loop (`P384Joint`): the public width-five NAF of `v` and the width-nine NAF
of `u` share their doublings (the register-allocated ones of ECDH's window,
`Impl/P384/EcdhDouble.lean`, which has the same slots), `u`'s digits reading `[m]G` from the
static `VG_P384_GTAB`. -/

@[expose] public section

namespace VG.Impl.Ecdsa.Verify.AArch64

open VG.AArch64

/-- `vg_ecdsa_p384_verify`. -/
def verifyP384 : Prog isa := P384Joint.verify

namespace Fn

/-- `vg_ecdsa_p384_verify` as emitted: `VerifyHash.verifyHash` around `verifyP384`, then
its cleanup, which clears the registers it writes that the calling convention
does not preserve, but the 32 bits of its result, and zeroes its 80 bytes of
stack (`Impl.Scrub.AArch64.scrubAll`), so that it returns without secret
residue. -/
def verifyHashP384 : Prog isa :=
  Scrub.AArch64.scrubAll 80 32
    ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
     [.v16, .v17, .v18, .v19, .v28, .v29],
     []⟩
    (Impl.Ecdsa.AArch64.VerifyHash.verifyHash Spec.Ecdsa.P384.inst.curve.len false verifyP384)

end Fn

end VG.Impl.Ecdsa.Verify.AArch64
