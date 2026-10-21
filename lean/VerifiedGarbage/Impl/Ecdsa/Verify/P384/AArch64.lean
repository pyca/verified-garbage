module

public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.P384Joint

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

end VG.Impl.Ecdsa.Verify.AArch64
