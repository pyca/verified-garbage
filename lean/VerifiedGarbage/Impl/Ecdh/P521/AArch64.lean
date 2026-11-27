module

public import VerifiedGarbage.Impl.Ecdh.P521.AArch64.Window
public import VerifiedGarbage.Impl.Ecdsa.P521.AArch64
public import VerifiedGarbage.Impl.Scrub.AArch64.Scrub

/-! # ECDH over P-521 on AArch64: nine-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdh.AArch64

open VG.AArch64

/-- `vg_ecdh_p521`. -/
def exchangeP521 : Prog isa := P521Window.code

end VG.Impl.Ecdh.AArch64

namespace VG.Impl.Ecdh.AArch64.Fn

/-- ECDH over P-521 as emitted: its code, then the registers it writes
that the calling convention does not preserve cleared, but the 32 bits of its
result (`Impl.Scrub.AArch64.scrubAll`; it uses no stack), so that it returns
without secret residue. -/
def exchangeP521 : Prog VG.AArch64.isa :=
  VG.Impl.Scrub.AArch64.scrubAll 0 32
    ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
     [.v16, .v17, .v18, .v19, .v20, .v21, .v22, .v24, .v25, .v26, .v28, .v29, .v31],
     []⟩
    VG.Impl.Ecdh.AArch64.exchangeP521

end VG.Impl.Ecdh.AArch64.Fn
