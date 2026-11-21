module

public import VerifiedGarbage.Impl.Ecdh.AArch64
public import VerifiedGarbage.Impl.Ecdsa.P224.AArch64
public import VerifiedGarbage.Impl.Scrub.AArch64.Scrub

/-! # ECDH over P-224 on AArch64: four-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdh.AArch64

open VG.AArch64

/-- `vg_ecdh_p224`. -/
def exchangeP224 : Prog isa := Cfg.exchange Impl.Ecdsa.AArch64.p224

end VG.Impl.Ecdh.AArch64

namespace VG.Impl.Ecdh.AArch64.Fn

/-- ECDH over P-224 as emitted: its code, then the registers it writes
that the calling convention does not preserve cleared, but the 32 bits of its
result (`Impl.Scrub.AArch64.scrubAll`; it uses no stack), so that it returns
without secret residue. -/
def exchangeP224 : Prog VG.AArch64.isa :=
  VG.Impl.Scrub.AArch64.scrubAll 0 32
    ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x16, .x17],
     [.v28, .v29],
     []⟩
    VG.Impl.Ecdh.AArch64.exchangeP224

end VG.Impl.Ecdh.AArch64.Fn
