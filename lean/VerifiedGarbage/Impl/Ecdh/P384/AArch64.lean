module

public import VerifiedGarbage.Impl.Ecdh.AArch64.WindowJ
public import VerifiedGarbage.Impl.Ecdsa.P384.AArch64
public import VerifiedGarbage.Impl.P384.EcdhAllocatedCode
public import VerifiedGarbage.Impl.P384.EcdhMadd
public import VerifiedGarbage.Impl.P384.EcdhSelect
public import VerifiedGarbage.Impl.Scrub.AArch64.Scrub

/-! # ECDH over P-384 on AArch64: six-word field elements and scalars, by
windows with a Jacobian accumulator and an affine table (`Cfg.exchangeJ4`),
the window's doublings register-allocated (`Impl/P384/EcdhDouble.lean`) and its
mixed additions inline (`Impl/P384/EcdhMadd.lean`), its entries selected in
registers (`Impl/P384/EcdhSelect.lean`) -/

@[expose] public section

namespace VG.Impl.Ecdh.AArch64

open VG.AArch64

/-- `vg_ecdh_p384`. -/
def exchangeP384 : Prog isa :=
  Cfg.exchangeJ4 Impl.Ecdsa.AArch64.p384
    (some (.block Impl.P384.EcdhAllocatedCode.doubleRD, .block Impl.P384.EcdhAllocatedCode.doubleDR))
    (some (.block Impl.P384.EcdhMadd.madd)) (some Impl.P384.EcdhSelect.sel)

end VG.Impl.Ecdh.AArch64

namespace VG.Impl.Ecdh.AArch64.Fn

/-- ECDH over P-384 as emitted: its code, then the registers it writes
that the calling convention does not preserve cleared, but the 32 bits of its
result (`Impl.Scrub.AArch64.scrubAll`; it uses no stack), so that it returns
without secret residue. -/
def exchangeP384 : Prog VG.AArch64.isa :=
  VG.Impl.Scrub.AArch64.scrubAll 0 32
    ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
     [.v16, .v17, .v18, .v19, .v28, .v29],
     []⟩
    VG.Impl.Ecdh.AArch64.exchangeP384

end VG.Impl.Ecdh.AArch64.Fn
