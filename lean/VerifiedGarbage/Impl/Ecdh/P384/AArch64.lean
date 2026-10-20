module

public import VerifiedGarbage.Impl.Ecdh.AArch64.WindowJ
public import VerifiedGarbage.Impl.Ecdsa.P384.AArch64
public import VerifiedGarbage.Impl.P384.EcdhAllocatedCode
public import VerifiedGarbage.Impl.P384.EcdhMadd

/-! # ECDH over P-384 on AArch64: six-word field elements and scalars, by
windows with a Jacobian accumulator and an affine table (`Cfg.exchangeJ4`),
the window's doublings register-allocated (`Impl/P384/EcdhDouble.lean`) and its
mixed additions inline (`Impl/P384/EcdhMadd.lean`) -/

@[expose] public section

namespace VG.Impl.Ecdh.AArch64

open VG.AArch64

/-- `vg_ecdh_p384`. -/
def exchangeP384 : Prog isa :=
  Cfg.exchangeJ4 Impl.Ecdsa.AArch64.p384
    (some (.block Impl.P384.EcdhAllocatedCode.doubleRD, .block Impl.P384.EcdhAllocatedCode.doubleDR))
    (some (.block Impl.P384.EcdhMadd.madd))

end VG.Impl.Ecdh.AArch64
