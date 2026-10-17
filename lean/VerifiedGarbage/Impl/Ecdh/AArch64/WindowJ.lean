module

public import VerifiedGarbage.Impl.Ecdh.AArch64.WithMul
public import VerifiedGarbage.Impl.Weierstrass.AArch64.WindowJ

/-!
# ECDH on AArch64 by windows in Jacobian coordinates

`exchange`, but `[d]P` by `WinCfg.windowJ` (`Impl/Weierstrass/AArch64/WindowJ.lean`):
the window method's table made affine by one inversion, and `R` kept in
Jacobian coordinates from one window to the next, the entries added by the
mixed addition, for a curve of prime order.
-/

@[expose] public section

namespace VG.Impl.Ecdh.AArch64.Cfg

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64

variable (c : Impl.Ecdsa.AArch64.Cfg)

/-- The inversion of `windowJ`'s table: `R.z^(p-2)` into `ACC` by the
signature's power (`pPow`), then into the selected entry's `x`. -/
def invJ : Prog isa := .seq c.pPow (.block (copy c.n (c.sl TX) (c.sl ACC)))

/-- `d + offset J` and its bits, then `[d]P` into `R` by `windowJ`. -/
def mulJ4 : Prog isa :=
  .seq (c.winPrep (c.sl K)) (WinCfg.windowJ (c.winCfg PX PY) (invJ c) c.padd)

/-- `vg_ecdh_<curve>` by windows with a Jacobian accumulator and an affine
table, for a curve of prime order. -/
def exchangeJ4 : Prog isa := exchangeWith c (mulJ4 c)

end VG.Impl.Ecdh.AArch64.Cfg
