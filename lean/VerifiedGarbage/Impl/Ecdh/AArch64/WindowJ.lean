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

/-- `d + offset J` and its bits, then `[d]P` into `R` by `windowJ`, its
doublings `dd`'s blocks if given, its mixed additions `ma`'s. -/
def mulJ4 (dd : Option (Prog isa × Prog isa) := none) (ma : Option (Prog isa) := none) : Prog isa :=
  .seq (c.winPrep (c.sl K)) (WinCfg.windowJ (c.winCfg PX PY) (invJ c) c.padd dd ma)

/-- `vg_ecdh_<curve>` by windows with a Jacobian accumulator and an affine
table, for a curve of prime order. -/
def exchangeJ4 (dd : Option (Prog isa × Prog isa) := none) (ma : Option (Prog isa) := none) : Prog isa :=
  exchangeWith c (mulJ4 c dd ma)

end VG.Impl.Ecdh.AArch64.Cfg
