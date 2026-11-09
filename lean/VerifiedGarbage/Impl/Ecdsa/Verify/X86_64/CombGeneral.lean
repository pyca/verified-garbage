module

public import VerifiedGarbage.Impl.Ecdsa.Verify.X86_64
public import VerifiedGarbage.Impl.Ecdsa.X86_64.CombGeneral
public import VerifiedGarbage.Impl.Weierstrass.X86_64.WindowGeneral

/-!
# ECDSA verification on x86-64 with a comb for any `a`

`Cfg.verify` with `[u]G` by the fixed-base comb whose additions are the
complete ones for any `a` (`Cfg.gMulG`), for a curve whose `a` is not `-3`
(so that `Cfg.comb`, whose additions are for `a = -3`, is none), rather than
by a call of `vg_<curve>_mul`:

* `mulVA`: `[v]Q` by ECDH's windows for any `a` (`WinCfg.windowA`: signed
  4-bit windows, the Jacobian doubling and the complete addition for any
  `a`, with `3 b R mod p` from the setup's `B3P`), where `mulV` has the
  ladder for a curve whose `a` is not `-3`; `v` is public, but the windows
  run in constant time all the same;
* `pointsG d`: the table of `u`'s bits, `[u]G` by `gMulG d` from `d`'s
  tables, saved to `U` and `R` reset to `O`; then `[v]Q` by `mulVA`, and
  `[u]G + [v]Q` by the complete addition, into `R`: `Cfg.points` with
  `gMulG d` in place of `gMul` and `mulVA` in place of `mulV`.
* `verifyG d`: `Cfg.verify` with the points by `pointsG d`.

The comb's tables are the static `d.tsym`, which the configuration declares
as its `gtab` (whose tables `Cfg.combConsts` lists). Its entries are scanned
in constant time, as the signature's are, though `u` is public.
-/

@[expose] public section

namespace VG.Impl.Ecdsa.Verify.X86_64

open VG.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass VG.Impl.Ecdsa.X86_64

namespace Cfg

variable (c : Impl.Ecdsa.X86_64.Cfg)

/-- `[v]Q`, into `R`, by the window method for any `a`: `v + offset J` and its
bits (`winPrep`), then `windowA` on `Q` (at ECDH's `PX`, `PY`), with
`3 b R mod p` (`B3P`) for its complete additions. -/
def mulVA : Prog isa :=
  .seq (c.winPrep (c.sl V)) (WinCfg.windowA (c.winCfg Impl.Ecdh.X86_64.PX Impl.Ecdh.X86_64.PY B3P))

/-- `[u]G + [v]Q`, into `R`, from `u` and `v`, `[u]G` by the comb of `d` and
`[v]Q` by `mulVA`. -/
def pointsG (d : CombData) : Prog isa :=
  .seq (bits (c.sl U) (bitsAt c.n 0) (8 * c.n)) <| .seq (c.gMulG d) <| .seq (.block (save c)) <|
  .seq (mulVA c) (sum c)

/-- Everything after the checks of the key, the points by `pointsG d`. -/
def backG (d : CombData) : Prog isa :=
  .seq (scalars c) <| .seq c.nPow <| .seq (uv c) <| .seq (pointsG c d) (tail c)

/-- `vg_ecdsa_<curve>_verify`, `[u]G` by the comb of `d`. -/
def verifyG (d : CombData) : Prog isa :=
  .seq (.block (args c)) <| .seq (Impl.Ecdh.X86_64.Cfg.prefix' c (some D)) <| .seq (.block (loadS c)) <|
  .seq (.block (Impl.Ecdh.X86_64.Cfg.peer c)) <| .seq (Impl.Ecdh.X86_64.Cfg.check c) (backG c d)

end Cfg

end VG.Impl.Ecdsa.Verify.X86_64
