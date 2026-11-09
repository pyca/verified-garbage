module

public import VerifiedGarbage.Impl.Ecdsa.X86_64
public import VerifiedGarbage.Impl.Weierstrass.X86_64.TCombGeneral

/-!
# ECDSA's signature on x86-64 with a comb for any `a`

`Cfg.sign` with `[k]G` by the fixed-base comb whose additions are the complete
ones for any `a` (`TCombCfg.generalComb`), for a curve whose `a` is not `-3`
(so that `Cfg.comb`, whose additions are for `a = -3`, is none):

* `combCfgG d`: `Cfg.combCfg d`, but with `a R mod p` (`AP`, a constant of the
  setup) in its addition's `a`; `b R mod p` stays in `EM`.
* `gMulG d`: `b R mod p` to `EM`, as `Cfg.gMul` does before its comb, then the
  comb, with `3 b R mod p` for each addition.
* `signG d`: `Cfg.sign` with the table of `k`'s bits made inline and `[k]G`
  by `gMulG d`.

The comb's tables are the static `d.tsym`, which the configuration declares
as its `gtab` (whose tables `Cfg.combConsts` lists).
-/

@[expose] public section

namespace VG.Impl.Ecdsa.X86_64.Cfg

open VG.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass

variable (c : Cfg)

/-- The comb for `[k]G` from `d`'s tables, its addition's `a` the constant
`a R mod p`. -/
def combCfgG (d : CombData) : TCombCfg :=
  { c.combCfg d with S := { c.rcbSlots with b3 := c.sl EM } }

/-- `R = [k]G`, from the table of `k`'s bits, by the comb of `combCfgG d`. -/
def gMulG (d : CombData) : Prog isa :=
  .seq (.block (setConst c.n (c.sl EM) (c.mont c.C.b)))
    ((c.combCfgG d).generalComb (c.mont (3 * c.C.b)))

/-- `vg_ecdsa_<curve>_sign` with `[k]G` by `gMulG d`. -/
def signG (d : CombData) : Prog isa :=
  .seq (.block c.setup) <|
  .seq (c.kBitsIf false) <|
  .seq (bits (c.sl EXPP) (bitsAt c.n 1) (8 * c.n)) <|
  .seq (bits (c.sl EXPN) (bitsAt c.n 2) (8 * c.n)) <|
  .seq (c.gMulG d) <|
  .seq c.pPow <|
  .seq c.middle <|
  .seq c.nPow c.scalar

end VG.Impl.Ecdsa.X86_64.Cfg
