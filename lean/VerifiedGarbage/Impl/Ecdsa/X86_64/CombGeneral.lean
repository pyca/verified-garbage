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
  comb, with `3 b R mod p` for each addition, calls of
  `vg_<curve>_add_complete` (`Cfg.addCompleteFn`).
* `signG d`: `Cfg.sign` with the table of `k`'s bits made inline and `[k]G`
  by a call of `gMulG d`, `vg_<curve>_comb_g` (`gMulGC`), which verification
  calls too (`signGW` with any code for `[k]G`).

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
    ((c.combCfgG d).generalComb (c.mont (3 * c.C.b)) c.addCompleteFn)

/-- The name of the comb's function, `vg_<curve>_comb_g`: `R = [k]G` from
the table of `k`'s bits (`gMulG`), which the signature and the
verification call. -/
def combGFn : String :=
  match c.mul with
  | some C => s!"vg_{C.curve}_comb_g"
  | none => "vg_comb_g"

/-- `gMulG d`, as the call of its function (`combGFn`). -/
def gMulGC (d : CombData) : Prog isa := .call c.combGFn (c.gMulG d)

/-- `vg_ecdsa_<curve>_sign` with `[k]G` by `gm`. -/
def signGW (gm : Prog isa) : Prog isa :=
  .seq (.block c.setup) <|
  .seq (c.kBitsIf false) <|
  .seq (bits (c.sl EXPP) (bitsAt c.n 1) (8 * c.n)) <|
  .seq (bits (c.sl EXPN) (bitsAt c.n 2) (8 * c.n)) <|
  .seq gm <|
  .seq c.pPow <|
  .seq c.middle <|
  .seq c.nPow c.scalar

/-- `vg_ecdsa_<curve>_sign` with `[k]G` by a call of `gMulG d` (`gMulGC`). -/
def signG (d : CombData) : Prog isa := c.signGW (c.gMulGC d)

end VG.Impl.Ecdsa.X86_64.Cfg
