module

public import VerifiedGarbage.Impl.Ecdsa.Verify.X86_64
public import VerifiedGarbage.Impl.Ecdsa.X86_64.CombGeneral

/-!
# ECDSA verification on x86-64 with a comb for any `a`

`Cfg.verify` with `[u]G` by the fixed-base comb whose additions are the
complete ones for any `a` (`Cfg.gMulG`), for a curve whose `a` is not `-3`
(so that `Cfg.comb`, whose additions are for `a = -3`, is none), rather than
by a call of `vg_<curve>_mul`:

* `pointsG d`: the table of `u`'s bits, `[u]G` by `gMulG d` from `d`'s
  tables, saved to `U` and `R` reset to `O`; then `[v]Q` by `mulV` (the
  ladder, for a curve without windows), and `[u]G + [v]Q` by the complete
  addition, into `R`: `Cfg.points` with `gMulG d` in place of `gMul`.
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

/-- `[u]G + [v]Q`, into `R`, from `u` and `v`, `[u]G` by the comb of `d`. -/
def pointsG (d : CombData) : Prog isa :=
  .seq (bits (c.sl U) (bitsAt c.n 0) (8 * c.n)) <| .seq (c.gMulG d) <| .seq (.block (save c)) <|
  .seq (mulV c) (sum c)

/-- Everything after the checks of the key, the points by `pointsG d`. -/
def backG (d : CombData) : Prog isa :=
  .seq (scalars c) <| .seq c.nPow <| .seq (uv c) <| .seq (pointsG c d) (tail c)

/-- `vg_ecdsa_<curve>_verify`, `[u]G` by the comb of `d`. -/
def verifyG (d : CombData) : Prog isa :=
  .seq (.block (args c)) <| .seq (Impl.Ecdh.X86_64.Cfg.prefix' c (some D)) <| .seq (.block (loadS c)) <|
  .seq (.block (Impl.Ecdh.X86_64.Cfg.peer c)) <| .seq (Impl.Ecdh.X86_64.Cfg.check c) (backG c d)

end Cfg

end VG.Impl.Ecdsa.Verify.X86_64
