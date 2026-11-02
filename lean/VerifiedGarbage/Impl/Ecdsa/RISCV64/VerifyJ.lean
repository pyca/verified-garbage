module

public import VerifiedGarbage.Impl.Ecdsa.RISCV64.WindowA

/-!
# ECDSA verification on RISC-V, its joint ladder's `R = 4 R` by Jacobian doublings

`vg_ecdsa_<curve>_verify` as `Impl/Ecdsa/RISCV64/Verify.lean` computes it,
but for one change to the joint ladder's step: `R = 4 R` is not two complete
additions of a point to itself but `quad2`, two Jacobian doublings by the
curve's `dbl` (as `vg_<curve>_mul`'s windows do, `Impl/Ecdsa/RISCV64/WindowA.lean`):

* `R` in Jacobian coordinates in `D` (`toJ`), `D` doubled to `T` and back,
  back in projective coordinates in `T` (`fromJ`), and `Y = 1` where `Z = 0`
  (the double of `O`);
* then `R = T + E` by the complete addition, as before.

Everything else (the table, the window's entry, the inversion and the
comparison) is verification's.
-/

@[expose] public section

namespace VG.Impl.Ecdsa.RISCV64.VerifyJ

open VG.RISCV64 VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdsa.RISCV64
open VG.Impl.Ecdsa.RISCV64.Verify

namespace Cfg

variable (c : Cfg) (dbl : RcbSlots → Pt → Pt → List FOp)

/-- `T = 4 R`: to Jacobian coordinates in `D`, two doublings between `D` and
`T`, back to `T`, then `Y = 1` where `Z` is zero. -/
def quad2 : Prog isa :=
  let S := c.rcbSlots
  let R := c.pt RX RY RZ
  let D := c.pt DX DY DZ
  let T := c.pt TX TY TZ
  progs [fprog c.FP (toJ S R (WindowA.Cfg.zeroPt c) D), fprog c.FP (dbl S D T), fprog c.FP (dbl S T D),
    fprog c.FP (fromJ S D (WindowA.Cfg.zeroPt c) T),
    .block (Ecdh.RISCV64.zeroMask c.n (c.sl TZ) ++ sel c.n (c.sl TY) (c.sl TY) (c.sl ONEP))]

/-- One step: `s1 -= 1`, the entry `E`, `T = 4 R`, `R = T + E`. -/
def step : Prog isa :=
  .seq (.block (decCounter :: Verify.Cfg.select c)) <|
  .seq (quad2 c dbl) (Verify.Cfg.addPt c (c.pt TX TY TZ) (c.pt EX EY EZ) (c.pt RX RY RZ))

/-- `R = [u]G + [v]Q`: the table, `R = O`, then the steps. -/
def joint : Prog isa :=
  .seq (Verify.Cfg.build c) <|
  .seq (.block (copy c.n (c.sl RX) (c.sl ZERO) ++ copy c.n (c.sl RY) (c.sl ONEP) ++ copy c.n (c.sl RZ) (c.sl ZERO) ++
    [.li ctr (Verify.Cfg.NW c)]))
    (.loop (step c dbl) more)

/-- `vg_ecdsa_<curve>_verify(public = a0, digest = a1, sig = a2, scratch = a3)`,
as `Verify.Cfg.verify`, with the joint ladder `joint`. -/
def verify (FN : Field) (checkName : String) (checkCode : Prog isa) : Prog isa :=
  .seq (.block (Verify.Cfg.setup c)) <|
  .seq (Ecdh.RISCV64.Cfg.wsCall checkName checkCode) <|
  .seq (.block ((Sign.Cfg.nConsts c).flatMap (fun (i, x) => Ecdh.RISCV64.setConst c.n (c.sl i) x))) <|
  .seq (Verify.Cfg.uv c FN) <|
  .seq (joint c dbl) <|
  .seq (chainPow (Ecdh.RISCV64.Cfg.chainP c) (c.sl ONEP) c.FP) <|
  .seq (Ecdh.RISCV64.Cfg.affineCoord c Ecdh.RISCV64.XM Ecdh.RISCV64.XO RX) <|
  .seq (Verify.Cfg.compare c FN) (.block (Verify.Cfg.finish c))

end Cfg

end VG.Impl.Ecdsa.RISCV64.VerifyJ
