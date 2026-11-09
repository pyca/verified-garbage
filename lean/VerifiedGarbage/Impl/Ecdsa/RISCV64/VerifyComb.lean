module

public import VerifiedGarbage.Impl.Ecdsa.RISCV64.VerifyJ
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.Comb
public import VerifiedGarbage.Impl.Ecdh.P256.RISCV64
public import VerifiedGarbage.Impl.Ecdsa.P384.RISCV64Window

/-!
# ECDSA verification on RISC-V, `[u]G` by the comb and `[v]Q` by windows

`vg_ecdsa_<curve>_verify` as `Impl/Ecdsa/RISCV64/Verify.lean` computes it,
but for `[u]G + [v]Q`: not a joint ladder but two calls, of the curve's
`vg_<curve>_mul` (`[v]Q`, by windows) and of its `vg_<curve>_mul_g` (`[u]G`,
by the comb and its table), and one complete addition (`joint`):

1. `K = v` and `Q` (the check's point) in `R`'s first two slots; the call of
   `vg_<curve>_mul`; `O = (0 : 1 : 0)` in `R` instead if `v = 0` (the mask of
   `v = 0`, `zeroMask`, by `selPt`), then `R` to `P = (GX : CPX : CPY)`, slots the
   comb does not write and the rest no longer reads (`G`'s first coordinate,
   which the comb does not need, and `Q`'s, which the call has read), and
   `b` to `BP` again (the callees' contracts do not keep it);
2. `K = u`; the call of `vg_<curve>_mul_g`; `O` in `R` instead if `u = 0`,
   and `b` to `BP` again;
3. `T = R + P` by the complete addition, copied to `R`.

The calls' contracts give `[k]Q` for `k` in `[1, n - 1]` (`u` and `v` are
below `n`), and what they leave alone for any `k`: a zero scalar's result is
replaced by `O`, by a mask, so only the pointers affect timing, as before.
-/

@[expose] public section

namespace VG.Impl.Ecdsa.RISCV64.VerifyComb

open VG.RISCV64 VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdsa.RISCV64
open VG.Impl.Ecdh.RISCV64 VG.Impl.Ecdsa.RISCV64.Verify

namespace Cfg

variable (c : Cfg)

/-- `O`, as a point. -/
def oPt : Pt := c.pt ZERO ONEP ZERO

/-- `R = O` if `[a] = 0`, and `b` (in Montgomery's form) to `BP` again: the
callees' contracts do not keep it. -/
def zeroR (a : Nat) : List Instr :=
  zeroMask c.n (c.sl a) ++ selPt c.n (c.pt RX RY RZ) (c.pt RX RY RZ) (oPt c) ++
    setConst c.n (c.sl BP) (Cfg.mont c c.C.b)

/-- `R = [u]G + [v]Q`, for `u` at `UU`, `v` at `VV` and `Q` at the check's
point: `vg_<curve>_mul` (`mulName`, its code `mulCode`) and
`vg_<curve>_mul_g` (`gName`, `gCode`). -/
def joint (mulName : String) (mulCode : Prog isa) (gName : String) (gCode : Prog isa) : Prog isa :=
  .seq (.block (copy c.n (c.sl K) (c.sl VV) ++ copy c.n (c.sl RX) (c.sl CPX) ++ copy c.n (c.sl RY) (c.sl CPY))) <|
  .seq (Ecdh.RISCV64.Cfg.wsCall mulName mulCode) <|
  .seq (.block (zeroR c VV ++ WindowA.Cfg.copyPt c (c.pt GX CPX CPY) (c.pt RX RY RZ) ++
    copy c.n (c.sl K) (c.sl UU))) <|
  .seq (Ecdh.RISCV64.Cfg.wsCall gName gCode) <|
  .seq (.block (zeroR c UU)) <|
  .seq (Verify.Cfg.addPt c (c.pt RX RY RZ) (c.pt GX CPX CPY) (c.pt TX TY TZ))
    (.block (WindowA.Cfg.copyPt c (c.pt RX RY RZ) (c.pt TX TY TZ)))

/-- `vg_ecdsa_<curve>_verify(public = a0, digest = a1, sig = a2, scratch = a3)`,
as `Verify.Cfg.verify`, with `joint`. -/
def verify (FN : Field) (checkName : String) (checkCode : Prog isa) (mulName : String) (mulCode : Prog isa)
    (gName : String) (gCode : Prog isa) : Prog isa :=
  .seq (.block (Verify.Cfg.setup c)) <|
  .seq (Ecdh.RISCV64.Cfg.wsCall checkName checkCode) <|
  .seq (.block ((Sign.Cfg.nConsts c).flatMap (fun (i, x) => setConst c.n (c.sl i) x))) <|
  .seq (Verify.Cfg.uv c FN) <|
  .seq (joint c mulName mulCode gName gCode) <|
  .seq (chainPow (Cfg.chainP c) (c.sl ONEP) c.FP) <|
  .seq (Cfg.affineCoord c XM XO RX) <|
  .seq (Verify.Cfg.compare c FN) (.block (Verify.Cfg.finish c))

end Cfg

/-- `vg_ecdsa_p256_verify`, with `vg_p256_mul` and `vg_p256_mul_g`. -/
def verifyP256 : Prog isa :=
  Cfg.verify p256 p256Order "vg_p256_check_point" checkP256 "vg_p256_mul" Window.mulP256
    Comb.mulGP256Name Comb.mulGP256

/-- `vg_ecdsa_p384_verify`, with `vg_p384_mul` and `vg_p384_mul_g`. -/
def verifyP384 : Prog isa :=
  Cfg.verify p384 p384Order "vg_p384_check_point" checkP384 "vg_p384_mul" mulP384
    Comb.mulGP384Name Comb.mulGP384

end VG.Impl.Ecdsa.RISCV64.VerifyComb
