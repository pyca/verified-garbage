module

public import VerifiedGarbage.Impl.Ecdsa.RISCV64.VerifyJ
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.Comb
public import VerifiedGarbage.Impl.Ecdh.P256.RISCV64

/-!
# ECDSA verification on RISC-V, `[u]G` by the comb and `[v]Q` by windows

`vg_ecdsa_<curve>_verify` as `Impl/Ecdsa/RISCV64/Verify.lean` computes it,
but for `[u]G + [v]Q`: not a joint ladder but two calls, of the curve's
`vg_<curve>_mul` (`[v]Q`, by windows) and of its `vg_<curve>_mul_g` (`[u]G`,
by the comb and its table), and one complete addition (`joint`):

1. `K = v`, or 1 if `v = 0`, and `Q` (the check's point) in `R`'s first two
   slots; the call of `vg_<curve>_mul`; `O = (0 : 1 : 0)` in `R` instead if
   `v = 0` (the mask of `v = 0`, `zeroMask`, by `selPt`), then `R` to `P`'s
   slots (`PX`, `PY`, `PZ`: `e`'s and two others the rest no longer reads,
   apart from what the comb writes);
2. `K = u`, or 1 if `u = 0`; the call of `vg_<curve>_mul_g`; `O` in `R`
   instead if `u = 0`;
3. `T = R + P` by the complete addition, copied to `R`.

The calls' contracts give `[k]Q` for `k` in `[1, n - 1]` (`u` and `v` are
below `n`), so a zero scalar is replaced by 1 and its result by `O`, by
masks: only the pointers affect timing, as before.
-/

@[expose] public section

namespace VG.Impl.Ecdsa.RISCV64.VerifyComb

open VG.RISCV64 VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdsa.RISCV64
open VG.Impl.Ecdh.RISCV64 VG.Impl.Ecdsa.RISCV64.Verify

/-! `[v]Q`'s slots, while the comb runs. -/
def PX := 32
def PY := 34
def PZ := 35

namespace Cfg

variable (c : Cfg)

/-- `O`, as a point. -/
def oPt : Pt := c.pt ZERO ONEP ZERO

/-- `K = [a]`, or 1 if `[a] = 0`: the mask of `[a] = 0`, `[a]` copied to `K`,
and the mask's low bit or'ed into `K`'s low word. -/
def scalar (a : Nat) : List Instr :=
  zeroMask c.n (c.sl a) ++ copy c.n (c.sl K) (c.sl a) ++
    ldAt .t0 wb (c.sl K) ++ [.logicImm .and .t1 .a7 1, .logic .or .t0 .t0 .t1] ++ sdAt .t0 wb (c.sl K)

/-- `R = O` if `[a] = 0`. -/
def zeroR (a : Nat) : List Instr :=
  zeroMask c.n (c.sl a) ++ selPt c.n (c.pt RX RY RZ) (c.pt RX RY RZ) (oPt c)

/-- `R = [u]G + [v]Q`, for `u` at `UU`, `v` at `VV` and `Q` at the check's
point: `vg_<curve>_mul` (`mulName`, its code `mulCode`) and
`vg_<curve>_mul_g` (`gName`, `gCode`). -/
def joint (mulName : String) (mulCode : Prog isa) (gName : String) (gCode : Prog isa) : Prog isa :=
  .seq (.block (scalar c VV ++ copy c.n (c.sl RX) (c.sl CPX) ++ copy c.n (c.sl RY) (c.sl CPY))) <|
  .seq (Ecdh.RISCV64.Cfg.wsCall mulName mulCode) <|
  .seq (.block (zeroR c VV ++ WindowA.Cfg.copyPt c (c.pt PX PY PZ) (c.pt RX RY RZ) ++ scalar c UU)) <|
  .seq (Ecdh.RISCV64.Cfg.wsCall gName gCode) <|
  .seq (.block (zeroR c UU)) <|
  .seq (Verify.Cfg.addPt c (c.pt RX RY RZ) (c.pt PX PY PZ) (c.pt TX TY TZ))
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

end VG.Impl.Ecdsa.RISCV64.VerifyComb
