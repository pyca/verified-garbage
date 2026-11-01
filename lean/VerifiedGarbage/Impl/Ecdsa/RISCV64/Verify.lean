module

public import VerifiedGarbage.Impl.Ecdsa.RISCV64.Sign
public import VerifiedGarbage.Impl.Ecdh.P256.RISCV64

/-!
# ECDSA signature verification on RISC-V

`vg_ecdsa_<curve>_verify(public, digest, sig, scratch) -> a0`
(`Spec/Ecdsa/Verify/Generic.lean`), for a curve whose `n` has `64 n` bits,
with the pieces of ECDH (`Impl/Ecdh/RISCV64.lean`) and of signing
(`Impl/Ecdsa/RISCV64/Sign.lean`):

1. the registers saved, the public key's `x` and `y` read into the check's
   slots, the flag set to the mask of its first byte being `04`, the
   constants stored, `r`, `s` and the digest's `e` read (into slots the
   check keeps, before its call writes the argument registers), and the
   masks of `r` and `s` being in `[1, n-1]` anded into the flag;
2. the check of the key, by a call (`x < p`, `y < p` and the curve's
   equation into the flag; its point, or `G`, to `CPX` and `CPY`);
3. modulo `n`: `w = (s R)^(n-2)`, `u = e w` and `v = r w`, out of
   Montgomery's form;
4. `[u]G` by the ladder of `vg_<curve>_mul`'s body, inline (its contract
   needs a scalar in `[1, n-1]`, and `u` may be 0), saved; then `[v]Q`;
5. their sum by the complete addition, `Z^(p-2)` and `x = X Z^(p-2)`;
6. `x mod n` and `r mod n` (by additions of zero, both operands below `2n`),
   their difference modulo `n`, the masks of `Z ≠ 0` and of that difference
   being zero into the flag, whose low bit is returned.

Everything is computed whatever the flag, and only the pointers affect
timing, although the contract would let every input affect it.
-/

@[expose] public section

namespace VG.Impl.Ecdsa.RISCV64.Verify

open VG.RISCV64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdsa.RISCV64
open VG.Impl.Ecdh.RISCV64 VG.Impl.Ecdsa.RISCV64.Sign

/-! Slots: `e`, `r` and `s`, which the check keeps; `u` and `v`, and `[u]G`,
in the check's slots, which the ladder keeps; and the values of the
comparison. -/
def VE := 32
def VR := 10
def VS := 11
def UM := 22
def UU := 33
def VM := 24
def VV := 36
def UX := 41
def UY := 42
def UZ := 34
def XN := 19
def RN := 20
def WD := 21

namespace Cfg

variable (c : Cfg) (FN : Field)

/-- The saves, the public key's point and the flag, the constants, `r`, `s`
and `e`, and the masks of `r` and `s` in `[1, n-1]`. -/
def setup : List Instr :=
  Ecdh.RISCV64.Cfg.saveCode .a3 ++ loadNum c.n (c.sl CX) .a0 1 ++ loadNum c.n (c.sl CY) .a0 (1 + 8 * c.n) ++
    leadMask .a0 ++ ([.store .d .a7 wb (c.sl FLAG)] : List Instr) ++ Ecdh.RISCV64.Cfg.constCode c ++
    loadNum c.n (c.sl VR) .a2 0 ++ loadNum c.n (c.sl VS) .a2 (8 * c.n) ++ loadNum c.n (c.sl VE) .a1 0 ++
    Ecdh.RISCV64.Cfg.rangeOf c VR ++ Ecdh.RISCV64.Cfg.rangeOf c VS

/-- `w = (s R)^(n-2)`, `u = e w` and `v = r w` modulo `n`. -/
def uv : Prog isa :=
  progs [mulCall FN (c.sl KM) (c.sl VS) (c.sl R2N), pow (Sign.Cfg.powN c) FN,
    mulCall FN (c.sl EM) (c.sl VE) (c.sl R2N), mulCall FN (c.sl UM) (c.sl EM) (c.sl ACC),
    mulCall FN (c.sl UU) (c.sl UM) (c.sl ONE), mulCall FN (c.sl RM) (c.sl VR) (c.sl R2N),
    mulCall FN (c.sl VM) (c.sl RM) (c.sl ACC), mulCall FN (c.sl VV) (c.sl VM) (c.sl ONE)]

/-- `R = [u]G`, saved to `U`, then `R = [v]Q`. -/
def points : Prog isa :=
  .seq (.block (copy c.n (c.sl K) (c.sl UU) ++ copy c.n (c.sl RX) (c.sl GX) ++ copy c.n (c.sl RY) (c.sl GY))) <|
  .seq c.mulBody <|
  .seq (.block (copy c.n (c.sl UX) (c.sl RX) ++ copy c.n (c.sl UY) (c.sl RY) ++ copy c.n (c.sl UZ) (c.sl RZ) ++
    copy c.n (c.sl K) (c.sl VV) ++ copy c.n (c.sl RX) (c.sl CPX) ++ copy c.n (c.sl RY) (c.sl CPY)))
    c.mulBody

/-- `R = U + R`, through `D`. -/
def sum : Prog isa :=
  .seq (fprog c.FP (rcb c.rcbSlots (c.pt UX UY UZ) (c.pt RX RY RZ) (c.pt DX DY DZ)))
    (.block (copy c.n (c.sl RX) (c.sl DX) ++ copy c.n (c.sl RY) (c.sl DY) ++ copy c.n (c.sl RZ) (c.sl DZ)))

/-- `x mod n`, `r mod n` and their difference. -/
def compare : Prog isa :=
  progs [addCall FN (c.sl XN) (c.sl XO) (c.sl ZERO), addCall FN (c.sl RN) (c.sl VR) (c.sl ZERO),
    subCall FN (c.sl WD) (c.sl XN) (c.sl RN)]

/-- The masks of `Z ≠ 0` and of the difference being zero into the flag, its
low bit returned, the registers restored. -/
def finish : List Instr :=
  Sign.Cfg.nonzeroFlag c RZ ++ zeroMask c.n (c.sl WD) ++ Ecdh.RISCV64.Cfg.andFlag c ++ Ecdh.RISCV64.Cfg.retCode c

/-- `vg_ecdsa_<curve>_verify(public = a0, digest = a1, sig = a2, scratch = a3)`,
with the check of the key `checkName` (its code `checkCode`). -/
def verify (checkName : String) (checkCode : Prog isa) : Prog isa :=
  .seq (.block (setup c)) <|
  .seq (Ecdh.RISCV64.Cfg.wsCall checkName checkCode) <|
  .seq (.block ((Sign.Cfg.nConsts c).flatMap (fun (i, x) => setConst c.n (c.sl i) x))) <|
  .seq (uv c FN) <|
  .seq (points c) <|
  .seq (sum c) <|
  .seq (pow (Ecdh.RISCV64.Cfg.powP c) c.FP) <|
  .seq (Ecdh.RISCV64.Cfg.affineCoord c XM XO RX) <|
  .seq (compare c FN) (.block (finish c))

end Cfg

/-- `vg_ecdsa_p256_verify`. -/
def verifyP256 : Prog isa :=
  Cfg.verify p256 p256Order "vg_p256_check_point" Ecdh.RISCV64.checkP256

end VG.Impl.Ecdsa.RISCV64.Verify
