module

public import VerifiedGarbage.Impl.Ecdh.RISCV64
public import VerifiedGarbage.Impl.Ecdsa.P256.RISCV64
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.Comb
public import VerifiedGarbage.Spec.Weierstrass.Mul

/-!
# ECDSA signatures on RISC-V

`vg_ecdsa_<curve>_sign(out, d, digest, k, scratch)` (`Spec/Ecdsa/Generic.lean`)
for a curve of `n` 64-bit words whose `n` has `64 n` bits (so that the
hash's integer `e` is the digest's), on the layout of
`Impl/Ecdsa/RISCV64.lean` and with the pieces of ECDH
(`Impl/Ecdh/RISCV64.lean`):

1. the registers saved and the working space's base to `s0` and `s3`, `out`
   to `s2` (`saveCode`), `k`, `d` and the digest read big-endian into `K`,
   `DD` and `EE`, the flag set, the constants stored, the mask of `d` being
   in `[1, n-1]` anded into the flag, and `G` to `R`'s first two slots;
2. ECDH's `tail` (`tl`): the mask of `k` being in `[1, n-1]` into the flag,
   `R = [k]G`, `Z^(p-2)` and `x = X Z^(p-2)` out of Montgomery's form;
3. modulo `n`, with the functions of `FN`: `r = x mod n` (`x + 0`, as
   `x < p < 2n`), `k R`, `w = (k R)^(n-2)` (`pow`, in Montgomery's form:
   `k^(n-2) R`), and `s = w (e R + (r R) (d R)) R⁻¹ R⁻¹` out of
   Montgomery's form;
4. the masks of `r ≠ 0` and `s ≠ 0` anded into the flag (`R = O` gives
   `x = 0`, so `r = 0`), `r` and `s` stored big-endian to `out` under the
   flag's mask, and the flag's low bit returned.

Everything is computed whatever the flag: only the pointers may affect
timing.
-/

@[expose] public section

namespace VG.Impl.Ecdsa.RISCV64.Sign

open VG.RISCV64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdsa.RISCV64
open VG.Impl.Ecdh.RISCV64

/-! Slots: `d`, `e` and the constants modulo `n`, which `vg_<curve>_mul`
keeps, and those of the values modulo `n`, which are past the ladder's use. -/
def DD := 33
def EE := 34
def R2N := 35
def ONEN := 36
def EXPN := 37
def RR := 19
def KM := 20
def EM := 21
def RM := 22
def DM := 23
def TT := 24
def SU := 25
def SMM := 26
def SS := 27

namespace Cfg

variable (c : Cfg) (FN : Field)

/-- The constants modulo `n`: `R² mod n`, `R mod n` and `n - 2`. -/
def nConsts : List (Nat × Nat) :=
  [(R2N, 2 ^ (64 * c.n) * 2 ^ (64 * c.n) % c.C.n), (ONEN, 2 ^ (64 * c.n) % c.C.n), (EXPN, c.C.n - 2)]

/-- The modulus `n`'s layout, as the power has it. -/
def MN' : Mod := { n := c.n, mo := c.sl MN, tmp := c.sl TMP, minv := 0 }

/-- The power `(k R)^(n-2)`, into `ACC`. -/
def powN : PowCfg := ⟨MN' c, c.sl ACC, c.sl PT, c.sl KM, c.sl ONEN, c.sl EXPN, 64 * c.n⟩

/-- The registers saved, the arguments read, the flag set, the constants
stored, the mask of `d` in `[1, n-1]`, and `G` to `R`'s first two slots. -/
def setup : List Instr :=
  Cfg.saveCode .a4 ++ loadNum c.n (c.sl K) .a3 0 ++ loadNum c.n (c.sl DD) .a1 0 ++
    loadNum c.n (c.sl EE) .a2 0 ++ [.li .t0 0, .addi .t0 .t0 (-1), .store .d .t0 wb (c.sl FLAG)] ++
    Cfg.constCode c ++ (nConsts c).flatMap (fun (i, x) => setConst c.n (c.sl i) x) ++
    Cfg.rangeOf c DD ++ copy c.n (c.sl RX) (c.sl GX) ++ copy c.n (c.sl RY) (c.sl GY)

/-- `s = k^(n-2) (e + r d) mod n`, from `r` in `RR`, by the functions of `FN`. -/
def scalars : Prog isa :=
  progs [mulCall FN (c.sl KM) (c.sl K) (c.sl R2N), pow (powN c) FN,
    mulCall FN (c.sl EM) (c.sl EE) (c.sl R2N), mulCall FN (c.sl RM) (c.sl RR) (c.sl R2N),
    mulCall FN (c.sl DM) (c.sl DD) (c.sl R2N), mulCall FN (c.sl TT) (c.sl RM) (c.sl DM),
    addCall FN (c.sl SU) (c.sl EM) (c.sl TT), mulCall FN (c.sl SMM) (c.sl ACC) (c.sl SU),
    mulCall FN (c.sl SS) (c.sl SMM) (c.sl ONE)]

/-- The flag `&=` the mask of the number at slot `i` being nonzero. -/
def nonzeroFlag (i : Nat) : List Instr :=
  zeroMask c.n (c.sl i) ++ [.logicImm .xor .a7 .a7 (-1)] ++ Cfg.andFlag c

/-- The checks of `r` and `s`, and `r ‖ s` to `out` under the flag's mask,
the flag's low bit returned. -/
def finish : List Instr :=
  nonzeroFlag c RR ++ nonzeroFlag c SS ++ [.load .d .a7 wb (c.sl FLAG)] ++
    storeNum c.n (c.sl RR) .s2 0 ++ storeNum c.n (c.sl SS) .s2 (8 * c.n) ++ Cfg.retCode c

/-- What follows `x`: `r`, `s`, the checks and the result. -/
def back : Prog isa :=
  .seq (.seq (addCall FN (c.sl RR) (c.sl XO) (c.sl ZERO)) (scalars c FN)) (.block (finish c))

/-- `vg_ecdsa_<curve>_sign(out = a0, d = a1, digest = a2, k = a3, scratch = a4)`,
with `tl` from `k`'s range to `x` (ECDH's `tail`, for some multiplication
of `R = [k]G`). -/
def signWith (tl : Prog isa) : Prog isa :=
  .seq (.block (setup c)) (.seq tl (back c FN))

/-- With `R = [k]G` by a call of `vg_<curve>_mul` (`mulName`, its code `mulCode`). -/
def sign (mulName : String) (mulCode : Prog isa) : Prog isa := signWith c FN (Cfg.tail c mulName mulCode)

end Cfg

/-- `vg_ecdsa_p256_sign`, with `[k]G` by the comb, `vg_p256_mul_g`. -/
def signP256 : Prog isa := Cfg.sign p256 p256Order Comb.mulGP256Name Comb.mulGP256

end VG.Impl.Ecdsa.RISCV64.Sign
