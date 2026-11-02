module

public import VerifiedGarbage.Impl.EcKey.Compressed.RISCV64
public import VerifiedGarbage.Impl.Ecdh.P224.RISCV64

/-!
# P-224's point compression and decompression on RISC-V

As P-256's (`Impl/EcKey/Compressed/RISCV64.lean`), with P-224's numbers of
28 bytes (`loadNum4`, `storeNum4`), and, as `p ≡ 1 (mod 4)`, Tonelli and
Shanks's square root (`Impl/EcKey/Compressed/Root.lean`'s `rootTonelli`, with
`p - 1 = q 2⁹⁶` and the nonresidue 11): in Montgomery's form,

1. `c = 11^q` and `w = rhs^((q-1)/2)` (`pow`), `r = w rhs = rhs^((q+1)/2)`
   and `t = w r = rhs^q`;
2. the descent's 95 rounds, for `n` from 94 down to 0 (`descent`): `u =
   t^(2^n)` (`n` squarings, by a loop counting `s1`), `b = 1` if `u = 1`, else
   `c` (by the mask of `u - 1 = 0`), then `r = r b`, `t = t b²` and `c = c²`;
3. `r` to the root's slot, then as P-256's: `y² - rhs`, `y` or `p - y`.

The rounds are unrolled, so the only loops are the powers' and the
squarings', on counters; every address is a pointer plus a constant.
-/

@[expose] public section

namespace VG.Impl.EcKey.Compressed.RISCV64

open VG.RISCV64 VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdsa.RISCV64
open VG.Impl.Ecdh.RISCV64 VG.Impl.Ecdh.RISCV64.Cfg VG.Impl.EcKey.Compressed.RISCV64.Cfg

/-- The odd part `q` of `p - 1 = q 2⁹⁶`. -/
def q224 : Nat := (Spec.P224.p - 1) / 2 ^ 96

/-- The descent's slots: `r`, `t`, `u = t^(2^n)`, `c`, `b`, `b²`, `u - 1`,
the nonresidue 11 and the exponent `q`. -/
def TR := 13
def TTT := 14
def TU := 15
def TC := 16
def TBV := 17
def TBW := 18
def TD := 22
def ZB := 27
def EXPQ := 28

/-- `vg_ec_p224_compress_public_key`. -/
def compressP224 : Prog isa :=
  .seq (.block (saveCode .a2 ++ loadNum4 3 (p224.sl CX) .a1 1 ++ loadNum4 3 (p224.sl CY) .a1 29 ++
    leadMask .a1 ++ sdAt .a7 wb (p224.sl FLAG) ++ constCode p224)) <|
  .seq (wsCall "vg_p224_check_point" checkP224) <|
  .block (ldAt .a7 wb (p224.sl FLAG) ++ [.load .d .t0 wb (p224.sl CY), .logicImm .and .t0 .t0 1, .addi .t0 .t0 2,
      .logic .and .t0 .t0 .a7, .store .b .t0 .s2 0] ++ storeNum4 3 (p224.sl CX) .s2 1 ++ retCode p224)

/-- The power `11^q`, into `ACC`. -/
def zP : PowCfg := ⟨p224.MP', p224.sl ACC, p224.sl PT, p224.sl ZB, p224.sl ONEP, p224.sl EXPQ, 256⟩

/-- `r = w rhs` and `t = w r`, for `w` in `ACC`. -/
def tonOps : List FOp :=
  [.mul (p224.sl TR) (p224.sl ACC) (p224.sl RHS), .mul (p224.sl TTT) (p224.sl ACC) (p224.sl TR)]

/-- The squarings of `u`, as a chain's (`ChainR.squares`). -/
def sqU : ChainCfg := ⟨p224.MP', p224.sl TU, 0, 0, 0, []⟩

/-- `u - 1`. -/
def subOps : List FOp := [.sub (p224.sl TD) (p224.sl TU) (p224.sl ONEP)]

/-- `r = r b`, `b² `, `t = t b²` and `c = c²`. -/
def updOps : List FOp :=
  [.mul (p224.sl TR) (p224.sl TR) (p224.sl TBV), .mul (p224.sl TBW) (p224.sl TBV) (p224.sl TBV),
    .mul (p224.sl TTT) (p224.sl TTT) (p224.sl TBW), .mul (p224.sl TC) (p224.sl TC) (p224.sl TC)]

/-- The round for `n`: `u = t^(2^n)`, `b = 1` if `u = 1`, else `c`, and the
updates. -/
def round224 (n : Nat) : Prog isa :=
  progs [.block (copy 4 (p224.sl TU) (p224.sl TTT)),
    if n = 0 then .block [] else ChainR.squares sqU p224Field n,
    fprog p224Field subOps,
    .block (zeroMask 4 (p224.sl TD) ++ sel 4 (p224.sl TBV) (p224.sl TC) (p224.sl ONEP)),
    fprog p224Field updOps]

/-- The rounds for `n - 1` down to `0`. -/
def descent224 : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (round224 n) (descent224 n)

/-- `vg_ec_p224_decompress_public_key`. -/
def decompressP224 : Prog isa :=
  .seq (.block (saveCode .a2 ++ loadNum4 3 (p224.sl CX) .a1 1 ++ parCode p224 .a1 ++ tagMask .a1 ++
    sdAt .a7 wb (p224.sl FLAG) ++ constCode p224 ++ setConst 4 (p224.sl EXPS) ((q224 - 1) / 2) ++
    setConst 4 (p224.sl EXPQ) q224 ++ setConst 4 (p224.sl ZB) (mont p224 11) ++
    ltMask 4 (p224.sl CX) (p224.sl MP) ++ andFlag p224)) <|
  .seq (fprog p224Field (rhsOps p224)) <|
  .seq (pow zP p224Field) <|
  .seq (.block (copy 4 (p224.sl TC) (p224.sl ACC))) <|
  .seq (pow (sqrtP p224) p224Field) <|
  .seq (fprog p224Field tonOps) <|
  .seq (descent224 95) <|
  .seq (.block (copy 4 (p224.sl ACC) (p224.sl TR))) <|
  .seq (fprog p224Field (rootOps p224)) <|
  .block (zeroMask 4 (p224.sl DIF) ++ andFlag p224 ++ parMask p224 Y1 ++
    sel 4 (p224.sl YF) (p224.sl Y1) (p224.sl Y2) ++ sameMask p224 YF ++ andFlag p224 ++
    ldAt .a7 wb (p224.sl FLAG) ++ pointOut224 CX YF)

end VG.Impl.EcKey.Compressed.RISCV64
