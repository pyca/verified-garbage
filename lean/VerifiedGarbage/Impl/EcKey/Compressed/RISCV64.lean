module

public import VerifiedGarbage.Impl.Ecdh.RISCV64

/-!
# SEC 1 point compression and decompression on RISC-V

`vg_ec_<curve>_compress_public_key(out = a0, public = a1, scratch = a2)`
and `vg_ec_<curve>_decompress_public_key(out = a0, public = a1, scratch =
a2)`, from the pieces of ECDH (`Impl/Ecdh/RISCV64.lean`): its saves (`s0` and
`s3` the working space, `s2` `out`), its constants, its loads and stores of
numbers, its masks into the flag, and its call of the curve's check of a
point.

`compressFn`: the point (`x`, `y`) read into the check's slots, the flag set
to the mask of the first byte being `04`, the check called (the flag `&=`
the mask of the point being valid), then `02 + (y mod 2)` and `x` (or zeros,
by the flag) to `out`, and the flag's low bit returned.

`decompressFn`, for a prime `p ≡ 3 (mod 4)`: `x` read and the low bit of the
first byte kept (`PAR`), the flag set to the mask of that byte being `02` or
`03` and of `x < p`; then, in Montgomery's form, `rhs = x³ + a x + b`, its
candidate root `y = rhs^((p+1)/4)` (`pow`), `y² - rhs` (whose zero mask goes
into the flag) and `y` out of Montgomery's form; `y` or `p - y`, whichever
has the first byte's parity (by a mask: `sel`), and the mask of the chosen
one having it into the flag (`y = 0` has only one parity); and `04`, `x` and
`y` (or zeros) to `out` (`pointOut`, as the public key's code).

The input is public, but the code does not branch on it either: every
address is a pointer plus a constant, and the only branches are the field
functions' and the power's counter.
-/

@[expose] public section

namespace VG.Impl.EcKey.Compressed.RISCV64

open VG.RISCV64 VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdsa.RISCV64
open VG.Impl.Ecdh.RISCV64 VG.Impl.Ecdh.RISCV64.Cfg

/-- Decompression's slots: the first byte's low bit, the root's exponent
`(p+1)/4`, `rhs`, a product, `y²`, `y² - rhs`, `y`, `p - y` and the chosen
root. -/
def PAR := 10
def EXPS := 11
def RHS := T0
def TT := T1
def YSQ := T2
def DIF := T3
def Y1 := 19
def Y2 := 20
def YF := 21

namespace Cfg

variable (c : Cfg)

/-- The mask `a7` of the byte at `[q]` being `02` or `03`, through `t0` and
`t1`: all ones iff `(byte ^ 2) >> 1 = 0`, the top bit of that minus one. -/
def tagMask (q : Reg) : List Instr :=
  [.load .b .t0 q 0, .logicImm .xor .t0 .t0 2, .shift .srl .d .t0 .t0 1, .addi .t0 .t0 (-1),
    .shift .srl .d .t0 .t0 63, .li .t1 0, .sub .a7 .t1 .t0]

/-- The low bit of the byte at `[q]` to `PAR`'s word, through `t0`. -/
def parCode (q : Reg) : List Instr :=
  [.load .b .t0 q 0, .logicImm .and .t0 .t0 1, .store .d .t0 wb (c.sl PAR)]

/-- The mask `a7` of the low bits of `[a]` and `PAR` differing, through `t0`
and `t1`. -/
def parMask (a : Nat) : List Instr :=
  [.load .d .t0 wb (c.sl a), .load .d .t1 wb (c.sl PAR), .logic .xor .t0 .t0 .t1, .logicImm .and .t0 .t0 1,
    .li .t1 0, .sub .a7 .t1 .t0]

/-- The mask `a7` of the low bits of `[a]` and `PAR` being equal, through `t0`
and `t1`. -/
def sameMask (a : Nat) : List Instr :=
  [.load .d .t0 wb (c.sl a), .load .d .t1 wb (c.sl PAR), .logic .xor .t0 .t0 .t1, .logicImm .and .t0 .t0 1,
    .addi .a7 .t0 (-1)]

/-- `vg_ec_<curve>_compress_public_key(out = a0, public = a1, scratch = a2)`. -/
def compressFn (checkName : String) (checkCode : Prog isa) : Prog isa :=
  .seq (.block (saveCode .a2 ++ loadNum c.n (c.sl CX) .a1 1 ++ loadNum c.n (c.sl CY) .a1 (1 + 8 * c.n) ++
    leadMask .a1 ++ sdAt .a7 wb (c.sl FLAG) ++ constCode c)) <|
  .seq (wsCall checkName checkCode) <|
  .block (ldAt .a7 wb (c.sl FLAG) ++ [.load .d .t0 wb (c.sl CY), .logicImm .and .t0 .t0 1, .addi .t0 .t0 2,
      .logic .and .t0 .t0 .a7, .store .b .t0 .s2 0] ++ storeNum c.n (c.sl CX) .s2 1 ++ retCode c)

/-- The power `rhs^((p+1)/4)`, into `ACC`. -/
def sqrtP : PowCfg := ⟨c.MP', c.sl ACC, c.sl PT, c.sl RHS, c.sl ONEP, c.sl EXPS, 64 * c.n⟩

/-- `x R` and `rhs = x³ + a x + b` in Montgomery's form. -/
def rhsOps : List FOp :=
  [.mul (c.sl CXM) (c.sl CX) (c.sl R2P), .mul (c.sl RHS) (c.sl CXM) (c.sl CXM),
    .mul (c.sl RHS) (c.sl RHS) (c.sl CXM), .mul (c.sl TT) (c.sl AP) (c.sl CXM),
    .add (c.sl RHS) (c.sl RHS) (c.sl TT), .add (c.sl RHS) (c.sl RHS) (c.sl BP)]

/-- `y²`, `y² - rhs`, `y` out of Montgomery's form, and `p - y`. -/
def rootOps : List FOp :=
  [.mul (c.sl YSQ) (c.sl ACC) (c.sl ACC), .sub (c.sl DIF) (c.sl YSQ) (c.sl RHS),
    .mul (c.sl Y1) (c.sl ACC) (c.sl ONE), .sub (c.sl Y2) (c.sl ZERO) (c.sl Y1)]

/-- `vg_ec_<curve>_decompress_public_key(out = a0, public = a1, scratch = a2)`. -/
def decompressFn : Prog isa :=
  .seq (.block (saveCode .a2 ++ loadNum c.n (c.sl CX) .a1 1 ++ parCode c .a1 ++ tagMask .a1 ++
    sdAt .a7 wb (c.sl FLAG) ++ constCode c ++ setConst c.n (c.sl EXPS) ((c.C.p + 1) / 4) ++
    ltMask c.n (c.sl CX) (c.sl MP) ++ andFlag c)) <|
  .seq (fprog c.FP (rhsOps c)) <|
  .seq (pow (sqrtP c) c.FP) <|
  .seq (fprog c.FP (rootOps c)) <|
  .block (zeroMask c.n (c.sl DIF) ++ andFlag c ++ parMask c Y1 ++ sel c.n (c.sl YF) (c.sl Y1) (c.sl Y2) ++
    sameMask c YF ++ andFlag c ++ ldAt .a7 wb (c.sl FLAG) ++ pointOut c CX YF)

end Cfg

end VG.Impl.EcKey.Compressed.RISCV64
