module

public import VerifiedGarbage.Impl.Ecdsa.RISCV64.Window
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.Verify

/-!
# `[k]Q` by four-bit windows on RISC-V, for any `a`

`vg_<curve>_mul(ws)` as `Impl/Ecdsa/RISCV64/Window.lean` computes it, for a
curve with any `a`, on the layout of `Impl/Ecdsa/RISCV64.lean` (`Q` affine in
`R`'s first two slots, `k` at `K`'s slot, `a` at `AP` and `3 b` at `B3P` in
Montgomery's form, the result in `R`), with the curve's Jacobian doubling
`dbl` (`dblJa` for any `a`, `dblJ0` for `a = 0`, `dblJ` for `a = -3`):

1. the table of `[e]Q` for `e < 16` at `c.jt` (`24 n` bytes each, past the
   slots when they reach it), stored through `a6 = s0 + jt` as verification's
   table is (`Verify.Cfg.storePt`): `O = (0 : 1 : 0)` and `Q = (x : y : 1)`,
   then `[e]Q = [e - 1]Q + Q` by fourteen complete additions (`Verify.Cfg.addPt`,
   `rcb` or, for `a = -3`, `rcb3`) in the slots `D` and `T`;
2. from `R = O`, for the windows `j` from `16 n - 1` down to `0`,
   `R = 16 R + [k_j]Q`:
   * the nibble `k_j` (`nibble`) and the masks of its four bits, then the
     entry by the comb's tree of selections over the sixteen entries at
     `a0 = s0 + jt` (`scanWord`), into `E`;
   * `R = 16 R` (`quad`): `R` in Jacobian coordinates, four doublings by
     `dbl`, back in projective coordinates, and `Y = 1` where `Z = 0`;
   * `T = R + E` by the complete addition, copied to `R`.

The only branch is on the counter, and every address is `s0` plus a
constant, plus `8 (j >>> 4)` for the nibble's word: only the pointer may
affect timing.
-/

@[expose] public section

namespace VG.Impl.Ecdsa.RISCV64.WindowA

open VG.RISCV64 VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdsa.RISCV64
open VG.Impl.Ecdsa.RISCV64.Window (windows)

/-- `o = 2p` in Jacobian coordinates for any `a`, at the slot `S.a`
(dbl-2007-bl, with `Z' = 2YZ` as a product): `A = X²`, `B = Y²`, `C = B²`,
`D = 2 ((X + B)² - A - C)`, `M = 3A + a (Z²)²`, `Z' = 2YZ`, `X' = M² - 2D`,
`Y' = M (D - X') - 8C`; 9 products and 1 by `a` (temporaries `t0 … t5`;
`o` apart from `p`). -/
def dblJa (S : RcbSlots) (p o : Pt) : List FOp :=
  [.mul S.t0 p.x p.x, .mul S.t1 p.y p.y, .mul S.t2 S.t1 S.t1, .add S.t3 p.x S.t1,
   .mul S.t3 S.t3 S.t3, .sub S.t3 S.t3 S.t0, .sub S.t3 S.t3 S.t2, .add S.t3 S.t3 S.t3,
   .mul S.t4 p.z p.z, .mul S.t4 S.t4 S.t4, .mul S.t4 S.a S.t4, .add S.t5 S.t0 S.t0,
   .add S.t5 S.t5 S.t0, .add S.t4 S.t4 S.t5, .mul o.z p.y p.z, .add o.z o.z o.z,
   .mul o.x S.t4 S.t4, .sub o.x o.x S.t3, .sub o.x o.x S.t3, .sub o.y S.t3 o.x,
   .mul o.y S.t4 o.y, .add S.t2 S.t2 S.t2, .add S.t2 S.t2 S.t2, .add S.t2 S.t2 S.t2,
   .sub o.y o.y S.t2]

namespace Cfg

variable (c : Cfg) (dbl : RcbSlots → Pt → Pt → List FOp)

/-- Zero, as a point (`toJ` and `fromJ` add zero to copy). -/
def zeroPt : Pt := c.pt ZERO ZERO ZERO

/-- `o = p`. -/
def copyPt (o p : Pt) : List Instr := copy c.n o.x p.x ++ copy c.n o.y p.y ++ copy c.n o.z p.z

/-- `[e + 2]Q = [e + 1]Q + Q` in `T` from `D`, stored, and `D = T`, for
`e` from 0 up to `e`. -/
def adds : Nat → Prog isa
  | 0 => .block []
  | e + 1 => .seq (adds e) <|
    .seq (Verify.Cfg.addPt c (c.pt DX DY DZ) (c.pt RX RY ONEP) (c.pt TX TY TZ))
      (.block (Verify.Cfg.storePt c (e + 2) (c.pt TX TY TZ) ++ copyPt c (c.pt DX DY DZ) (c.pt TX TY TZ)))

/-- The table: `O`, `Q`, then `[e]Q` for `e = 2 … 15`. -/
def build : Prog isa :=
  .seq (.block (Verify.Cfg.storePt c 0 (c.pt ZERO ONEP ZERO) ++ Verify.Cfg.storePt c 1 (c.pt RX RY ONEP) ++
    copyPt c (c.pt DX DY DZ) (c.pt RX RY ONEP))) (adds c 14)

/-- The nibble `k_j` of `k` into `t2`, for `j` in `s1`: the word `j >>> 4`
shifted right by `4 j` (modulo 64), and four bits of it. -/
def nibble : List Instr :=
  [.shift .srl .d .t0 ctr 4, .shift .sll .d .t0 .t0 3, .add .t0 .t0 wb] ++ ldAt .t2 .t0 (c.sl K) ++
    [.shift .sll .d .t1 ctr 2, .shiftReg .srl .d .t2 .t2 .t1, .logicImm .and .t2 .t2 15]

/-- The entry of the nibble to `E`: the nibble, its bits' masks, `a0` at the
table, and its `3 n` quadwords, as verification selects its table's
(`Verify.Cfg.scanWord`). -/
def select : List Instr :=
  nibble c ++ (List.range 4).flatMap Comb.Cfg.maskOfBit ++ addAt .a0 wb c.jt ++
    (List.range (3 * c.n)).flatMap (Verify.Cfg.scanWord c)

/-- `R = 16 R`: to Jacobian coordinates in `D`, four doublings between `D`
and `T`, back to `R`, then `Y = 1` where `Z` is zero. -/
def quad : Prog isa :=
  let S := c.rcbSlots
  let R := c.pt RX RY RZ
  let D := c.pt DX DY DZ
  let T := c.pt TX TY TZ
  progs [fprog c.FP (toJ S R (zeroPt c) D), fprog c.FP (dbl S D T), fprog c.FP (dbl S T D),
    fprog c.FP (dbl S D T), fprog c.FP (dbl S T D), fprog c.FP (fromJ S D (zeroPt c) R),
    .block (Ecdh.RISCV64.zeroMask c.n (c.sl RZ) ++ sel c.n (c.sl RY) (c.sl RY) (c.sl ONEP))]

/-- One window: `s1 -= 1`, the entry `E` of the nibble, `R = 16 R`, and
`R = R + E`. -/
def step : Prog isa :=
  .seq (.block (decCounter :: select c)) <|
  .seq (quad c dbl) <|
  .seq (Verify.Cfg.addPt c (c.pt RX RY RZ) (c.pt c.EX c.EY c.EZ) (c.pt TX TY TZ))
    (.block (copyPt c (c.pt RX RY RZ) (c.pt TX TY TZ)))

/-- The body: the table, `R = O`, then the windows. -/
def body : Prog isa :=
  .seq (build c) <|
  .seq (.block (copyPt c (c.pt RX RY RZ) (c.pt ZERO ONEP ZERO) ++ [.li ctr (windows c)]))
    (.loop (step c dbl) more)

/-- `vg_<curve>_mul(ws = a0)`: `s0`, `s1` and `ra` kept around the body, as
`Cfg.mulFn` does, with the working space's base in `s0`. -/
def mulFn : Prog isa :=
  .seq (.block (sdAt .s0 .a0 c.mulSave ++ sdAt .s1 .a0 (c.mulSave + 8) ++ sdAt .ra .a0 (c.mulSave + 16) ++
    [.addi .s0 .a0 0])) <|
  .seq (body c dbl) (.block (ldAt .ra .s0 (c.mulSave + 16) ++ ldAt .s1 .s0 (c.mulSave + 8) ++
    ldAt .s0 .s0 c.mulSave))

end Cfg

end VG.Impl.Ecdsa.RISCV64.WindowA
