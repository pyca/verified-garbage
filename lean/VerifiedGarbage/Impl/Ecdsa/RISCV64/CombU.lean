module

public import VerifiedGarbage.Impl.Ecdsa.RISCV64.WindowU
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.Comb
public import VerifiedGarbage.Impl.P521.CombTable7

/-!
# `[k]G` on P-521 by the signed seven-bit comb on RISC-V, in 58-bit limbs

`vg_p521_mul_g(ws)`: `R = [k]G` for the scalar `k` at `K`'s slot, on
`vg_p521_mul`'s layout and field arithmetic
(`Impl/Ecdsa/RISCV64/WindowU.lean`: elements of nine 58-bit limbs, the
complete addition `addPt`), by the comb of `Impl/Ecdsa/RISCV64/Comb.lean`
over the table the other targets share (`Impl/P521/CombTable7.lean`, 83
windows of seven bits): `[k]G = S + Σ_j [(k_j - 64) 2^(7j)]G` for the
start `S = [64 Σ_j 2^(7j)]G`. Table `j` of the static `VG_P521_COMB` holds
`[m 2^(7j)]G` for `m = 1 … 64` (entry `m - 1`: `x` then `y`, nine words
each, in Montgomery's form, 144 bytes), 9216 bytes a table.

`S`, in Montgomery's form, goes to limbs with the constants (`convIn`).
Then, for `j` from 82 down to 0 (the counter `s1 = j + 1`, then `j`):

1. the window `k_j` of the copy of `k` at `KC` (`Comb.Cfg.window`), its
   digit's sign's mask and the mask of a zero digit, kept at `MS` and `MZ`
   across the calls, and the masks of the six bits of the entry's number
   (`Comb.Cfg.maskOfBit`);
2. each of the entry's 18 quadwords selected from the table's 64 entries
   without a secret address (`scanWord`): eight groups of eight entries,
   each by `Comb.tree` over the masks of bits 0 to 2 at `a7`, which steps
   through the groups, then the pairs, the fours and the two by the masks of
   bits 3, 4 and 5 (`groups`); the entry to `D`'s first two slots;
3. `D`'s coordinates to limbs (`toU`), `Z = 1`; for a zero digit,
   `D = (0 : 1 : 0)` by its mask; `-y` (the field's subtraction from zero,
   into `T`'s first slot) and `y = -y` by the sign's mask;
4. `T = R + D` by the complete addition (`addPt`), copied to `R`.

`R` then goes back to Montgomery's form (`convOut`), as `vg_p521_mul`'s does.

The only branch is on the counter, and every address is `s0` plus a constant
(plus `8 (7j >>> 6)` for the window's words) or the table's address plus a
constant (plus `9216 j`): only the pointer may affect timing. The table's
address is in `s4`, as in `Comb.lean`'s functions.
-/

@[expose] public section

namespace VG.Impl.Ecdsa.RISCV64.CombU

open VG.RISCV64 VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdsa.RISCV64
open VG.Impl.Ecdsa.RISCV64.WindowU (c F addPt toU UONE convIn convOut)
open VG.Impl.Ecdsa.RISCV64.Comb (KC maskReg treeRegs pick tree)
open VG.Impl.Ecdsa.RISCV64.WindowA.Cfg (copyPt)

/-- The windows: `⌈576 / 7⌉`. -/
def nwin : Nat := 83

/-- The bytes of an entry. -/
def eb : Nat := 144

/-- Where the mask of the digit's sign is kept, after the copy of `k` and
its zero word, and the mask of a zero digit after it. -/
def MS : Nat := c.sl KC + 80
def MZ : Nat := c.sl KC + 88

/-- The selection of quadword `q` among `2 ^ L` groups of eight entries,
from the group at `a7` on, into the first of the registers: a group by
`tree` over the masks of bits 0 to 2, `a7` then on to the next, and two
halves' selections by the mask of bit `3 + L`. -/
def groups (q : Nat) : Nat → List Reg → List Instr
  | 0, rs => tree .a7 eb 3 (8 * q) rs ++ [.addi .a7 .a7 (8 * eb)]
  | L + 1, a :: b :: rs => groups q L (a :: b :: rs) ++ groups q L (b :: rs) ++ pick a b (maskReg (3 + L))
  | _, _ => []

/-- Quadword `q` of the entry selected from the row at `a0`, to `D` at `8 q`. -/
def scanWord (q : Nat) : List Instr :=
  .addi .a7 .a0 0 :: (groups q 3 treeRegs ++ [.store .d .t0 wb (c.sl DX + 8 * q)])

/-- From the window in `t2`: the digit's sign's mask to `MS`, the entry's
number `t = |d| - 1` in `t2`, the mask of `|d| = 0` to `MZ`. -/
def digit : List Instr :=
  [.addi .t2 .t2 (-64), .shift .sra .d .t3 .t2 63, .logic .xor .t2 .t2 .t3, .sub .t2 .t2 .t3,
   .addi .t2 .t2 (-1), .shift .sra .d .t4 .t2 63] ++ sdAt .t3 wb MS ++ sdAt .t4 wb MZ

/-- The table's row `j` (for `j` in `s1`, the table's address in `s4`), of
64 entries of 144 bytes, in `a0`: `9216 j` as `8192 j + 1024 j`. -/
def row : List Instr :=
  [.shift .sll .d .t0 ctr 13, .shift .sll .d .t1 ctr 10, .add .t0 .t0 .t1, .add .a0 .s4 .t0]

/-- The entry, in Montgomery's form, to `D`'s first two slots: the window,
the digit, the masks, the row and the 18 quadwords. -/
def select : List Instr :=
  Comb.Cfg.window c ++ digit ++ (List.range 6).flatMap Comb.Cfg.maskOfBit ++ row ++
    (List.range 18).flatMap scanWord

/-- `D`: the entry in limbs with `Z = 1`, `(0 : 1 : 0)` for a zero digit,
and `y = -y` for a negative one. -/
def entry : Prog isa :=
  progs [toU (c.sl DX) (c.sl DX), toU (c.sl DY) (c.sl DY),
    .block (ldAt .a7 wb MZ ++ sel 9 (c.sl DX) (c.sl DX) (c.sl ZERO) ++ sel 9 (c.sl DY) (c.sl DY) (c.sl UONE) ++
      sel 9 (c.sl DZ) (c.sl UONE) (c.sl ZERO)),
    subCall F (c.sl TX) (c.sl ZERO) (c.sl DY),
    .block (ldAt .a7 wb MS ++ sel 9 (c.sl DY) (c.sl DY) (c.sl TX))]

/-- One step: `s1 -= 1`, the signed entry `D`, and `R = R + D`. -/
def step : Prog isa :=
  .seq (.block (decCounter :: select)) <|
  .seq entry <|
  .seq (addPt (c.pt RX RY RZ) (c.pt DX DY DZ) (c.pt TX TY TZ))
    (.block (copyPt c (c.pt RX RY RZ) (c.pt TX TY TZ)))

/-- The comb's body: the copy of `k` and its zero word, the start (affine,
in Montgomery's form) to `R`'s first two slots, it and the constants to
limbs, `Z = 1`, then the steps. -/
def body (start : Nat × Nat) : Prog isa :=
  .seq (.block (copy 9 (c.sl KC) (c.sl K) ++ [.li .t0 0] ++ sdAt .t0 wb (c.sl KC + 72) ++
    Ecdh.RISCV64.setConst 9 (c.sl RX) (Ecdh.RISCV64.Cfg.mont c start.1) ++
    Ecdh.RISCV64.setConst 9 (c.sl RY) (Ecdh.RISCV64.Cfg.mont c start.2))) <|
  .seq convIn <|
  .seq (.block (copy 9 (c.sl RZ) (c.sl UONE) ++ [.li ctr nwin]))
    (.loop step more)

/-- The table's symbol. -/
def p521Sym : String := "VG_P521_COMB"

/-- The words of P-521's tables (`Impl/P521/CombTable7.lean`), in
Montgomery's form. -/
@[irreducible] def p521CombWords : List (BitVec 64) :=
  tcombWords 9 (2 ^ 576) Spec.P521.curve.p Impl.P521.p521Comb7

def p521CombConsts : List (String × List (BitVec 64)) := [(p521Sym, p521CombWords)]

/-- `vg_p521_mul_g(ws = a0)`: the table's address (`lla`, first, into `t0`,
then `s4`), `s0`, `s1`, `s4` and `ra` kept around the body, with the working
space's base in `s0`, and `R` back in Montgomery's form. -/
def mulGP521 : Prog isa :=
  .seq (.block ([.lla .t0 p521Sym] ++ sdAt .s0 .a0 c.mulSave ++ sdAt .s1 .a0 (c.mulSave + 8) ++
    sdAt .ra .a0 (c.mulSave + 16) ++ sdAt .s4 .a0 (c.mulSave + 24) ++ [.addi .s0 .a0 0, .addi .s4 .t0 0])) <|
  .seq (body Impl.P521.p521Comb7Start) <|
  .seq convOut (.block (ldAt .ra .s0 (c.mulSave + 16) ++ ldAt .s4 .s0 (c.mulSave + 24) ++
    ldAt .s1 .s0 (c.mulSave + 8) ++ ldAt .s0 .s0 c.mulSave))

/-- The name of `vg_p521_mul_g`. -/
def mulGP521Name : String := "vg_p521_mul_g"

end VG.Impl.Ecdsa.RISCV64.CombU
