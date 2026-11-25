module

public import VerifiedGarbage.Impl.Ed25519.AArch64.Field

/-!
# Ed25519 and X25519 on AArch64: inversion by divsteps

`[slot 15] = [slot 2]^(p - 2)` (`invert`), `p = 2^255 - 19`: the inverse (zero
for zero) by ten batches of 59 packed divsteps, as the generic inversion of the
Weierstrass curves (`Impl/Weierstrass/AArch64/Inv.lean`), with a batch's update
in registers and the reduction that this modulus has. Nothing depends on the
numbers but through masks and selections.

* `f`, `g`: four words each (two's complement), from `(p, x)`, `x` brought
  into `[0, p)` (`start`).
* `a`, `b`: four words each, below `2^255 + 2^67`, from `(0, 2^-590)`, so that
  after `k` batches `2^590 x a ≡ 2^(59 k) f` and `2^590 x b ≡ 2^(59 k) g`
  modulo `p`, and after ten `x a ≡ f`, which is `±1`: no constant is left to
  multiply by, and `finish` only takes `a` or `2 p - a`.
* A batch runs 59 divsteps on the low words of `f` and `g` in chunks of at
  most 15 (`divsteps59`), whose matrix `(u, v, q, r)` then updates `(f, g)` and
  `(a, b)` (`update`).
* The matrix is biased, `u' = u + 2^59` and so on, so that every product is
  one of unsigned numbers. `u f + v g = (u' f + v' g) - 2^59 (f + g)`, so the
  shift by 59 comes first and the sum `f + g` after it; for `(a, b)` the rows add
  `2^59 (2 p - a - b)`, and the bits of `t` from 255 up are folded by `19` once.

The half of a divstep's `d`, `i = (d - 1) / 2`, is in `x20`: a swap makes it `-i`
and any other step `i + 1`.
-/

@[expose] public section

namespace VG.Impl.Ed25519.AArch64.Divstep
open VG.AArch64

/-! ## The working space

Words at byte offsets of `x0`. -/

def oF : Nat := 192
def oG : Nat := 224
def oA : Nat := 256
def oB : Nat := 288
/-- The sum `f + g`, four words. -/
def oS : Nat := 320
/-- The row that replaces `f` or `a`, until the second row is done. -/
def oT : Nat := 352
/-- `2^59 (2 p - a - b)`, five words. -/
def oE : Nat := 384

def ldp4 (o : Nat) (a b c d : Reg) : List Instr := [.ldp a b .x0 o, .ldp c d .x0 (o + 16)]
def stp4 (o : Nat) (a b c d : Reg) : List Instr := [.stp a b .x0 o, .stp c d .x0 (o + 16)]

/-! ## The divsteps

The low words of `f` and `g` are in `x2` and `x3`, the matrix in `x4`–`x7`.
A chunk of `n ≤ 15` steps has its rows `u P + v Q` in `x8` and `q P + r Q` in
`x9` and `x10` in turn, for `P = f mod 2^15 + 2^31` and `Q = g mod 2^15 + 2^47`,
doubled where `(f, g)` would be halved, and `2^j`, the bit of `g`'s parity at
step `j`, in `x12`. -/

/-- A divstep, from the `g` row in `g` to that in `t`. `ccmp` leaves `pl` for an
odd `g` and `i ≥ 0`, a swap. -/
def stepCode (g t : Reg) : List Instr :=
  [.add .x t g .x8, .sub .x .x11 g .x8, .tst .x g .x12, .cselc .x t t g .ne,
    .ccmp .x .x20 0 8 .ne, .cselc .x t .x11 t .pl, .add .x .x16 g g, .add .x .x8 .x8 .x8,
    .cselc .x .x8 .x16 .x8 .pl, .addImm .x .x13 .x20 1, .csneg .x .x20 .x13 .x20 .mi,
    .add .x .x12 .x12 .x12]

/-- The `g` row's register before step `j`. -/
def gReg (j : Nat) : Reg := if j % 2 = 0 then .x9 else .x10

def stepsCode (n : Nat) : List Instr :=
  (List.range n).flatMap fun j => stepCode (gReg j) (gReg (j + 1))

/-- `x14 = 2^30 + 2^45 + 2^61`, `x15 = 2^15 - 1`, `x17 = 2^14`. -/
def consts : List Instr :=
  [.movz .x .x14 0x4000 1, .movk .x .x14 0x2000 2, .movk .x .x14 0x2000 3, .movz .x .x15 0x7fff 0,
    .movz .x .x17 0x4000 0]

/-- The rows' start: `x8 = x2 mod 2^15 + 2^31`, `x9 = x3 mod 2^15 + 2^47`. -/
def rowsStart : List Instr :=
  [.logic .and .x .x8 .x2 .x15, .logic .and .x .x9 .x3 .x15, .movk .x .x8 0x8000 1,
    .movk .x .x9 0x8000 2, .movz .x .x12 1 0]

/-- A row's entries, from the row in `w`: that at bit 31 into `l`, that at bit 47
into `h`. -/
def entries (w l h : Reg) : List Instr :=
  [.add .x w w .x14, .lsr .x h w 47, .lsl .x l w 17, .lsr .x l l 48, .sub .x h h .x17,
    .sub .x l l .x17]

/-- `x2 = (u x2 + v x3) >> n`, `x3 = (q x2 + r x3) >> n`. -/
def lows (n : Nat) (u v q r : Reg) : List Instr :=
  [.mul .x .x13 .x2 u, .mul .x .x16 .x2 q, .madd .x .x2 .x3 v .x13, .madd .x .x3 .x3 r .x16,
    .lsr .x .x2 .x2 n, .lsr .x .x3 .x3 n]

/-- `(y, z) = (u y + v z, q y + r z)`. -/
def column (u v q r y z : Reg) : List Instr :=
  [.mul .x .x13 u y, .mul .x .x16 q y, .madd .x y v z .x13, .madd .x z r z .x16]

/-- The batch's matrix times the chunk's. -/
def compose (u v q r : Reg) : List Instr := column u v q r .x4 .x6 ++ column u v q r .x5 .x7

/-- A batch's first chunk, of 15 steps: its matrix is the batch's so far. -/
def chunk0 : List Instr :=
  rowsStart ++ stepsCode 15 ++ entries .x8 .x4 .x5 ++ entries .x10 .x6 .x7 ++ lows 15 .x4 .x5 .x6 .x7

/-- A further chunk of 15 steps. -/
def chunk15 : List Instr :=
  rowsStart ++ stepsCode 15 ++ entries .x8 .x8 .x11 ++ entries .x10 .x10 .x9 ++
    lows 15 .x8 .x11 .x10 .x9 ++ compose .x8 .x11 .x10 .x9

/-- The last chunk, of 14 steps. -/
def chunk14 : List Instr :=
  rowsStart ++ stepsCode 14 ++ entries .x8 .x8 .x11 ++ entries .x9 .x9 .x10 ++
    compose .x8 .x11 .x9 .x10

/-- A batch's divsteps. -/
def divsteps59 : List Instr := consts ++ chunk0 ++ chunk15 ++ chunk15 ++ chunk14

/-! ## The update

The biased matrix is in `x4`–`x7`, the row in `x2`, `x3`, `x8`–`x10`, an
operand in `x11`–`x14`, and `x16 = 0`. -/

/-- The matrix plus `2^59`, and `x16 = 0`. -/
def bias : List Instr :=
  [.movz .x .x16 0x0800 3, .add .x .x4 .x4 .x16, .add .x .x5 .x5 .x16, .add .x .x6 .x6 .x16,
    .add .x .x7 .x7 .x16, .movz .x .x16 0 0]

/-- The row is `u` times the operand. -/
def mulFirst (u : Reg) : List Instr :=
  [.mul .x .x2 u .x11, .umulh .x3 u .x11, .mul .x .x15 u .x12, .adds .x .x3 .x3 .x15,
    .umulh .x8 u .x12, .mul .x .x15 u .x13, .adcs .x .x8 .x8 .x15,
    .umulh .x9 u .x13, .mul .x .x15 u .x14, .adcs .x .x9 .x9 .x15,
    .umulh .x10 u .x14, .adc .x .x10 .x10 .x16]

/-- The row plus `v` times the operand. -/
def mulAcc (v : Reg) : List Instr :=
  [.mul .x .x15 v .x11, .adds .x .x2 .x2 .x15, .mul .x .x15 v .x12, .adcs .x .x3 .x3 .x15,
    .mul .x .x15 v .x13, .adcs .x .x8 .x8 .x15, .mul .x .x15 v .x14, .adcs .x .x9 .x9 .x15,
    .adc .x .x10 .x10 .x16,
    .umulh .x15 v .x11, .adds .x .x3 .x3 .x15, .umulh .x15 v .x12, .adcs .x .x8 .x8 .x15,
    .umulh .x15 v .x13, .adcs .x .x9 .x9 .x15, .umulh .x15 v .x14, .adc .x .x10 .x10 .x15]

/-- The row less `2^256 u` for a negative operand. -/
def signed (u : Reg) : List Instr :=
  [.tst .x .x14 .x14, .cselc .x .x15 u .x16 .mi, .sub .x .x10 .x10 .x15]

/-- The row's four low words plus the operand. -/
def addOpd : List Instr :=
  [.adds .x .x2 .x2 .x11, .adcs .x .x3 .x3 .x12, .adcs .x .x8 .x8 .x13, .adc .x .x9 .x9 .x14]

/-- The row's four low words less the operand. -/
def subOpd : List Instr :=
  [.subs .x .x2 .x2 .x11, .sbcs .x .x3 .x3 .x12, .sbcs .x .x8 .x8 .x13, .sbc .x .x9 .x9 .x14]

/-- The row over `2^59`. -/
def shift : List Instr :=
  [.extr .x .x2 .x3 .x2 59, .extr .x .x3 .x8 .x3 59, .extr .x .x8 .x9 .x8 59, .extr .x .x9 .x10 .x9 59]

/-- `[oS] = f + g`. -/
def sumFG : List Instr :=
  ldp4 oF .x2 .x3 .x8 .x9 ++ ldp4 oG .x11 .x12 .x13 .x14 ++ addOpd ++ stp4 oS .x2 .x3 .x8 .x9

/-- `[o] = (u f + v g) / 2^59`, for the biased `u` and `v`. -/
def rowFG (u v : Reg) (o : Nat) : List Instr :=
  ldp4 oF .x11 .x12 .x13 .x14 ++ mulFirst u ++ signed u ++ ldp4 oG .x11 .x12 .x13 .x14 ++ mulAcc v ++
    signed v ++ ldp4 oS .x11 .x12 .x13 .x14 ++ shift ++ subOpd ++ stp4 o .x2 .x3 .x8 .x9

def copy4 (d s : Nat) : List Instr := ldp4 s .x11 .x12 .x13 .x14 ++ stp4 d .x11 .x12 .x13 .x14

/-- The words of `2 p`: the lowest in `x15`, the others in `x17`. -/
def twoP : List Instr := [.movz .x .x17 38 0, .sub .x .x15 .x16 .x17, .subImm .x .x17 .x16 1]

/-- `2 p` less the row's four low words. -/
def negRow : List Instr :=
  [.subs .x .x2 .x15 .x2, .sbcs .x .x3 .x17 .x3, .sbcs .x .x8 .x17 .x8, .sbcs .x .x9 .x17 .x9]

/-- The five words of `2^59` times the row's four low words less the operand, into
`x11`–`x15`, and `x17 = 19`. -/
def subShift : List Instr :=
  [.subs .x .x2 .x2 .x11, .sbcs .x .x3 .x3 .x12, .sbcs .x .x8 .x8 .x13, .sbcs .x .x9 .x9 .x14,
    .sbc .x .x10 .x16 .x16,
    .lsl .x .x11 .x2 59, .extr .x .x12 .x3 .x2 5, .extr .x .x13 .x8 .x3 5, .extr .x .x14 .x9 .x8 5,
    .extr .x .x15 .x10 .x9 5, .movz .x .x17 19 0]

/-- `[oE] = 2^59 (2 p - a - b)`, and `x17 = 19`. -/
def offsetAB : List Instr :=
  ldp4 oA .x2 .x3 .x8 .x9 ++ ldp4 oB .x11 .x12 .x13 .x14 ++ twoP ++ negRow ++ subShift ++
    stp4 oE .x11 .x12 .x13 .x14 ++ ([st .x15 (oE + 32)] : List Instr)

/-- The row plus the five words of `x11`–`x15`, its bits from 255 up folded by `x17 = 19`. -/
def fold : List Instr :=
  [.adds .x .x2 .x2 .x11, .adcs .x .x3 .x3 .x12, .adcs .x .x8 .x8 .x13, .adcs .x .x9 .x9 .x14,
    .adc .x .x10 .x10 .x15,
    .adds .x .x9 .x9 .x9, .adc .x .x10 .x10 .x10, .lsr .x .x9 .x9 1,
    .mul .x .x11 .x10 .x17, .umulh .x12 .x10 .x17,
    .adds .x .x2 .x2 .x11, .adcs .x .x3 .x3 .x12, .adcs .x .x8 .x8 .x16, .adc .x .x9 .x9 .x16]

/-- `[o] ≡ u a + v b`, for the biased `u` and `v`. -/
def rowAB (u v : Reg) (o : Nat) : List Instr :=
  ldp4 oA .x11 .x12 .x13 .x14 ++ mulFirst u ++ ldp4 oB .x11 .x12 .x13 .x14 ++ mulAcc v ++
    ldp4 oE .x11 .x12 .x13 .x14 ++ ([ld .x15 (oE + 32)] : List Instr) ++ fold ++ stp4 o .x2 .x3 .x8 .x9

def updateFG : List Instr :=
  sumFG ++ rowFG .x4 .x5 oT ++ rowFG .x6 .x7 oG ++ copy4 oF oT

def updateAB : List Instr :=
  offsetAB ++ rowAB .x4 .x5 oT ++ rowAB .x6 .x7 oB ++ copy4 oA oT

def batchStart : List Instr := [.subImm .x .x19 .x19 1, ld .x2 oF, ld .x3 oG]

def batch : List Instr := batchStart ++ divsteps59 ++ bias ++ updateFG ++ updateAB

/-! ## The ends -/

/-- `2^-590` modulo `p`, `b`'s start. -/
def b0 : Nat := 0x276508b2417706156c6c893805ac5242a8c68f3f1d132595a0f99e2375022099

/-- `[o] = v`, four words. -/
def set4 (o v : Nat) : List Instr :=
  const64 .x2 (BitVec.ofNat 64 v) ++ const64 .x3 (BitVec.ofNat 64 (v / 2 ^ 64)) ++
    const64 .x8 (BitVec.ofNat 64 (v / 2 ^ 128)) ++ const64 .x9 (BitVec.ofNat 64 (v / 2 ^ 192)) ++
    stp4 o .x2 .x3 .x8 .x9

/-- The input's top bit folded by `19`, `x17 = 19` and `x16 = 0`. -/
def foldTop : List Instr :=
  [.movz .x .x16 0 0, .movz .x .x17 19 0, .adds .x .x9 .x9 .x9, .lsr .x .x9 .x9 1,
    .csel .x .x11 .x17 .x16, .adds .x .x2 .x2 .x11, .adcs .x .x3 .x3 .x16, .adcs .x .x8 .x8 .x16,
    .adc .x .x9 .x9 .x16]

/-- The operand is the row's four low words plus `19`. -/
def plus19 : List Instr :=
  [.adds .x .x11 .x2 .x17, .adcs .x .x12 .x3 .x16, .adcs .x .x13 .x8 .x16, .adc .x .x14 .x9 .x16]

/-- The operand less `2^255` if that is not negative, else the row: `y - p` for `y ≥ p`
from `y + 19`. -/
def reduceOnce : List Instr :=
  [.tst .x .x14 .x14, .add .x .x14 .x14 .x14, .lsr .x .x14 .x14 1,
    .cselc .x .x2 .x11 .x2 .mi, .cselc .x .x3 .x12 .x3 .mi, .cselc .x .x8 .x13 .x8 .mi,
    .cselc .x .x9 .x14 .x9 .mi]

/-- `i = 0`, and ten batches. -/
def counters : List Instr := [.movz .x .x20 0 0, .movz .x .x19 10 0]

def start : List Instr :=
  set4 oF Spec.X25519.P ++ set4 oA 0 ++ set4 oB b0 ++
    ldp4 128 .x2 .x3 .x8 .x9 ++ foldTop ++ plus19 ++ reduceOnce ++ stp4 oG .x2 .x3 .x8 .x9 ++ counters

/-- The row's four low words for a negative `x10`, else the operand. -/
def bySign : List Instr :=
  [.tst .x .x10 .x10, .cselc .x .x2 .x2 .x11 .mi, .cselc .x .x3 .x3 .x12 .mi, .cselc .x .x8 .x8 .x13 .mi,
    .cselc .x .x9 .x9 .x14 .mi]

/-- `[slot 15] = a`, or `2 p - a` for a negative `f`. -/
def finish : List Instr :=
  ldp4 oA .x2 .x3 .x8 .x9 ++ ldp4 oA .x11 .x12 .x13 .x14 ++ ([ld .x10 (oF + 24)] : List Instr) ++
    ([.movz .x .x16 0 0] : List Instr) ++ twoP ++ negRow ++ bySign ++ stores (offset 15) .x2 .x3 .x8 .x9

/-- `[slot 15] = [slot 2]^(p - 2)`. -/
def invert : Prog isa :=
  .seq (.block start) (.seq (.loop (.block batch) (.nonzero .x .x19)) (.block finish))

end VG.Impl.Ed25519.AArch64.Divstep
