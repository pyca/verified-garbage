module

public import VerifiedGarbage.Impl.Weierstrass.RISCV64.GenWide
public import VerifiedGarbage.Impl.Words.RISCV64.Word64
public import VerifiedGarbage.Impl.Words.RISCV64.Sched

/-!
# Montgomery's multiplication by rows, in registers, on RISC-V

`[t2] = [t4] [t5] R⁻¹ mod m` for a modulus of `k` words known when the code is
generated (`fast`), with `[t4]`, the running value and the modulus in
registers, which a `Lay` names, `a3` the base of the function's own working
space:

1. the callee-saved registers the layout uses are kept (`save`);
2. the product's `2 k` words: of `[t4]` and `[t5]` by rows (`mulProd`), or,
   when the pointers are equal, the square (`sqrProd`): the products `aᵢ aⱼ`,
   `i < j`, by rows, then doubled with the squares added (`diag`). A row's
   words are in `V`, and its carry in `C`;
3. Montgomery's reduction of the product (`red`), separated operand scanning:
   the window of `k` words in `V`, the modulus's words in `A` and `m'` in
   `NI`; round `i`'s quotient word replaces word `i` in its register, which
   word `i + k` then takes;
4. the final subtraction (`csub`): the window less the modulus, in `A`, and
   that or the window by a mask, into `[t2]`;
5. the registers back (`restore`).

A step of a row (`mac`) multiplies once by `mul` and once by `mulhu`, through
the layout's temporaries in turn, so that the steps of a row are independent
but for the carry: the code is written a step after the other, and emitted in
an order (`Impl/Words/RISCV64/Sched.lean`) that begins the products of the
next steps before the sums of this one, for an in-order issue of two
operations a cycle whose products take four. Every selection is a mask, and
the only branch is on the pointers, which are public, as every address is a
pointer plus a constant.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.RISCV64.Rows

open VG.RISCV64
open VG.Impl.Weierstrass.RISCV64.GenWide (wordOf negInv)
open VG.Impl.Words.RISCV64 (li64 sched)

/-- The number of words, and the registers: the running value's words, an
operand's or the modulus's words, the temporaries of a step, in turn, and the
registers kept; and where, from `a3`, these and the product are. -/
structure Lay where
  k : Nat
  VL : List Reg
  AL : List Reg
  LO : List Reg
  HI : List Reg
  KR : List Reg
  sv : Nat
  pp : Nat

/-- The carry word of a row. -/
abbrev C : Reg := .t3

/-- The word of `[t5]` a row multiplies by, and the carry out of the reduction's window. -/
abbrev Y : Reg := .t4
abbrev TOP : Reg := .t4

/-- `m'`, in the reduction. -/
abbrev NI : Reg := .t5

namespace Lay

variable (L : Lay)

/-- The register of word `i` of the running value. -/
def V (i : Nat) : Reg := L.VL.getD (i % L.k) .t0

/-- The register of word `j` of `[t4]` or of the modulus. -/
def A (j : Nat) : Reg := L.AL.getD j .a0

/-- The temporaries of step `j`. -/
def lo (j : Nat) : Reg := L.LO.getD (j % L.LO.length) .t6
def hi (j : Nat) : Reg := L.HI.getD (j % L.HI.length) .s11

/-- The product's word `j`. -/
abbrev P (j : Nat) : Nat := L.pp + 8 * j

end Lay

/-! ## Rows -/

/-- `v + 2⁶⁴ C := x y + v + C`, or without `v` (`acc` false). -/
def mac (acc : Bool) (lo hi x y v : Reg) : List Instr :=
  if acc then
    [.mul lo x y, .mulhu hi x y, .add v v lo, .sltu lo v lo, .add lo hi lo, .add v v C, .sltu hi v C, .add C lo hi]
  else [.mul v x y, .mulhu hi x y, .add v v C, .sltu lo v C, .add C hi lo]

/-- `mac` without the carry in. -/
def mac1 (acc : Bool) (lo x y v : Reg) : List Instr :=
  if acc then [.mul lo x y, .mulhu C x y, .add v v lo, .sltu lo v lo, .add C C lo]
  else [.mul v x y, .mulhu C x y]

variable (L : Lay)

/-- The words `V i …` plus `y` times the `n` words `x`, with the carry `C` in and out. -/
def row (acc : Bool) (x : Nat → Reg) (y : Reg) (i n : Nat) : List Instr :=
  (List.range n).flatMap fun j => mac acc (L.lo j) (L.hi j) (x j) y (L.V (i + j))

/-- `row` of `n + 1` words without the carry in. -/
def row1 (acc : Bool) (x : Nat → Reg) (y : Reg) (i n : Nat) : List Instr :=
  mac1 acc (L.lo 0) (x 0) y (L.V i) ++ row L acc (fun j => x (j + 1)) y (i + 1) n

/-! ## The products -/

/-- The words of `[t4]` into `A`. -/
def loadA : List Instr := (List.range L.k).flatMap fun j => [.load .d (L.A j) .t4 (8 * j)]

/-- Row `i` of the product: its low word stored. -/
def mulRow (i : Nat) : List Instr :=
  [.load .d Y .t5 (8 * i)] ++ row1 L (decide (0 < i)) L.A Y i (L.k - 1) ++
    [.store .d (L.V i) .a3 (L.P i), .addi (L.V i) C 0]

/-- The product of `[t4]` and `[t5]`. -/
def mulProd : List Instr :=
  loadA L ++ ((List.range L.k).flatMap (mulRow L) ++
    (List.range L.k).flatMap fun j => [.store .d (L.V (L.k + j)) .a3 (L.P (L.k + j))])

/-- Row `i` of the square's products `aᵢ aⱼ`, `i < j`: its two low words stored. -/
def sqrRow (i : Nat) : List Instr :=
  row1 L (decide (0 < i)) (fun j => L.A (i + 1 + j)) (L.A i) (2 * i + 1) (L.k - 2 - i) ++
    [.addi (L.V (i + L.k)) C 0, .store .d (L.V (2 * i + 1)) .a3 (L.P (2 * i + 1)),
      .store .d (L.V (2 * i + 2)) .a3 (L.P (2 * i + 2))]

/-- The register of the bit doubling carries into word `j`. -/
def bit (j : Nat) : Reg := if j % 2 = 0 then .t4 else .t5

/-- Word `j` of the product doubled, plus `h` and the carry `C`, in and out. -/
def dword (j : Nat) (w h : Reg) : List Instr :=
  [.load .d w .a3 (L.P j), .shift .srl .d (bit (j + 1)) w 63, .shift .sll .d w w 1, .add w w (bit j),
    .add w w h, .sltu h w h, .add w w C, .sltu C w C, .add C C h, .store .d w .a3 (L.P j)]

/-- Words `2 i` and `2 i + 1` of the product doubled, plus `aᵢ²`. -/
def diag (i : Nat) : List Instr :=
  [.mul (L.V (4 * i)) (L.A i) (L.A i), .mulhu (L.V (4 * i + 1)) (L.A i) (L.A i)] ++
    (dword L (2 * i) (L.V (4 * i + 2)) (L.V (4 * i)) ++ dword L (2 * i + 1) (L.V (4 * i + 3)) (L.V (4 * i + 1)))

/-- The square of `[t4]`. -/
def sqrProd : List Instr :=
  loadA L ++ ((List.range (L.k - 1)).flatMap (sqrRow L) ++
    ([.li C 0, .li .t4 0, .store .d C .a3 (L.P 0), .store .d C .a3 (L.P (2 * L.k - 1))] ++
      (List.range L.k).flatMap (diag L)))

/-! ## The reduction -/

variable (m : Nat)

/-- The modulus's words and `m'`. -/
def consts : List Instr :=
  ((List.range L.k).flatMap fun j => li64 (L.A j) (L.lo j) (wordOf m j)) ++
    li64 NI (L.lo L.k) (BitVec.ofNat 64 (negInv m))

/-- The quotient word of `V i`, in place, and the carry word of adding its
product with the modulus's word 0, in `C`. -/
def quot (i : Nat) : List Instr :=
  [.mul (L.V i) (L.V i) NI, .mulhu C (L.V i) (L.A 0), .li (L.lo 0) 0, .sltu (L.lo 0) (L.lo 0) (L.V i), .add C C (L.lo 0)]

/-- Word `i + k` of the product plus the carries `C` and `TOP`, into `V i`, the carry out in `TOP`. -/
def top (i : Nat) : List Instr :=
  [.load .d (L.V i) .a3 (L.P (L.k + i)), .add (L.V i) (L.V i) C, .sltu (L.lo 0) (L.V i) C, .add (L.V i) (L.V i) TOP,
    .sltu TOP (L.V i) TOP, .add TOP TOP (L.lo 0)]

/-- Round `i`. -/
def redRound (i : Nat) : List Instr :=
  quot L i ++ (row L true (fun j => L.A (j + 1)) (L.V i) (i + 1) (L.k - 1) ++ top L i)

/-- The product reduced, into `V 0 …` and `TOP`. -/
def red : List Instr :=
  ((List.range L.k).flatMap fun j => [.load .d (L.V j) .a3 (L.P j)]) ++ ([.li TOP 0] ++ (List.range L.k).flatMap (redRound L))

/-! ## The final subtraction -/

/-- Word `j` of the window less the modulus, with the borrow in `C`, in `A j`. -/
def subStep (j : Nat) : List Instr :=
  [.sltu (L.lo j) (L.V j) (L.A j), .sub (L.A j) (L.V j) (L.A j), .sltu (L.hi j) (L.A j) C, .sub (L.A j) (L.A j) C,
    .add C (L.lo j) (L.hi j)]

/-- Word `j` of the result: the difference's, or the window's under the mask `TOP`. -/
def selStep (j : Nat) : List Instr :=
  [.logic .xor (L.V j) (L.V j) (L.A j), .logic .and (L.V j) (L.V j) TOP, .logic .xor (L.V j) (L.V j) (L.A j),
    .store .d (L.V j) .t2 (8 * j)]

/-- The window and `TOP`, below twice the modulus, reduced into `[t2]`. -/
def csub : List Instr :=
  [.li C 0] ++ ((List.range L.k).flatMap (subStep L) ++ ([.sub TOP TOP C] ++ (List.range L.k).flatMap (selStep L)))

/-! ## The multiplication -/

/-- The registers kept, and back. -/
def save : List Instr := (List.range L.KR.length).flatMap fun j => [.store .d (L.KR.getD j .s6) .a3 (L.sv + 8 * j)]

def restore : List Instr := (List.range L.KR.length).flatMap fun j => [.load .d (L.KR.getD j .s6) .a3 (L.sv + 8 * j)]

/-- The constants, the reduction and the final subtraction. -/
def tail : List Instr := consts L m ++ (red L ++ csub L)

/-- The orders of the product's code, the square's and the rest's. -/
structure Order where
  mul : List Nat
  sqr : List Nat
  tail : List Nat

/-- `[t2] = [t4] [t5] R⁻¹ mod m`, for `tail` that reduces the product. -/
def fastWith (tail : List Instr) (o : Order) : Prog isa :=
  .seq (.block (save L)) <|
    .seq (.ite (.eq .t4 .t5) (.block (sched o.sqr (sqrProd L))) (.block (sched o.mul (mulProd L)))) <|
      .seq (.block (sched o.tail tail)) (.block (restore L))

/-- `[t2] = [t4] [t5] R⁻¹ mod m`. -/
def fast (o : Order) : Prog isa := fastWith L (tail L m) o

end VG.Impl.Weierstrass.RISCV64.Rows
