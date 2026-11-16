module

public import VerifiedGarbage.Impl.X25519.PPC64LE

/-!
# X25519: PPC64LE implementation, five 51-bit limbs

`vg_x25519(out = r3, scalar = r4, point = r5, scratch = r6)`.

A field element is 40 bytes of the working space, five doublewords
`l0 + 2⁵¹ l1 + 2¹⁰² l2 + 2¹⁵³ l3 + 2²⁰⁴ l4`, each below `2⁵¹ + 2¹⁸`, standing
for its residue modulo `p = 2²⁵⁵ - 19`. The ladder and the inversion use no
instruction that reads or writes XER's carry: a product of limbs is taken
with both operands shifted left, by 13 bits together, so that `mulhdu` gives
the product shifted right by 51 and `mulld`, shifted right by 13, its low 51
bits (`term`), and the sums of five of each fit in a doubleword.

* `terms`: the products of a list, each added to its column's two sums
  (`lo k` and `hi k`: `r7`–`r11` and `r28`–`r31`, `r5`), the first of a
  column written to them;
* `tail`: the five columns `lo k + 2⁵¹ hi k` reduced to an element: `hi k`
  added to `lo (k + 1)`, the top one folded in as 19 times its two halves,
  then every limb's bits from 51 up added to the next limb, those of the
  top limb to the lowest as 19 times them, all at once, so that no limb
  waits for the one below;
* `mulCore`, `sqrCore`: the product of the elements whose limbs are in
  `ra` (`r14`–`r18`) and `rb` (`r19`–`r23`), and the square of the one in
  `ra`, any limbs below `2⁵³`;
* the operations of the ladder, each a product or a square of sums and
  differences of elements, which it takes from the working space into `ra`
  and `rb` (`ldAdd`, `ldSub`, `ldSel`): a difference is `a + 2p - b`, limb by
  limb.

A load of what was just stored is slow on POWER, so an operation computes
the sums and differences it multiplies rather than read them back, the
ladder's conditional swap is a selection of what it squares (`sqrSel`: the
other products of an iteration are symmetric in the two points), and the
operations of an iteration are in an order in which none but its first reads
what the one before it wrote. The squarings of the inversion take their
operand from the registers the one before left it in (`sqrL`).

`x25519` decodes the u-coordinate and expands the scalar as
`Impl.X25519.PPC64LE`'s code does (`setup`, `bits`), takes the limbs from the
four words (`unpack`), and gives the result back in four words (`pack`) to
that code's final reduction (`freeze`). It saves `r14`–`r31` in the working
space, around all but those.
-/

@[expose] public section

namespace VG.Impl.X25519.PPC64LE.Fe51

open VG.PPC64LE

/-! ## The layout of the working space

The elements are above what `Impl.X25519.PPC64LE`'s code uses: its
elements of four words (`U`, `O`), `Y`, `BITS` and the saved registers. -/

/-- The decoded u-coordinate, in four words. -/
abbrev U : Nat := Impl.X25519.PPC64LE.X1
/-- The result, in four words. -/
abbrev O : Nat := Impl.X25519.PPC64LE.X2

def X1 : Nat := 1088
def X2 : Nat := 1128
def Z2 : Nat := 1168
def X3 : Nat := 1208
def Z3 : Nat := 1248
def AA : Nat := 1288
def BB : Nat := 1328
def DA : Nat := 1368
def CB : Nat := 1408
def T : Nat := 1448
def G : Nat := 1488
def A : Nat := 1528
def B : Nat := 1568
def C : Nat := 1608
def D : Nat := 1648
def R : Nat := 1688

/-! ## Registers -/

/-- Limb `i` of the first operand, `r14`–`r18`. -/
def ra (i : Nat) : Reg := [Reg.r14, .r15, .r16, .r17].getD i .r18

/-- Limb `j` of the second operand, `r19`–`r23`. -/
def rb (j : Nat) : Reg := [Reg.r19, .r20, .r21, .r22].getD j .r23

/-- 19 times limb `j` of the second operand, `r24`–`r27` for `j` from 1. -/
def rn (j : Nat) : Reg := [Reg.r24, .r24, .r25, .r26].getD j .r27

/-- The sum of the low 51 bits of column `k`'s products, `r7`–`r11`. -/
def lo (k : Nat) : Reg := [Reg.r7, .r8, .r9, .r10].getD k .r11

/-- The sum of the bits from 51 up of column `k`'s products. -/
def hi (k : Nat) : Reg := [Reg.r28, .r29, .r30, .r31].getD k .r5

/-! ## Products -/

/-- The product of `x` and `y`, which hold limbs shifted left by 13 bits
together, into column `k`: its low 51 bits to `lo k` and the others to
`hi k`, which it writes if the product is the column's first. -/
def term (first : Bool) (x y : Reg) (k : Nat) : List Instr :=
  if first then [.mul .r4 x y, .lsr .d (lo k) .r4 13, .mulhu (hi k) x y]
  else [.mul .r4 x y, .lsr .d .r4 .r4 13, .add (lo k) (lo k) .r4, .mulhu .r4 x y,
    .add (hi k) (hi k) .r4]

/-- A product: whether it is its column's first, its registers and its column. -/
abbrev Term : Type := Bool × Reg × Reg × Nat

def terms (ts : List Term) : List Instr := ts.flatMap fun t => term t.1 t.2.1 t.2.2.1 t.2.2.2

/-- `2⁵¹ - 1` into `r4`. -/
def mask51 : List Instr := [.li .r4 1, .lsl .r4 .r4 51, .subi .r4 .r4 1]

/-- The bits from 51 up of limb `k`, `r16`–`r20`. -/
def cy (k : Nat) : Reg := [Reg.r16, .r17, .r18, .r19].getD k .r20

/-- The limbs in `rs` stored at `o`. -/
def stores (rs : Nat → Reg) (o : Nat) : List Instr := (List.range 5).map fun k => .store .d (rs k) .r6 (o + 8 * k)

/-- The columns `lo k + 2⁵¹ hi k` reduced to the element at `o`, which it
leaves in `lo` too. -/
def tail (o : Nat) : List Instr :=
  (List.range 4).map (fun k => .add (lo (k + 1)) (lo (k + 1)) (hi k)) ++ mask51 ++
  [.li .r15 19, .logic .and .r14 .r5 .r4, .lsr .d .r5 .r5 51, .mul .r14 .r14 .r15, .mul .r5 .r5 .r15,
    .add .r7 .r7 .r14, .add .r8 .r8 .r5] ++
  (List.range 5).map (fun k => .lsr .d (cy k) (lo k) 51) ++
  (List.range 5).map (fun k => .logic .and (lo k) (lo k) .r4) ++
  [.mul .r20 .r20 .r15, .add .r7 .r7 .r20] ++
  (List.range 4).map (fun k => .add (lo (k + 1)) (lo (k + 1)) (cy k)) ++ stores lo o

/-- The products of a multiplication: column `k` has `a_i b_j` for
`i + j = k`, and 19 times it for `i + j = k + 5`. -/
def mulTerms : List Term :=
  (List.range 5).flatMap fun k => (List.range 5).map fun i =>
    (i == 0, ra i, if i ≤ k then rb (k - i) else rn (k + 5 - i), k)

/-- The product of the elements in `ra` and `rb`, at `o`. -/
def mulCore (o : Nat) : List Instr :=
  (List.range 5).map (fun i => .lsl (ra i) (ra i) 8) ++
  (List.range 5).map (fun j => .lsl (rb j) (rb j) 5) ++ [.li .r5 19] ++
  (List.range 4).map (fun j => .mul (rn (j + 1)) (rb (j + 1)) .r5) ++ terms mulTerms ++ tail o

/-- The square of the element in `ra`, at `o`: `a0` times the others, with
`a0` doubled; then `a1`'s products, `a2`'s, `a3`'s and `a4`'s, each with the
forms of the limbs it needs (doubled in `ra`; halved in `r19`; times 19 in
`r22` and `r23`). -/
def sqrCore (o : Nat) : List Instr :=
  [.lsl .r19 .r14 4, .lsl .r14 .r14 9, .lsl .r20 .r15 5, .lsl .r21 .r16 5, .lsl .r22 .r17 5,
    .lsl .r23 .r18 5] ++
  terms [(true, .r14, .r19, 0), (true, .r14, .r20, 1), (true, .r14, .r21, 2), (true, .r14, .r22, 3),
    (true, .r14, .r23, 4)] ++
  [.lsl .r19 .r15 4, .lsl .r15 .r15 9, .li .r24 19, .mul .r23 .r23 .r24] ++
  terms [(false, .r15, .r19, 2), (false, .r15, .r21, 3), (false, .r15, .r22, 4), (false, .r15, .r23, 0)] ++
  [.lsl .r19 .r16 4, .lsl .r16 .r16 9, .mul .r22 .r22 .r24] ++
  terms [(false, .r16, .r19, 4), (false, .r16, .r22, 0), (false, .r16, .r23, 1)] ++
  [.lsl .r17 .r17 8] ++ terms [(false, .r17, .r22, 1)] ++
  [.lsl .r17 .r17 1] ++ terms [(false, .r17, .r23, 2)] ++
  [.lsl .r18 .r18 8] ++ terms [(false, .r18, .r23, 3)] ++ tail o

/-! ## Operands -/

/-- The limbs of `2p`, for a difference: `2⁵² - 38` into `r9` and `2⁵² - 2`
into `r5`. -/
def subConsts : List Instr := [.li .r5 1, .lsl .r5 .r5 52, .subi .r9 .r5 38, .subi .r5 .r5 2]

/-- Limb `k` of `2p`. -/
def twoP (k : Nat) : Reg := if k = 0 then .r9 else .r5

/-- `[a]` into `rs`. -/
def ldV (rs : Nat → Reg) (a : Nat) : List Instr := (List.range 5).map fun k => .load .d (rs k) .r6 (a + 8 * k)

/-- `[a] + [b]` into `rs`. -/
def ldAdd (rs : Nat → Reg) (a b : Nat) : List Instr :=
  (List.range 5).flatMap fun k =>
    [.load .d (rs k) .r6 (a + 8 * k), .load .d .r8 .r6 (b + 8 * k), .add (rs k) (rs k) .r8]

/-- `[a] + 2p - [b]` into `rs`, after `subConsts`. -/
def ldSub (rs : Nat → Reg) (a b : Nat) : List Instr :=
  (List.range 5).flatMap fun k =>
    [.load .d (rs k) .r6 (a + 8 * k), .load .d .r8 .r6 (b + 8 * k), .add (rs k) (rs k) (twoP k),
      .sub (rs k) (rs k) .r8]

/-- Limb `k` of `[a] ± [b]`, or of `[c] ± [d]` if the mask `r4` is all
ones, into `ra k`. -/
def selStep (sub : Bool) (a b c d k : Nat) : List Instr :=
  [.load .d .r7 .r6 (a + 8 * k), .load .d .r8 .r6 (b + 8 * k)] ++
  (if sub then [.add .r7 .r7 (twoP k), .sub .r7 .r7 .r8] else [.add .r7 .r7 .r8]) ++
  [.load .d .r10 .r6 (c + 8 * k), .load .d .r8 .r6 (d + 8 * k)] ++
  (if sub then [.add .r10 .r10 (twoP k), .sub .r10 .r10 .r8] else [.add .r10 .r10 .r8]) ++
  [.logic .xor .r10 .r10 .r7, .logic .and .r10 .r10 .r4, .logic .xor (ra k) .r7 .r10]

/-- `[a] ± [b]`, or `[c] ± [d]` if `swap` (`r0`) is 1, into `ra`. -/
def ldSel (sub : Bool) (a b c d : Nat) : List Instr :=
  [.li .r4 0, .sub .r4 .r4 .r0] ++ (if sub then subConsts else []) ++
    (List.range 5).flatMap (selStep sub a b c d)

/-! ## Field operations -/

/-- `[o] = [a] · [b]`. -/
def mul (o a b : Nat) : List Instr := ldV ra a ++ ldV rb b ++ mulCore o

/-- `[o] = [a]²`. -/
def sqr (o a : Nat) : List Instr := ldV ra a ++ sqrCore o

/-- `[o]` is the square of the element in `lo`, which the operation before
left there. -/
def sqrL (o : Nat) : List Instr := (List.range 5).map (fun k => .logic .or (ra k) (lo k) (lo k)) ++ sqrCore o

/-- `[o] = ([a] - [b]) · ([c] + [d])`. -/
def mulDS (o a b c d : Nat) : List Instr := subConsts ++ ldSub ra a b ++ ldAdd rb c d ++ mulCore o

/-- `[o] = ([a] - [b]) · [c]`. -/
def mulSub (o a b c : Nat) : List Instr := subConsts ++ ldSub ra a b ++ ldV rb c ++ mulCore o

/-- `[o] = ([a] + [b])²`. -/
def sqrAdd (o a b : Nat) : List Instr := ldAdd ra a b ++ sqrCore o

/-- `[o] = ([a] - [b])²`. -/
def sqrSub (o a b : Nat) : List Instr := subConsts ++ ldSub ra a b ++ sqrCore o

/-- `[o] = ([a] ± [b])²`, or `([c] ± [d])²` if `swap` (`r0`) is 1. -/
def sqrSel (o : Nat) (sub : Bool) (a b c d : Nat) : List Instr := ldSel sub a b c d ++ sqrCore o

/-- Limb `k` of `[a]` into `rb k` and of `[a] + 2p - [b]`, shifted left by
11, into `ra k`. -/
def a24Step (a b k : Nat) : List Instr :=
  [.load .d (rb k) .r6 (a + 8 * k), .load .d .r8 .r6 (b + 8 * k), .add (ra k) (rb k) (twoP k),
    .sub (ra k) (ra k) .r8, .lsl (ra k) (ra k) 11]

/-- `[o] = [a] + 121665 · ([a] - [b])` (`a24 = 121665 = 2¹⁶ + 0xdb41`, in
`r24` shifted left by 2). -/
def addA24 (o a b : Nat) : List Instr :=
  subConsts ++ (List.range 5).flatMap (a24Step a b) ++
  [.lis .r24 1, .ori .r24 .r24 0xdb41, .lsl .r24 .r24 2] ++
  terms ((List.range 5).map fun k => (true, ra k, .r24, k)) ++
  (List.range 5).map (fun k => .add (lo k) (lo k) (rb k)) ++ tail o

/-- Swaps limb `k` of `[x]` and `[y]` if the mask `r11` is all ones (and not
if it is zero). -/
def cswapStep (x y k : Nat) : List Instr :=
  [.load .d .r5 .r6 (x + 8 * k), .load .d .r7 .r6 (y + 8 * k), .logic .xor .r8 .r5 .r7,
    .logic .and .r8 .r8 .r11, .logic .xor .r5 .r5 .r8, .logic .xor .r7 .r7 .r8,
    .store .d .r5 .r6 (x + 8 * k), .store .d .r7 .r6 (y + 8 * k)]

def cswap (x y : Nat) : List Instr := (List.range 5).flatMap (cswapStep x y)

/-! ## The ladder -/

/-- The start of an iteration, for the bit `t = r12 - 1`: `swap ^= k_t`. -/
def stepHead : List Instr :=
  [.subi .r12 .r12 1, .add .r4 .r6 .r12, .lbz .r4 .r4 BITS, .logic .xor .r0 .r0 .r4]

/-- `swap = k_t`, after the selections. -/
def stepBit : List Instr := [.add .r4 .r6 .r12, .lbz .r0 .r4 BITS]

/-- One iteration of the ladder, RFC 7748 §5's with its swap of the two
points taken where they differ, in `AA = A²` and `BB = B²`, whose `A` and
`B` are those of the point the swap makes the first: `DA + CB` and
`(DA - CB)²` are the same for the two orders. -/
def step : Prog isa :=
  .seq (.block stepHead) <|
  .seq (.block (sqrSel AA false X2 Z2 X3 Z3)) <| .seq (.block (sqrSel BB true X2 Z2 X3 Z3)) <|
  .seq (.block stepBit) <|
  .seq (.block (mulDS DA X3 Z3 X2 Z2)) <| .seq (.block (mulDS CB X2 Z2 X3 Z3)) <|
  .seq (.block (addA24 G AA BB)) <| .seq (.block (sqrSub T DA CB)) <| .seq (.block (sqrAdd X3 DA CB)) <|
  .seq (.block (mulSub Z2 AA BB G)) <| .seq (.block (mul Z3 X1 T)) (.block (mul X2 AA BB))

/-- The 255 iterations, for `t` from 254 down to 0, with `swap = 0`. -/
def ladder : Prog isa :=
  .seq (.block [.li .r12 255, .li .r0 0]) (.loop step (.nonzero .d .r12))

/-- The swap after the loop. -/
def lastSwap : List Instr := Impl.X25519.PPC64LE.mask ++ cswap X2 X3 ++ cswap Z2 Z3

/-! ## Inversion

`[R] = [Z2]^(p-2)` by ref10's addition chain (254 squarings and 11
multiplications; `Proof/X25519/Chain250.lean`'s `chainF`, then five squarings
and `z^11`). -/

/-- `[a]` squared `n` times into `[o]`, the squarings after the first in a
loop counted by `r12`, each of what the one before left in `lo`. -/
def sqn (o a n : Nat) : Prog isa :=
  .seq (.block (sqr o a)) <| .seq (.block [.li .r12 (n - 1)]) <|
    .loop (.block (sqrL o ++ [.subi .r12 .r12 1])) (.nonzero .d .r12)

def invert : Prog isa :=
  .seq (.block (sqr A Z2)) <| .seq (.block (sqr B A)) <| .seq (.block (sqr B B)) <|
  .seq (.block (mul B Z2 B)) <| .seq (.block (mul A A B)) <| .seq (.block (sqr C A)) <|
  .seq (.block (mul B B C)) <|
  .seq (sqn C B 5) <| .seq (.block (mul B C B)) <|
  .seq (sqn C B 10) <| .seq (.block (mul C C B)) <|
  .seq (sqn D C 20) <| .seq (.block (mul C D C)) <|
  .seq (sqn C C 10) <| .seq (.block (mul B C B)) <|
  .seq (sqn C B 50) <| .seq (.block (mul C C B)) <|
  .seq (sqn D C 100) <| .seq (.block (mul C D C)) <|
  .seq (sqn C C 50) <| .seq (.block (mul B C B)) <|
  .seq (sqn B B 5) (.block (mul R B A))

/-! ## To and from four words -/

/-- 1 at limb 0 and 0 at the others: `r7` and `r8`. -/
def one (k : Nat) : Reg := if k = 0 then .r7 else .r8

/-- The limbs of the four words at `U`, below `2²⁵⁵`, into `X1` and `X3`;
`x2 = 1`, `z2 = 0` and `z3 = 1`. -/
def unpack : List Instr :=
  mask51 ++ (List.range 4).map (fun k => .load .d (lo k) .r6 (U + 8 * k)) ++
  [.logic .and .r14 .r7 .r4,
    .lsr .d .r15 .r7 51, .lsl .r5 .r8 13, .add .r15 .r15 .r5, .logic .and .r15 .r15 .r4,
    .lsr .d .r16 .r8 38, .lsl .r5 .r9 26, .add .r16 .r16 .r5, .logic .and .r16 .r16 .r4,
    .lsr .d .r17 .r9 25, .lsl .r5 .r10 39, .add .r17 .r17 .r5, .logic .and .r17 .r17 .r4,
    .lsr .d .r18 .r10 12] ++
  stores ra X1 ++ stores ra X3 ++ [.li .r7 1, .li .r8 0] ++ stores one X2 ++ stores (fun _ => .r8) Z2 ++
  stores one Z3

/-- The element at `X2` in four words at `O`: its limbs' carries taken, one
limb after the other, then the limbs' bits put together, with the carry
chain for the lowest's bit 51. -/
def pack : List Instr :=
  ldV ra X2 ++ mask51 ++ [.li .r7 19] ++
  (List.range 4).flatMap (fun k =>
    [.lsr .d .r5 (ra k) 51, .logic .and (ra k) (ra k) .r4, .add (ra (k + 1)) (ra (k + 1)) .r5]) ++
  [.lsr .d .r5 .r18 51, .logic .and .r18 .r18 .r4, .mul .r5 .r5 .r7, .add .r14 .r14 .r5,
    .lsl .r5 .r15 51, .lsr .d .r9 .r15 13, .lsl .r12 .r16 38, .add .r9 .r9 .r12,
    .lsr .d .r10 .r16 26, .lsl .r12 .r17 25, .add .r10 .r10 .r12,
    .lsr .d .r11 .r17 39, .lsl .r12 .r18 12, .add .r11 .r11 .r12,
    .addc .r8 .r14 .r5, .addze .r9 .r9, .addze .r10 .r10, .addze .r11 .r11] ++
  Impl.X25519.PPC64LE.stores4 O

/-! ## The function -/

/-- Where `x25519` saves `r14`–`r31`. -/
abbrev SAVE : Nat := Impl.X25519.PPC64LE.SAVE

/-- Nonvolatile register `k`, `r14`–`r31`. -/
def nvR (k : Nat) : Reg :=
  [Reg.r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r25, .r26, .r27, .r28, .r29,
    .r30].getD k .r31

/-- `r14`–`r31` saved at `SAVE`. -/
def saveNV : List Instr := (List.range 18).map fun k => .store .d (nvR k) .r6 (SAVE + 8 * k)

/-- … and restored. -/
def restoreNV : List Instr := (List.range 18).map fun k => .load .d (nvR k) .r6 (SAVE + 8 * k)

def x25519 : Prog isa :=
  .seq (.block Impl.X25519.PPC64LE.setup) <| .seq Impl.X25519.PPC64LE.bits <| .seq (.block saveNV) <|
  .seq (.block unpack) <| .seq ladder <| .seq (.block lastSwap) <| .seq invert <|
  .seq (.block (mul X2 X2 R)) <| .seq (.block pack) (.block (restoreNV ++ Impl.X25519.PPC64LE.freeze))

end VG.Impl.X25519.PPC64LE.Fe51
