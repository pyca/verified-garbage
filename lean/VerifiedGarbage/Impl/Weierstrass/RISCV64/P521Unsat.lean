module

public import VerifiedGarbage.Impl.Weierstrass.RISCV64.GenWide
public import VerifiedGarbage.Impl.Words.RISCV64.Wide
public import VerifiedGarbage.Impl.Weierstrass.RISCV64
public import VerifiedGarbage.Impl.Weierstrass.Layout.Mont

/-!
# Arithmetic modulo P-521's prime in 58-bit limbs, on RISC-V

An element is nine words `l₀ … l₈`, its limbs, standing for
`Σ lᵢ 2⁵⁸ⁱ`; it is *tight* if `lᵢ < 2⁵⁹` for `i < 8` and `l₈ < 2⁵⁸`. The
functions, with GenWide's entry and copies (`GenWide.fnWith`, `GenWide.fn`, so
`vg_<name>(ws, o, a, b)` as GenWide's), take tight elements to tight
elements, equal modulo `p = 2⁵²¹ - 1`, for which `2⁵²² ≡ 2`
(`Proof/Weierstrass/RISCV64/P521Unsat/`):

* `mulFn`: `[o] ≡ [a] [b]`. Column `c < 9` of the product is
  `Σ_{i+j=c} aᵢ bⱼ + Σ_{i+j=c+9} aᵢ (2 bⱼ)`, the doubled limbs `2 bⱼ`
  stored first at `Y`, each term's two words added to a two-word
  accumulator (`a4`, `a5`), each term's product computed, and the next one's
  operands loaded, a term ahead of its sums, so that an in-order processor
  does not wait for them; the column's low 58 bits are stored at `Z` and the
  accumulator shifted right by 58 (`colEnd`). What is left past `2⁵²²`,
  doubled, is added into limbs 0 and 1 (`fold`). If the two pointers are
  equal, the terms are a square's (`sqPairs`): each cross product once, from
  a doubled limb.
* `addFn`, `subFn`: `[o] ≡ [a] + [b]`, `[o] ≡ [a] + 4p - [b]`, limb by
  limb, `4p`'s limbs `2⁶⁰ - 4` and `2⁵⁹ - 4` added for the difference,
  with the carries through the limbs and the last one, doubled, into limb 0.
* `unpackFn`: the limbs of a number below `2⁵²²` given as nine words.
* `packFn`: the residue modulo `p`, as nine words, of a tight element: its
  carries (`carryPass`), the bits from 521 on folded down, its carries again,
  and `p` subtracted if `v + 1` reaches `2⁵²¹` (`canon`), then its limbs
  gathered into words.

Each result is written at `Z` first and then copied to `[o]`, which may be
either operand. Every multiplication is `mul` or `mulhu`, and the only
branches are on the pointers: GenWide's, and whether they are equal.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.RISCV64.P521Unsat

open VG.RISCV64
open VG.Impl.Weierstrass.RISCV64.GenWide (T fnWith fn fnA)
open VG.Impl.Words.RISCV64 (mulWide add2)

/-- The nine limbs of a result, from `a3`. -/
abbrev Z : Nat := T 9

/-- The nine doubled limbs of an operand, from `a3`, after `Z`. -/
abbrev Y : Nat := T 9 + 72

/-- `a6 = 2⁵⁸ - 1`. -/
def mask : List Instr := [.li .a6 (-1), .shift .srl .d .a6 .a6 6]

/-- `Y[j] = 2 [src + 8 j]`, through `a1`. -/
def dbl (src : Reg) : List Instr :=
  (List.range 9).flatMap fun j => [.load .d .a1 src (8 * j), .shift .sll .d .a1 .a1 1, .store .d .a1 .a3 (Y + 8 * j)]

/-- `[t2 + 8 j] = Z[j]` from limb `j₀`, through `a1`. -/
def copyZ (j₀ : Nat) : List Instr :=
  (List.range' j₀ (9 - j₀)).flatMap fun j => [.load .d .a1 .a3 (Z + 8 * j), .store .d .a1 .t2 (8 * j)]

/-! ## The product by columns, software-pipelined -/

/-- An operand's word: its base register and offset. -/
abbrev Src := Reg × Nat

/-- A term: its column and its two operands. -/
abbrev Tm := Nat × Src × Src

/-- Term `n` of `ts`. -/
def tm (ts : List Tm) (n : Nat) : Tm := ts.getD n (0, (.t4, 0), (.t4, 0))

/-- A product's terms, column by column, from each column's pairs `ps c`. -/
def terms (ps : Nat → List (Src × Src)) : List Tm :=
  (List.range 9).flatMap fun c => (ps c).map fun p => (c, p)

/-- The index of column `c`'s first term, for `cs c` terms in column `c`. -/
def pstart (cs : Nat → Nat) (c : Nat) : Nat := ((List.range c).map cs).sum

/-- The registers of term `n`'s product, low and high: `a7`, `t0` and `t3`,
`t6` in turn. -/
def PR (n : Nat) : Reg × Reg := if n % 2 = 0 then (.a7, .t0) else (.t3, .t6)

/-- Term `n`'s operands into `a1` and `a2`, if it is one. -/
def ldN (ts : List Tm) (n : Nat) : List Instr :=
  if n < ts.length then
    [.load .d .a1 (tm ts n).2.1.1 (tm ts n).2.1.2, .load .d .a2 (tm ts n).2.2.1 (tm ts n).2.2.2]
  else []

/-- Term `n`'s product, from `a1` and `a2`, if it is one. -/
def mulN (ts : List Tm) (n : Nat) : List Instr :=
  if n < ts.length then mulWide (PR n).1 (PR n).2 .a1 .a2 else []

/-- Term `n`: the next term's product and the operands of the one after it,
issued before this one's sums into `a4 + 2⁶⁴ a5`, which they do not depend on. -/
def pstep (ts : List Tm) (n : Nat) : List Instr :=
  mulN ts (n + 1) ++ ldN ts (n + 2) ++ add2 .a4 .a5 (PR n).1 (PR n).2

/-- The end of column `c`: `Z[c]` the accumulator's low 58 bits, and the
accumulator shifted right by 58, through the registers of a product `e`
already summed. -/
def colEnd (e c : Nat) : List Instr :=
  [.logic .and (PR e).1 .a4 .a6, .store .d (PR e).1 .a3 (Z + 8 * c), .shift .srl .d (PR e).1 .a4 58,
    .shift .sll .d (PR e).2 .a5 6, .logic .or .a4 (PR e).1 (PR e).2, .shift .srl .d .a5 .a5 58]

/-- Column `c`: its `cs c` terms, then its end, through the registers of its
last term's product (those of the term after the next). -/
def pcol (ts : List Tm) (cs : Nat → Nat) (c : Nat) : List Instr :=
  (List.range' (pstart cs c) (cs c)).flatMap (pstep ts) ++ colEnd (pstart cs (c + 1) + 1) c

/-- The terms `ts` into the nine limbs at `Z` and what is left in the
accumulator, the first term's product and the second's operands ahead. -/
def pipe (ts : List Tm) (cs : Nat → Nat) : List Instr :=
  [.li .a4 0, .li .a5 0] ++ ldN ts 0 ++ mulN ts 0 ++ ldN ts 1 ++ (List.range 9).flatMap (pcol ts cs)

/-- The pairs of column `c` of `[t4] [t5]`: `aᵢ bⱼ` for `i + j = c`, then
`aᵢ (2 bⱼ)` for `i + j = c + 9`, the doubled limb from `Y`. -/
def mulPairs (c : Nat) : List (Src × Src) :=
  ((List.range 9).filter fun i => i ≤ c).map (fun i => ((.t4, 8 * i), (.t5, 8 * (c - i)))) ++
    ((List.range 9).filter fun i => c < i).map (fun i => ((.t4, 8 * i), (.a3, Y + 8 * (c + 9 - i))))

/-- The pairs of column `c` of `[t4]²`, from the limbs `aᵢ` and the doubled
limbs `dᵢ = 2 aᵢ` at `Y`: `aᵢ dⱼ` for `i + j = c`, `j < i`, and `a_{c/2}²`;
then `dᵢ dⱼ` for `i + j = c + 9`, `j < i`, and `a_{(c+9)/2} d_{(c+9)/2}`. -/
def sqPairs (c : Nat) : List (Src × Src) :=
  ((List.range 9).filter fun i => i ≤ c ∧ c - i < i).map (fun i => ((.t4, 8 * i), (.a3, Y + 8 * (c - i)))) ++
    (if c % 2 = 0 then [((.t4, 8 * (c / 2)), (.t4, 8 * (c / 2)))] else []) ++
    ((List.range 9).filter fun i => c < i ∧ c + 9 - i < i).map
      (fun i => ((.a3, Y + 8 * i), (.a3, Y + 8 * (c + 9 - i)))) ++
    (if c % 2 = 1 then [((.t4, 8 * ((c + 9) / 2)), (.a3, Y + 8 * ((c + 9) / 2)))] else [])

/-- What is left past `2⁵²²`, `C = a4 + 2⁶⁴ a5`, doubled into limbs 0 and 1:
`(2C) mod 2⁵⁸` into limb 0, `(2C) >> 58` and limb 0's carry into limb 1;
then the limbs to `[t2]`. -/
def fold : List Instr :=
  [.load .d .a1 .a3 Z, .load .d .a2 .a3 (Z + 8), .shift .sll .d .t3 .a4 1, .logic .and .t3 .t3 .a6,
    .add .a1 .a1 .t3, .shift .srl .d .t3 .a4 57, .shift .sll .d .t6 .a5 7, .add .t3 .t3 .t6, .add .a2 .a2 .t3,
    .shift .srl .d .t3 .a1 58, .logic .and .a1 .a1 .a6, .add .a2 .a2 .t3, .store .d .a1 .t2 0,
    .store .d .a2 .t2 8] ++ copyZ 2

/-- `[t2] ≡ [t4] [t5]`. -/
def mulC : List Instr := mask ++ dbl .t5 ++ pipe (terms mulPairs) (fun c => (mulPairs c).length) ++ fold

/-- `[t2] ≡ [t4]²`. -/
def sqC : List Instr := mask ++ dbl .t4 ++ pipe (terms sqPairs) (fun c => (sqPairs c).length) ++ fold

/-- The product, a square if the pointers are equal. -/
def core : Prog isa := .ite (.eq .t4 .t5) (.block sqC) (.block mulC)

/-! ## Sums and differences -/

/-- Limb `i` of `[t4] + [t5]` (or `[t4] + 4p - [t5]`, `4p`'s limbs in `a7`
and `t6`) and the carry `a4` into `Z[i]`, the carry out in `a4`. -/
def addStep (sub : Bool) (i : Nat) : List Instr :=
  [.load .d .a1 .t4 (8 * i), .load .d .a2 .t5 (8 * i)] ++
    (if sub then [.add .a1 .a1 (if i < 8 then .a7 else .t6), .sub .a1 .a1 .a2] else [.add .a1 .a1 .a2]) ++
    [.add .a1 .a1 .a4, .shift .srl .d .a4 .a1 58, .logic .and .a1 .a1 .a6, .store .d .a1 .a3 (Z + 8 * i)]

/-- `[t2] ≡ [t4] + [t5]`, or `[t4] + 4p - [t5]`: the limbs, the last carry
doubled into limb 0. -/
def addC (sub : Bool) : List Instr :=
  mask ++ [.li .a4 0] ++
    (if sub then [.li .a7 1, .shift .sll .d .a7 .a7 60, .addi .a7 .a7 (-4), .li .t6 1, .shift .sll .d .t6 .t6 59,
      .addi .t6 .t6 (-4)] else []) ++
    (List.range 9).flatMap (addStep sub) ++
    [.load .d .a1 .a3 Z, .shift .sll .d .a4 .a4 1, .add .a1 .a1 .a4, .store .d .a1 .t2 0] ++ copyZ 1

/-! ## Words to limbs and back -/

/-- Limb `k` of the number at `[t4]`: its bits `58 k …` from words `58 k / 64`
and the next, into `Z[k]`. -/
def unpackStep (k : Nat) : List Instr :=
  [.load .d .a1 .t4 (8 * (58 * k / 64)), .shift .srl .d .a1 .a1 (58 * k % 64)] ++
    (if 64 - 58 * k % 64 < 58 ∧ 58 * k / 64 + 1 < 9 then
      [.load .d .a2 .t4 (8 * (58 * k / 64 + 1)), .shift .sll .d .a2 .a2 (64 - 58 * k % 64), .add .a1 .a1 .a2]
     else []) ++
    [.logic .and .a1 .a1 .a6, .store .d .a1 .a3 (Z + 8 * k)]

/-- `[t2]`: the limbs of the number below `2⁵²²` at `[t4]`. -/
def unpackC : List Instr := mask ++ (List.range 9).flatMap unpackStep ++ copyZ 0

/-- Limb `i` of `[src + off]` plus the carry `a4` into `Z[i]`, cut to 58 bits
with its carry into `a4` but the last. -/
def carryStep (src : Reg) (off i : Nat) : List Instr :=
  [.load .d .a1 src (off + 8 * i), .add .a1 .a1 .a4] ++
    (if i < 8 then [.shift .srl .d .a4 .a1 58, .logic .and .a1 .a1 .a6] else []) ++
    [.store .d .a1 .a3 (Z + 8 * i)]

/-- The carries through the nine limbs at `src + off`, into `Z`, from the carry in `a4`. -/
def carryPass (src : Reg) (off : Nat) : List Instr := (List.range 9).flatMap (carryStep src off)

/-- `Z[8]`'s bits from 57 on into `a4`, and `Z[8]` cut to 57 bits, through `a7`. -/
def topCut : List Instr :=
  [.load .d .a1 .a3 (Z + 64), .shift .srl .d .a4 .a1 57, .shift .srl .d .a7 .a6 1, .logic .and .a1 .a1 .a7,
    .store .d .a1 .a3 (Z + 64)]

/-- The carry of limb `i` of `Z + 1` into `a4`. -/
def probeStep (i : Nat) : List Instr :=
  [.load .d .a1 .a3 (Z + 8 * i), .add .a1 .a1 .a4, .shift .srl .d .a4 .a1 58]

/-- The residue at `Z` of the tight element at `[t4]`: its carries; the bits
from 521 on added back to limb 0, and the carries again, for `v < 2⁵²¹ + 2⁴`;
then `q`, bit 521 of `v + 1`, added, and limb 8 cut to 57 bits: `v - q p`. -/
def canon : List Instr :=
  [.li .a4 0] ++ carryPass .t4 0 ++ topCut ++ carryPass .a3 Z ++
    [.li .a4 1] ++ (List.range 8).flatMap probeStep ++
    [.load .d .a1 .a3 (Z + 64), .add .a1 .a1 .a4, .shift .srl .d .a4 .a1 57] ++
    carryPass .a3 Z ++ topCut

/-- The limbs at `Z` that word `j` of their number holds bits of. -/
def packLimbs (j : Nat) : List Nat := (List.range 9).filter fun k => 58 * k < 64 * j + 64 ∧ 64 * j < 58 * k + 58

/-- Word `j` of the number whose limbs are at `Z`, into `[t2 + 8 j]`. -/
def packStep (j : Nat) : List Instr :=
  [.li .a2 0] ++ (packLimbs j).flatMap (fun k =>
      [.load .d .a1 .a3 (Z + 8 * k)] ++
      (if 64 * j ≤ 58 * k then [.shift .sll .d .a1 .a1 (58 * k - 64 * j)]
       else [.shift .srl .d .a1 .a1 (64 * j - 58 * k)]) ++
      [.add .a2 .a2 .a1]) ++ [.store .d .a2 .t2 (8 * j)]

/-- `[t2]`: the residue modulo `p` of the tight element at `[t4]`, as nine words. -/
def packC : List Instr := mask ++ canon ++ (List.range 9).flatMap packStep

/-! ## The functions -/

/-- The function multiplying modulo `p`: on the byte-wise copies, which are
never the same pointer, the product. -/
def mulFn : Prog isa := fnWith 9 core mulC

/-- The function adding modulo `p`. -/
def addFn : Prog isa := fn 9 (addC false)

/-- The function subtracting modulo `p`. -/
def subFn : Prog isa := fn 9 (addC true)

/-- The function unpacking a number into limbs. -/
def unpackFn : Prog isa := fn 9 unpackC

/-- The function packing an element's residue into words. -/
def packFn : Prog isa := fn 9 packC

/-- The function multiplying, for aligned offsets (`GenWide.fnA`): `core`
on the operands where they are. -/
def mulFnA : Prog isa := fnA core

/-- Their names: `vg_p521u_<op>_mod_p`. -/
def S : Impl.Weierstrass.Mont.Modulus := { Impl.Weierstrass.Mont.p521p with curve := "p521u" }

/-- The product, sum and difference as a field's functions, for the calls of
field programs (`Impl/Weierstrass/RISCV64.lean`'s `fprog`); the calls'
offsets, multiples of 8, take `mulFnA`. -/
def field : Field := ⟨S, mulFn, addFn, subFn, mulFnA, addFn, subFn⟩

end VG.Impl.Weierstrass.RISCV64.P521Unsat
