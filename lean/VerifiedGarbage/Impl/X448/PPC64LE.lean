module

public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# X448: PPC64LE implementation

`vg_x448(out = r3, scalar = r4, point = r5, scratch = r6)`.

X25519's PPC64LE implementation (`Impl/X25519/PPC64LE.lean`) for curve448's
field, `p = 2⁴⁴⁸ - 2²²⁴ - 1`: a field element is fourteen 32-bit limbs
`x0 + 2³² x1 + … + 2⁴¹⁶ x13`, each in a word of the working space, any
number below `2⁴⁴⁸` standing for its residue modulo `p`; only the result is
reduced fully. Every element lives in the working space at a constant offset
from its base, which stays in `r6` (`out` stays in `r3`):

* `x1, x2, z2, x3, z3`, the ladder's temporaries, the constant `a24`, the
  inversion's result and the final reduction's temporary, 56 bytes each
  (`X1`, …);
* the registers `r14`–`r27` a multiplication saves (`ACC`, 112 bytes; Ed448's
  scalar arithmetic keeps the limbs of its products there) and the bits of
  the scalar (`BITS`, byte `t` is bit `t` of the clamped scalar).

The arithmetic (registers `r4`, `r5`, `r7`–`r11`), with `2⁴⁴⁸ ≡ 2²²⁴ + 1`:

* `pass`: the limbs of a number from fourteen sums `c_k` (below `2⁶⁴` less a
  carry), limb `k` being `c_k` plus the carry from limb `k - 1`, modulo
  `2³²`, and the carry out in `r8`;
* `fold`: the carry out `c` folded in as `c + 2²²⁴ c`: added to limbs 0 and
  7 and carried again; `tail` folds twice, after which nothing carries out;
* `mul` (`mulR`), in registers: `r14`–`r27` saved at `ACC`, the operands'
  seven doublewords each loaded into `opA` and `opB`, and `r28`–`r31` saved
  over the result's first four doublewords (the operands are loaded, so the
  result may be one of them); the product's fourteen doublewords column by
  column into `pw` (a column's products of doublewords, `mulld` and
  `mulhdu`, added into three registers with `addc`, `adde` and `addze`;
  the later words in the registers of operands' words no later column
  reads); then, with `H = Hₗ + 2²²⁴ Hₕ` its high half,
  `L + 2⁴⁴⁸ H ≡ L + H + (2²²⁴ Hₗ + Hₕ) + 2²²⁴ Hₕ` by three carry chains
  (the second adds `H` rotated by 224 bits, computed into `rotReg` first),
  their carry `c` folded in as `c + 2²²⁴ c` twice; finally `r28`–`r31`
  restored, the result stored and `r14`–`r27` restored, so that it changes
  only the volatile registers `r4`, `r5` and `r7`–`r11`;
* `add`, `sub`: the seven doublewords of `a + b` (carry chain, `addc`/`adde`)
  and of `a - b` modulo `2⁴⁴⁸` (borrow chain, `subc`/`sube`), each stored as
  it is made, then the carry `c` added as `c + 2²²⁴ c`, or the borrow `β`
  taken away as `β + 2²²⁴ β`, twice (a chain over the stored doublewords;
  the second carries or borrows nothing);
* `cswap`: with the mask `-swap` (in `r11`), as RFC 7748 §5 describes;
* `freeze`: the full reduction of the result: `y = x + 2²²⁴ + 1` carries out
  exactly when `x ≥ p` (`x < 2⁴⁴⁸`), and is then `x - p` modulo `2⁴⁴⁸`,
  selected with a mask.

The ladder follows RFC 7748 §5 operation by operation (with `a24 · E`
by the one-word multiplication `mulA24`), over the bits of the scalar
from 447 down to 0 (the counter `r12`, which indexes `BITS`; `swap` in `r0`).
The inversion `z2^(p-2)` is an addition chain (446 squarings and 15
multiplications, in the ladder's temporaries), its runs of squarings counted
by `r12`.

The function changes only volatile registers (a multiplication restores the
others it uses). The only branches are on the loop
counters, and every address is a pointer plus a constant or a counter, so
only the pointers can affect timing.
-/

@[expose] public section

namespace VG.Impl.X448.PPC64LE

open VG.PPC64LE

/-! ## The layout of the working space -/

def X1 : Nat := 0
def X2 : Nat := 56
def Z2 : Nat := 112
def X3 : Nat := 168
def Z3 : Nat := 224
def A : Nat := 280
def B : Nat := 336
def C : Nat := 392
def D : Nat := 448
def AA : Nat := 504
def BB : Nat := 560
def E : Nat := 616
def DA : Nat := 672
def CB : Nat := 728
def R : Nat := 840
def Y : Nat := 896
def ACC : Nat := 952
def BITS : Nat := 1064

/-! ## Carrying -/

/-- A limb stored at `rb + off`: `r7 + r8` modulo `2³²`, and the carry
`(r7 + r8) >> 32` into `r8`. -/
def carryStep (rb : Reg) (off : Nat) : List Instr :=
  [.add .r7 .r7 .r8, .store .w .r7 rb off, .lsr .d .r8 .r7 32]

/-- The limbs at `rb + o` from the sums `src k` leaves in `r7` and the carry
in `r8`. -/
def pass (rb : Reg) (o : Nat) (src : Nat → List Instr) : List Instr :=
  (List.range 14).flatMap fun k => src k ++ carryStep rb (o + 4 * k)

/-- Limb `k` of `[o]`, into `r7`. -/
def ldSrc (o k : Nat) : List Instr := [.load .w .r7 .r6 (o + 4 * k)]

/-- Limb `k` of `[o]`, with the carry folded in kept in `r10` added to limb 7, into `r7`. -/
def foldSrc (o k : Nat) : List Instr := ldSrc o k ++ (if k = 7 then [.add .r7 .r7 .r10] else [])

/-! ## Field arithmetic -/

/-- Limb `k` of `[a] + [b]`, a source for `pass` (Ed448's scalar arithmetic
on PPC64LE uses it). -/
def addSrc (a b k : Nat) : List Instr :=
  [.load .w .r7 .r6 (a + 4 * k), .load .w .r5 .r6 (b + 4 * k), .add .r7 .r7 .r5]

/-- Step `k` of a carry chain (`addc`, then `adde`), or with `sub` of a
borrow chain (`subc`, then `sube`), of `r7` and `src`, into `r7`. -/
def chainOp (sub : Bool) (k : Nat) (src : Reg) : Instr :=
  if sub then (if k = 0 then .subc .r7 .r7 src else .sube .r7 .r7 src)
  else (if k = 0 then .addc .r7 .r7 src else .adde .r7 .r7 src)

/-- Doubleword `k` of `[x] ± [y]` by the chain, stored at `o + 8k`. -/
def chainStep (sub : Bool) (o x y k : Nat) : List Instr :=
  [.load .d .r7 .r6 (x + 8 * k), .load .d .r8 .r6 (y + 8 * k), chainOp sub k .r8,
    .store .d .r7 .r6 (o + 8 * k)]

/-- What a fold adds to (or subtracts from) doubleword `k`: `r4` to word 0,
`r5` to word 3, `r8` (zero) to the others. -/
def foldSrc64 (k : Nat) : Reg := if k = 0 then .r4 else if k = 3 then .r5 else .r8

/-- Doubleword `k` of `[o] ± foldSrc64`, by the chain. -/
def foldStep (sub : Bool) (o k : Nat) : List Instr :=
  [.load .d .r7 .r6 (o + 8 * k), chainOp sub k (foldSrc64 k), .store .d .r7 .r6 (o + 8 * k)]

/-- The carry `c` of a sum into `r4`, `2³² c` into `r5` and zero into `r8`:
the fold then adds `c + 2²²⁴ c` (`2⁴⁴⁸ ≡ 2²²⁴ + 1`). -/
def carryPrep : List Instr := [.li .r4 0, .addze .r4 .r4, .lsl .r5 .r4 32, .li .r8 0]

/-- The borrow `β` of a difference (CA clear) into `r4`, `2³² β` into `r5`
and zero into `r8`: `CA - 1` by `sube`, negated. -/
def borrowPrep : List Instr := [.li .r8 0, .sube .r4 .r8 .r8, .sub .r4 .r8 .r4, .lsl .r5 .r4 32]

/-- `[o] = [a] + [b]` (`o` may be `a` or `b`): the seven doublewords of the
sum by the carry chain, each stored as it is made, and its carry folded in
as `c + 2²²⁴ c`, twice (after the first, nothing carries out). -/
def add (o a b : Nat) : List Instr :=
  (List.range 7).flatMap (chainStep false o a b) ++
    carryPrep ++ (List.range 7).flatMap (foldStep false o) ++
    carryPrep ++ (List.range 7).flatMap (foldStep false o)

/-- `[o] = [a] - [b]` (`o` may be `a` or `b`): the seven doublewords of the
difference modulo `2⁴⁴⁸` by the borrow chain, and its borrow `β` taken away
as `β + 2²²⁴ β`, twice (the second does not borrow). -/
def sub (o a b : Nat) : List Instr :=
  (List.range 7).flatMap (chainStep true o a b) ++
    borrowPrep ++ (List.range 7).flatMap (foldStep true o) ++
    borrowPrep ++ (List.range 7).flatMap (foldStep true o)

/-- Doubleword `k` of `a24 · [a]` (`a24 = 39081` in `r5`, the previous
step's high word in `r7`): `mulld` plus the previous `mulhdu` by the carry
chain, stored at `o + 8k`, and this step's `mulhdu` into `r7`. -/
def a24Step (o a k : Nat) : List Instr :=
  [.load .d .r8 .r6 (a + 8 * k), .mul .r9 .r8 .r5,
    if k = 0 then .addc .r9 .r9 .r7 else .adde .r9 .r9 .r7, .mulhu .r7 .r8 .r5,
    .store .d .r9 .r6 (o + 8 * k)]

/-- `[o] = a24 · [a]` (`a24 = 39081`; `o` may be `a`): the seven doublewords
of the product, each stored as it is made, and its top word `t < 2¹⁶`
folded in as `t + 2²²⁴ t` twice, as `add` folds its carry. -/
def mulA24 (o a : Nat) : List Instr :=
  [.li .r5 0, .ori .r5 .r5 0x98a9, .li .r7 0] ++ (List.range 7).flatMap (a24Step o a) ++
    [.addze .r4 .r7, .lsl .r5 .r4 32, .li .r8 0] ++ (List.range 7).flatMap (foldStep false o) ++
    carryPrep ++ (List.range 7).flatMap (foldStep false o)

/-- Register `r` stored into the `n` words from `o` of the working space. -/
def storeN (r : Reg) (o n : Nat) : List Instr := (List.range n).flatMap fun k => [.store .w r .r6 (o + 4 * k)]

/-- The words `ACC[0, 14)` zeroed (Ed448's scalar arithmetic on PPC64LE uses
this and `row`). -/
def zeroAcc : List Instr := .li .r7 0 :: storeN .r7 ACC 14

/-- Limb `j` of row `i` (`r9` = the base plus `4 i`, `a_i` in `r4`) into
`r7`: `a_i b_j + acc[i + j]`. -/
def rowSrc (b j : Nat) : List Instr :=
  [.load .w .r5 .r6 (b + 4 * j), .mul .r5 .r4 .r5, .load .w .r7 .r9 (ACC + 4 * j), .add .r7 .r7 .r5]

/-- Row `i` of the product: `acc[i, i + 15) = acc[i, i + 14) + a_i · b`. -/
def row (a b : Nat) : List Instr :=
  [.load .w .r4 .r9 a, .li .r8 0] ++ pass .r9 ACC (rowSrc b) ++
    [.store .w .r8 .r9 (ACC + 56), .addi .r9 .r9 4, .subi .r11 .r11 1]

/-! ## Multiplication in registers -/

/-- The registers of the operands' words: `a_i` in `opA i`, `b_j` in `opB j`. -/
def opA (i : Nat) : Reg := [.r14, .r15, .r16, .r17, .r18, .r19, .r20].getD i .r14
def opB (j : Nat) : Reg := [.r21, .r22, .r23, .r24, .r25, .r26, .r27].getD j .r21

/-- The registers of the product's words `0, …, 14`: from word 9 on, those
of operands' words no later column reads (`a_0`, `b_0`, `a_1`, `b_1`, `a_2`,
`a_3`). -/
def pw (k : Nat) : Reg :=
  [.r7, .r8, .r9, .r10, .r11, .r28, .r29, .r30, .r31, .r14, .r21, .r15, .r22, .r16, .r17].getD k .r7

/-- The pairs `(i, j)` of column `k`: `i + j = k`, `i, j < 7`. -/
def pairs (k : Nat) : List (Nat × Nat) :=
  ((List.range 7).filter fun i => i ≤ k ∧ k - i < 7).map fun i => (i, k - i)

/-- The term `a_i b_j` of column `k`, added into `pw k, pw (k + 1), pw (k + 2)`. -/
def termR (k : Nat) (p : Nat × Nat) : List Instr :=
  [.mul .r4 (opA p.1) (opB p.2), .mulhu .r5 (opA p.1) (opB p.2),
    .addc (pw k) (pw k) .r4, .adde (pw (k + 1)) (pw (k + 1)) .r5, .addze (pw (k + 2)) (pw (k + 2))]

/-- Column `k`: `pw (k + 2)` cleared, then its terms. -/
def colR (k : Nat) : List Instr := .li (pw (k + 2)) 0 :: (pairs k).flatMap (termR k)

/-- The registers the reduction's chains add from. -/
def rotReg (k : Nat) : Reg := [.r18, .r19, .r20, .r23, .r24, .r25, .r26].getD k .r18

/-- Step `k` of a carry chain into `pw k` from `src`. -/
def chainR (k : Nat) (src : Reg) : Instr := if k = 0 then .addc (pw k) (pw k) src else .adde (pw k) (pw k) src

/-- The carry chain `pw 0, …, pw 6 += src 0, …, src 6`. -/
def chain7 (src : Nat → Reg) : List Instr := (List.range 7).map fun k => chainR k (src k)

/-- Doubleword `k` of the product's high half `H = pw 7, …, pw 13` rotated by
224 bits into `rotReg k` (`r27` scratch). -/
def rotR (k : Nat) : List Instr :=
  [.lsr .d (rotReg k) (pw (7 + (k + 3) % 7)) 32, .lsl .r27 (pw (7 + (k + 4) % 7)) 32,
    .add (rotReg k) (rotReg k) .r27]

/-- What the third chain adds: `H` with its low 224 bits cleared (zero in
`r18`, doubleword 3 in `r19`). -/
def hiReg (k : Nat) : Reg := if k < 3 then .r18 else if k = 3 then .r19 else pw (7 + k)

/-- What a fold adds: the carry `c` (`r4`) to word 0, `2³² c` (`r5`) to word
3, zero (`r18`) to the others. -/
def foldReg (k : Nat) : Reg := if k = 0 then .r4 else if k = 3 then .r5 else .r18

/-- The reduction of the product in `pw` into `pw 0, …, pw 6`, as `reduce`'s
on memory: `L + H`, `+= 2²²⁴ Hₗ + Hₕ`, `+= 2²²⁴ Hₕ` (carries summed in
`r4`), then the carry folded in as `c + 2²²⁴ c` twice. -/
def reduceR : List Instr :=
  chain7 (fun k => pw (7 + k)) ++ [.li .r4 0, .addze .r4 .r4] ++
  (List.range 7).flatMap rotR ++ chain7 rotReg ++ [.addze .r4 .r4] ++
  [.li .r18 0, .lsr .d .r19 (pw 10) 32, .lsl .r19 .r19 32] ++ chain7 hiReg ++ [.addze .r4 .r4] ++
  [.lsl .r5 .r4 32] ++ chain7 foldReg ++ [.li .r4 0, .addze .r4 .r4, .lsl .r5 .r4 32] ++ chain7 foldReg

/-- Registers `regs 0`, …, `regs (n - 1)` at consecutive doublewords. -/
def slotsOf (regs : Nat → Reg) (n : Nat) : List (Reg × Nat) := (List.range n).map fun i => (regs i, 8 * i)

/-- Each `(r, d)`'s register stored at `base + d` of the working space. -/
def stdsAt (base : Nat) (l : List (Reg × Nat)) : List Instr := l.map fun (r, d) => .store .d r .r6 (base + d)

/-- Each `(r, d)`'s register loaded from `base + d` of the working space. -/
def ldsAt (base : Nat) (l : List (Reg × Nat)) : List Instr := l.map fun (r, d) => .load .d r .r6 (base + d)

/-- `r14`–`r27`, saved at `ACC`. -/
def loR (i : Nat) : Reg :=
  [.r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r25, .r26, .r27].getD i .r14

/-- `r28`–`r31`, saved over the first four doublewords of the result. -/
def hiR (i : Nat) : Reg := [.r28, .r29, .r30, .r31].getD i .r28

/-- Where the result's words are before it is stored: `pw 5` and `pw 6`
(`r28`, `r29`, which are restored first) moved into `r23` and `r24`. -/
def outR (k : Nat) : Reg := [.r7, .r8, .r9, .r10, .r11, .r23, .r24].getD k .r7

/-- `[o] = [a] · [b]` (`o` may be `a` or `b`) in registers: `r14`–`r27`
saved at `ACC`; the operands' words loaded; `r28`–`r31` saved at `o`; the
product's fifteen words column by column (`colR`) and their reduction
(`reduceR`); `r28`–`r31` restored, the result stored at `o`, and
`r14`–`r27` restored. -/
def mulR (o a b : Nat) : List Instr :=
  stdsAt ACC (slotsOf loR 14) ++ ldsAt a (slotsOf opA 7) ++ ldsAt b (slotsOf opB 7) ++
  stdsAt o (slotsOf hiR 4) ++ [.li (pw 0) 0, .li (pw 1) 0] ++ (List.range 13).flatMap colR ++ reduceR ++
  [.addi .r23 (pw 5) 0, .addi .r24 (pw 6) 0] ++ ldsAt o (slotsOf hiR 4) ++ stdsAt o (slotsOf outR 7) ++
  ldsAt ACC (slotsOf loR 14)

/-- `[o] = [a] · [b]` (`o` may be `a` or `b`): `mulR`. -/
def mul (o a b : Nat) : Prog isa := .block (mulR o a b)

/-- Swaps limb `k` of `[x]` and `[y]` if the mask `r11` is all ones (and not
if it is zero): `d = r11 ∧ (x ⊕ y)`, `x ⊕= d`, `y ⊕= d`. -/
def cswapStep (x y k : Nat) : List Instr :=
  [.load .w .r5 .r6 (x + 4 * k), .load .w .r7 .r6 (y + 4 * k), .logic .xor .r8 .r5 .r7,
    .logic .and .r8 .r8 .r11, .logic .xor .r5 .r5 .r8, .logic .xor .r7 .r7 .r8,
    .store .w .r5 .r6 (x + 4 * k), .store .w .r7 .r6 (y + 4 * k)]

def cswap (x y : Nat) : List Instr := (List.range 14).flatMap (cswapStep x y)

/-! ## The ladder -/

/-- The mask `-swap` into `r11`. -/
def mask : List Instr := [.li .r11 0, .sub .r11 .r11 .r0]

/-- The start of an iteration of the ladder, for the bit `t = r12 - 1`: `k_t`
from `BITS`, `swap ^= k_t`, the swaps by the mask `-swap`, and `swap = k_t`. -/
def stepHead : List Instr :=
  [.subi .r12 .r12 1, .add .r4 .r6 .r12, .lbz .r4 .r4 BITS, .logic .xor .r0 .r0 .r4] ++ mask ++
    cswap X2 X3 ++ cswap Z2 Z3 ++ [.addi .r0 .r4 0]

/-- One iteration of the ladder: `stepHead`, then the formulas of RFC 7748 §5
in order. -/
def step : Prog isa :=
  .seq (.block stepHead) <|
  .seq (.block (add A X2 Z2)) <| .seq (mul AA A A) <| .seq (.block (sub B X2 Z2)) <|
  .seq (mul BB B B) <| .seq (.block (sub E AA BB)) <| .seq (.block (add C X3 Z3)) <|
  .seq (.block (sub D X3 Z3)) <| .seq (mul DA D A) <| .seq (mul CB C B) <|
  .seq (.block (add X3 DA CB)) <| .seq (mul X3 X3 X3) <| .seq (.block (sub Z3 DA CB)) <|
  .seq (mul Z3 Z3 Z3) <| .seq (mul Z3 X1 Z3) <| .seq (mul X2 AA BB) <| .seq (.block (mulA24 Z2 E)) <|
  .seq (.block (add Z2 AA Z2)) <| .seq (mul Z2 E Z2) (.block [])

/-- The 448 iterations, for `t` from 447 down to 0, with `swap = 0`. -/
def ladder : Prog isa :=
  .seq (.block [.li .r12 448, .li .r0 0]) (.loop step (.nonzero .d .r12))

/-- The swap after the loop. -/
def lastSwap : List Instr := mask ++ cswap X2 X3 ++ cswap Z2 Z3

/-! ## Inversion

`[R] = [Z2]^(p-2)` by the addition chain of `Proof/X448/Invert.lean`, as
RISC-V's `R64` implementation has it. -/

/-- `[R] = 1` (Ed448's verification uses it). -/
def one : List Instr :=
  [.li .r4 1, .li .r5 0, .store .w .r4 .r6 R] ++ storeN .r5 (R + 4) 13

/-- The inversion's temporaries: the ladder's `A`, `B`, `C`, `D`, `AA`, `BB`
and `E`, free after it. -/
def T0 : Nat := A
def T1 : Nat := B
def T2 : Nat := C
def T3 : Nat := D
def T4 : Nat := AA
def T5 : Nat := BB
def T6 : Nat := E

/-- A squaring of a run after its first: the counter `r12` down by one, then `[o] = [o]²`. -/
def sqStep (o : Nat) : Prog isa := .seq (.block [.subi .r12 .r12 1]) (mul o o o)

/-- `[o] = [x]^(2^n)`, the squarings after the first in a loop counted by `r12`. -/
def sqn (o x n : Nat) : Prog isa :=
  if n = 1 then mul o x x
  else .seq (mul o x x) (.seq (.block [.li .r12 (n - 1)]) (.loop (sqStep o) (.nonzero .d .r12)))

/-- `[R] = [z]^(2²²³ - 1)` and `[T6] = [z]^(2²²² - 1)`, through `T0`–`T5`
(`Proof/X448/Invert.lean`'s `c223`, as RISC-V's `R64` implementation has it). -/
def chain223 (z : Nat) : Prog isa :=
  .seq (sqn T0 z 1) <| .seq (mul T0 T0 z) <|          -- z^(2^2 - 1)
  .seq (sqn T1 T0 2) <| .seq (mul T1 T1 T0) <|        -- z^(2^4 - 1)
  .seq (sqn T2 T1 4) <| .seq (mul T2 T2 T1) <|        -- z^(2^8 - 1)
  .seq (sqn T3 T2 8) <| .seq (mul T3 T3 T2) <|        -- z^(2^16 - 1)
  .seq (sqn T4 T3 16) <| .seq (mul T4 T4 T3) <|       -- z^(2^32 - 1)
  .seq (sqn T5 T4 32) <| .seq (mul T5 T5 T4) <|       -- z^(2^64 - 1)
  .seq (sqn T6 T5 64) <| .seq (mul T6 T6 T5) <|       -- z^(2^128 - 1)
  .seq (sqn T6 T6 64) <| .seq (mul T6 T6 T5) <|       -- z^(2^192 - 1)
  .seq (sqn T6 T6 16) <| .seq (mul T6 T6 T3) <|       -- z^(2^208 - 1)
  .seq (sqn T6 T6 8) <| .seq (mul T6 T6 T2) <|        -- z^(2^216 - 1)
  .seq (sqn T6 T6 4) <| .seq (mul T6 T6 T1) <|        -- z^(2^220 - 1)
  .seq (sqn T6 T6 2) <| .seq (mul T6 T6 T0) <|        -- z^(2^222 - 1)
  .seq (sqn R T6 1) (mul R R z)                       -- z^(2^223 - 1)

/-- From `chain223 Z2`: `[R] = [Z2]^(p - 2)`. -/
def invTail : Prog isa :=
  .seq (sqn R R 225) <| .seq (sqn T6 T6 2) <| .seq (mul T6 T6 Z2) (mul R R T6)

/-- `[R] = [Z2]^(p-2)`, by the addition chain: 446 squarings and 15
multiplications. -/
def invert : Prog isa := .seq (chain223 Z2) invTail

/-! ## Encoding and decoding -/

/-- Limb `k` of `[X2]`, or of `[Y]` if the mask `r11` is all ones, as word
`k` of `out` (`r3`). -/
def outStep (k : Nat) : List Instr :=
  [.load .w .r5 .r6 (X2 + 4 * k), .load .w .r7 .r6 (Y + 4 * k), .logic .xor .r7 .r7 .r5,
    .logic .and .r7 .r7 .r11, .logic .xor .r5 .r5 .r7, .store .w .r5 .r3 (4 * k)]

/-- `[X2]` reduced fully, into `out` (`r3`): `y = x + 2²²⁴ + 1` into `Y`
(the carry into limb 0, `r10` = 1 into limb 7), and `y` selected (with the
mask `r11 = -carry`) if it carries out. -/
def freeze : List Instr :=
  [.li .r8 1, .li .r10 1] ++ pass .r6 Y (foldSrc X2) ++ [.li .r4 0, .sub .r11 .r4 .r8] ++
    (List.range 14).flatMap outStep

/-- Limb `k` of `u` (word `k` at `r5`) into `X1` and `X3`. -/
def decodeStep (k : Nat) : List Instr :=
  [.load .w .r7 .r5 (4 * k), .store .w .r7 .r6 (X1 + 4 * k), .store .w .r7 .r6 (X3 + 4 * k)]

/-- `x2 = 1`, `z2 = 0` and `z3 = 1`. -/
def consts : List Instr :=
  [.li .r7 1, .li .r8 0, .store .w .r7 .r6 X2, .store .w .r8 .r6 Z2, .store .w .r7 .r6 Z3] ++
  storeN .r8 (X2 + 4) 13 ++ storeN .r8 (Z2 + 4) 13 ++ storeN .r8 (Z3 + 4) 13

/-- The u-coordinate into `X1` and `X3`, and the constants. -/
def setup : List Instr := (List.range 14).flatMap decodeStep ++ consts

/-- The base point's u-coordinate, 5, into `X1` and `X3`. -/
def five : List Instr :=
  [.li .r7 5, .li .r8 0, .store .w .r7 .r6 X1, .store .w .r7 .r6 X3] ++ storeN .r8 (X1 + 4) 13 ++
    storeN .r8 (X3 + 4) 13

/-- `setup` for the base point: its u-coordinate, 5, into `X1` and `X3`, and
the constants. -/
def setupBase : List Instr := five ++ consts

/-- The bits of the byte at `r4` into `BITS` at `r9`, advancing both. -/
def bitsBody : List Instr :=
  [.lbz .r7 .r4 0] ++
  (List.range 8).flatMap (fun j => [.lsl .r8 .r7 (63 - j), .lsr .d .r8 .r8 63, .stb .r8 .r9 (BITS + j)]) ++
  [.addi .r4 .r4 1, .addi .r9 .r9 8, .subi .r11 .r11 1]

/-- `BITS[8i + j] = bit j of scalar[i]`, then the clamping: bits 0 and 1
cleared and bit 447 set. -/
def bits : Prog isa :=
  .seq (.block [.addi .r9 .r6 0, .li .r11 56])
    (.seq (.loop (.block bitsBody) (.nonzero .d .r11))
      (.block [.li .r7 0, .stb .r7 .r6 BITS, .stb .r7 .r6 (BITS + 1), .li .r7 1, .stb .r7 .r6 (BITS + 447)]))

/-- What follows the setup. -/
def afterSetup : Prog isa :=
  .seq bits <| .seq ladder <| .seq (.block lastSwap) <| .seq invert <| .seq (mul X2 X2 R) (.block freeze)

def x448 : Prog isa := .seq (.block setup) afterSetup

/-- `vg_x448_base(out = r3, scalar = r4, scratch = r5)`: the working space into
`r6`, as `vg_x448` has it, and `vg_x448` with the base point's u-coordinate, 5,
written instead of read (`setupBase`). -/
def x448Base : Prog isa := .seq (.block ([.addi .r6 .r5 0] ++ setupBase)) afterSetup

end VG.Impl.X448.PPC64LE
