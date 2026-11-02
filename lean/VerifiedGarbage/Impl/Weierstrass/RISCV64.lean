module

public import VerifiedGarbage.Impl.Weierstrass.Chain
public import VerifiedGarbage.Impl.Weierstrass.Slots
public import VerifiedGarbage.Impl.Weierstrass.Layout.Mont
public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# Short Weierstrass curves on RISC-V: field programs, scalar multiplication, powers

Code for curves whose field elements are numbers of 64-bit words in slots
of the working space, in Montgomery form, and whose arithmetic modulo `p`
or `n` is calls of the functions of `Proof/Weierstrass/MontContract.lean` (`Field`:
their names and code), which use the bytes of the working space from
`ownAt k` to 4096 for themselves. The working space's base is in `s0`,
which the callees keep (a callee-saved register); a point is three slots,
projective coordinates `(X : Y : Z)`. As on PPC64LE
(`Impl/Weierstrass/PPC64LE.lean`):

* `ldAt`, `sdAt`, `liAt`: a load, a store or an offset in a register, for
  offsets up to 4094, past what an instruction's 12 bits (signed) reach: from
  2048 on, through `base + 2047`. A load computes it in its own destination,
  a store in its base, which it restores, so neither writes another
  register, and below 2048 each is the one instruction.
* `callOp`: `[o] = f([a], [b])` by a call of `f` with `a0 = s0` and the
  offsets in `a1`–`a3`; `fprog`: field
  operations on slots (`FOp`, `Impl/Weierstrass/Slots.lean`), such as the
  complete addition `rcb`, one after the other.
* `ladder`: `[k]G` by double-and-add from the top bit: `D = R + R`,
  `T = D + G` and `R = D` or `T` by a mask of the bit (in `a7`), so every
  iteration does the same.
* `pow`: `x^e` by square-and-multiply over the bits of a public exponent,
  also always multiplying and selecting by a mask.
* `chainPow`: `x^e` for an exponent fixed when the code is generated, by its
  chain of sliding windows (`ChainCfg`, `Impl/Weierstrass/Chain.lean`): the
  table `x, x³, …, x¹⁵` and `x²` (`x` multiplied by `R mod m` first, so that
  the table's numbers are below the modulus, as the multiplication's second
  operand must be), then each step's squarings, by a loop
  counting `s1` down, and its multiplication by the table.

The bit of iteration `j` (the counter, in `s1`) is read from the number
itself (`bitMask`): its word `j / 64`, at the slot plus `8 (j >>> 6)`,
shifted right by `j` (`srl` takes `j mod 64`), so no table of bits is
needed. The loops' only branches are on `s1`, and every address is `s0`
plus a constant, or plus `8 (s1 >>> 6)`: nothing but `s0` may affect
timing.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.RISCV64

open VG.RISCV64 VG.Impl.Weierstrass

/-- The working space's base. -/
abbrev wb : Reg := .s0

/-- The loops' counter. -/
abbrev ctr : Reg := .s1

/-- The functions of a modulus: its contract's names (`S`), and their code. -/
structure Field where
  S : Impl.Weierstrass.Mont.Modulus
  mul : Prog isa
  add : Prog isa
  sub : Prog isa

/-! ## Offsets past 2047 -/

/-- `ld rd, off(base)`, for `off < 4095`: from 2048 on, `rd = base + 2047`
first. -/
def ldAt (rd base : Reg) (off : Nat) : List Instr :=
  if off < 2048 then [.load .d rd base off] else [.addi rd base 2047, .load .d rd rd (off - 2047)]

/-- `sd t, off(base)`, for `off < 4095`: from 2048 on, `base` moved up by
2047 around the store (`t` another register). -/
def sdAt (t base : Reg) (off : Nat) : List Instr :=
  if off < 2048 then [.store .d t base off]
  else [.addi base base 2047, .store .d t base (off - 2047), .addi base base (-2047)]

/-- `rd = v`, for `v < 4095`: from 2048 on, `2047` and then `v - 2047`
added. -/
def liAt (rd : Reg) (v : Nat) : List Instr :=
  if v < 2048 then [.li rd v] else [.li rd 2047, .addi rd rd ((v - 2047 : Nat) : Int)]

/-! ## Calls -/

/-- `[o] = f([a], [b])` by a call of `f`, whose code is `body`, on the
working space in `s0`. -/
def callOp (f : String) (body : Prog isa) (o a b : Nat) : Prog isa :=
  .seq (.block (.addi .a0 wb 0 :: (liAt .a1 o ++ (liAt .a2 a ++ liAt .a3 b)))) (.call f body)

/-- `[o] = [a] [b] R⁻¹ mod m`. -/
def mulCall (F : Field) (o a b : Nat) : Prog isa := callOp (F.S.fn "mul") F.mul o a b

/-- `[o] = [a] + [b] mod m`. -/
def addCall (F : Field) (o a b : Nat) : Prog isa := callOp (F.S.fn "add") F.add o a b

/-- `[o] = [a] - [b] mod m`. -/
def subCall (F : Field) (o a b : Nat) : Prog isa := callOp (F.S.fn "sub") F.sub o a b

/-- The code of a field operation: a call of its function. -/
def opCode (F : Field) : FOp → Prog isa
  | .mul o a b => mulCall F o a b
  | .add o a b => addCall F o a b
  | .sub o a b => subCall F o a b

/-- Programs one after the other. -/
def progs : List (Prog isa) → Prog isa
  | [] => .block []
  | [p] => p
  | p :: ps => .seq p (progs ps)

/-- A straight-line sequence of field operations. -/
def fprog (F : Field) (ops : List FOp) : Prog isa := progs (ops.map (opCode F))

/-! ## Copies and selections -/

/-- A word of `[o] = [a]` if the mask `a7` is zero, `[b]` if it is all
ones, through `t0` and `t1`. -/
def selWord (o a b : Nat) : List Instr :=
  ldAt .t0 wb a ++ ldAt .t1 wb b ++ [.logic .xor .t1 .t1 .t0, .logic .and .t1 .t1 .a7, .logic .xor .t0 .t0 .t1] ++
    sdAt .t0 wb o

/-- `[o] = [a]` if the mask `a7` is zero, `[b]` if it is all ones, `k`
64-bit words, through `t0` and `t1`. -/
def sel : Nat → Nat → Nat → Nat → List Instr
  | 0, _, _, _ => []
  | k + 1, o, a, b => selWord o a b ++ sel k (o + 8) (a + 8) (b + 8)

/-- `o = a` or `b`, a point of `n`-word coordinates, by the mask `a7`. -/
def selPt (n : Nat) (o a b : Pt) : List Instr :=
  sel n o.x a.x b.x ++ sel n o.y a.y b.y ++ sel n o.z a.z b.z

/-- `[o] = [a]`, `k` 64-bit words, through `t0`. -/
def copy : Nat → Nat → Nat → List Instr
  | 0, _, _ => []
  | k + 1, o, a => (ldAt .t0 wb a ++ sdAt .t0 wb o) ++ copy k (o + 8) (a + 8)

/-- The mask `a7 = -bit` of bit `s1` of the number at `src`, through `t0`–`t2`:
its word `s1 >>> 6` shifted right by `s1 mod 64`. -/
def bitMask (src : Nat) : List Instr :=
  [.shift .srl .d .t0 ctr 6, .shift .sll .d .t0 .t0 3, .add .t0 .t0 wb, .load .d .t1 .t0 src,
    .shiftReg .srl .d .t1 .t1 ctr, .logicImm .and .t1 .t1 1, .li .t2 0, .sub .a7 .t2 .t1]

/-- `s1 -= 1`. -/
def decCounter : Instr := .addi ctr ctr (-1)

/-- The loops' condition: `s1` is not zero. -/
abbrev more : Cond := .nonzero ctr

/-! ## Scalar multiplication and powers -/

/-- What the ladder needs: the field's slots and points (`LadderCfg`, whose
`bits` is the slot of the scalar here). -/
abbrev Ladder := LadderCfg

/-- One iteration of the ladder, for the bit `t = s1 - 1`: `D = R + R`,
`T = D + G`, then `R = T` if bit `t` is set, else `D`. -/
def ladderBody (L : LadderCfg) (F : Field) : Prog isa :=
  .seq (.block [decCounter]) <| .seq (fprog F (rcb L.S L.R L.R L.D)) <|
    .seq (fprog F (rcb L.S L.D L.G L.T)) <|
    .block (bitMask L.bits ++ selPt L.M.n L.R L.D L.T)

/-- The ladder over the bits `nbits - 1` down to 0 of the number at
`L.bits`, from `R` as set up by the caller (the point at infinity). -/
def ladder (L : LadderCfg) (F : Field) : Prog isa :=
  .seq (.block [.li ctr L.nbits]) (.loop (ladderBody L F) more)

/-- One iteration: `acc = acc²`, `tmp = base · acc`, and `acc = tmp` if the
exponent's bit `s1 - 1` is set (the base the multiplication's first operand,
which the functions take below `2^(64 k)` rather than below the modulus). -/
def powBody (P : PowCfg) (F : Field) : Prog isa :=
  .seq (.block [decCounter]) <| .seq (mulCall F P.acc P.acc P.acc) <|
  .seq (mulCall F P.tmp P.base P.acc) <|
    .block (bitMask P.bits ++ sel P.M.n P.acc P.acc P.tmp)

/-- `[acc] = [base]^e` (in Montgomery form), for the exponent at `P.bits`,
from its bit `nbits - 1`. -/
def pow (P : PowCfg) (F : Field) : Prog isa :=
  .seq (.block (copy P.M.n P.acc P.one ++ [.li ctr P.nbits])) (.loop (powBody P F) more)

/-! ## Powers by a chain -/

namespace ChainR

variable (P : ChainCfg) (F : Field)

/-- The odd powers after `x`: `x^(2 i + 3) = x^(2 i + 1) x²`, for `i < c`. -/
def odd : Nat → Prog isa
  | 0 => .block []
  | c + 1 => .seq (odd c) (mulCall F (P.slot (c + 1)) (P.slot c) (P.slot 8))

/-- The table: `x` (reduced, by a multiplication by `R mod m`, at `one`),
`x²`, then `x³ … x¹⁵`. -/
def table (one : Nat) : Prog isa :=
  .seq (mulCall F (P.slot 0) P.base one) (.seq (mulCall F (P.slot 8) (P.slot 0) (P.slot 0)) (odd P F 7))

/-- `acc = acc^(2^s)`, by a loop counting `s1` from `s` down. -/
def squares (s : Nat) : Prog isa :=
  .seq (.block [.li ctr s]) (.loop (.seq (.block [decCounter]) (mulCall F P.acc P.acc P.acc)) more)

/-- A step: `acc = acc^(2^s) x^d`. -/
def step : Nat × Nat → Prog isa
  | (s, d) => .seq (if s = 0 then .block [] else squares P F s)
      (if d = 0 then .block [] else mulCall F P.acc P.acc (P.slot ((d - 1) / 2)))

/-- The steps in order. -/
def steps : List (Nat × Nat) → Prog isa
  | [] => .block []
  | st :: rest => .seq (step P F st) (steps rest)

end ChainR

/-- `[acc] = [base]^e` (in Montgomery form) for the chain of `e`, with
`R mod m` at `one`. -/
def chainPow (P : ChainCfg) (one : Nat) (F : Field) : Prog isa :=
  .seq (ChainR.table P F one) (.seq (.block (copy P.M.n P.acc (P.slot ((P.first - 1) / 2)))) (ChainR.steps P F P.steps))

end VG.Impl.Weierstrass.RISCV64
