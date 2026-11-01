module

public import VerifiedGarbage.Impl.Weierstrass.Slots
public import VerifiedGarbage.Spec.Weierstrass.Mont
public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# Short Weierstrass curves on RISC-V: field programs, scalar multiplication, powers

Code for curves whose field elements are numbers of 64-bit words in slots
of the working space, in Montgomery form, and whose arithmetic modulo `p`
or `n` is calls of the functions of `Spec/Weierstrass/Mont.lean` (`Field`:
their names and code), which use the bytes of the working space from
`ownAt k` to 4096 for themselves. The working space's base is in `s0`,
which the callees keep (a callee-saved register); a point is three slots,
projective coordinates `(X : Y : Z)`. As on PPC64LE
(`Impl/Weierstrass/PPC64LE.lean`):

* `callOp`: `[o] = f([a], [b])` by a call of `f` with `a0 = s0` and the
  offsets in `a1`–`a3` (`li`: every slot is below 2048); `fprog`: field
  operations on slots (`FOp`, `Impl/Weierstrass/Slots.lean`), such as the
  complete addition `rcb`, one after the other.
* `ladder`: `[k]G` by double-and-add from the top bit: `D = R + R`,
  `T = D + G` and `R = D` or `T` by a mask of the bit (in `a7`), so every
  iteration does the same.
* `pow`: `x^e` by square-and-multiply over the bits of a public exponent,
  also always multiplying and selecting by a mask.

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
  S : Spec.Weierstrass.Mont.Modulus
  mul : Prog isa
  add : Prog isa
  sub : Prog isa

/-! ## Calls -/

/-- `[o] = f([a], [b])` by a call of `f`, whose code is `body`, on the
working space in `s0`. -/
def callOp (f : String) (body : Prog isa) (o a b : Nat) : Prog isa :=
  .seq (.block [.addi .a0 wb 0, .li .a1 o, .li .a2 a, .li .a3 b]) (.call f body)

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

/-- `[o] = [a]` if the mask `a7` is zero, `[b]` if it is all ones, `k`
64-bit words, through `t0` and `t1`. -/
def sel : Nat → Nat → Nat → Nat → List Instr
  | 0, _, _, _ => []
  | k + 1, o, a, b => [.load .d .t0 wb a, .load .d .t1 wb b, .logic .xor .t1 .t1 .t0,
      .logic .and .t1 .t1 .a7, .logic .xor .t0 .t0 .t1, .store .d .t0 wb o] ++ sel k (o + 8) (a + 8) (b + 8)

/-- `o = a` or `b`, a point of `n`-word coordinates, by the mask `a7`. -/
def selPt (n : Nat) (o a b : Pt) : List Instr :=
  sel n o.x a.x b.x ++ sel n o.y a.y b.y ++ sel n o.z a.z b.z

/-- `[o] = [a]`, `k` 64-bit words, through `t0`. -/
def copy : Nat → Nat → Nat → List Instr
  | 0, _, _ => []
  | k + 1, o, a => [.load .d .t0 wb a, .store .d .t0 wb o] ++ copy k (o + 8) (a + 8)

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

end VG.Impl.Weierstrass.RISCV64
