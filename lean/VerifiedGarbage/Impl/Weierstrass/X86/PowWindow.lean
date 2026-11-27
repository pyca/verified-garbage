module

public import VerifiedGarbage.Impl.Weierstrass.X86.PowChain

/-!
# Powers by a public exponent, with a table of saved powers

`tabPower P F tab ops` is a fixed sequence of operations on the accumulator
and the slots `tab` (`TabOp`): squarings, multiplications by a slot, and
copies to and from one. `windowOps e bits` is the sequence for the exponent
`e < 2^bits` by a sliding window of four bits: the odd powers `x, x³, …,
x¹⁵` in the slots 0 to 7 (and `x²` in slot 8), then, from the exponent's top
bit, a run of squarings and a multiplication for each window. The exponent
is a constant of the code, so the sequence is: there is no table of bits and
nothing is selected.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.X86
open VG.X86 VG.Impl.Mont.X86 VG.Impl.Weierstrass

/-- An operation on the accumulator and the saved powers: `acc = tab[i]`,
`tab[i] = acc`, `acc = acc^(2^n)` and `acc = acc · tab[i]`. -/
inductive TabOp where
  | get (i : Nat)
  | put (i : Nat)
  | squares (n : Nat)
  | mul (i : Nat)
  deriving Repr

/-- The code of an operation, with `mul` that of the multiplication it calls. -/
def tabOpOf (P : PowCfg) (F : Impl.Weierstrass.Mont.Modulus) (tab : List Nat) (mul : Prog isa) :
    TabOp → Prog isa
  | .get i => .block (copy (2 * P.M.n) P.acc (tab.getD i 0))
  | .put i => .block (copy (2 * P.M.n) (tab.getD i 0) P.acc)
  | .squares n => squareRunOf P F mul n
  | .mul i => Mont.callOp (F.fn "mul") mul P.acc P.acc (tab.getD i 0)

def tabOp (P : PowCfg) (F : Impl.Weierstrass.Mont.Modulus) (tab : List Nat) (op : TabOp) : Prog isa :=
  tabOpOf P F tab (Mont.mulFn F.k F.m) op

def tabChainOf (P : PowCfg) (F : Impl.Weierstrass.Mont.Modulus) (tab : List Nat) (mul : Prog isa) :
    List TabOp → Prog isa
  | [] => .block []
  | op :: ops => .seq (tabOpOf P F tab mul op) (tabChainOf P F tab mul ops)

/-- The operations, one after the other: the code of the multiplication they call is
computed once. -/
def tabChain (P : PowCfg) (F : Impl.Weierstrass.Mont.Modulus) (tab : List Nat) (ops : List TabOp) :
    Prog isa :=
  tabChainOf P F tab (Mont.mulFn F.k F.m) ops

/-- `[acc] = [base]^e` for the exponent `e` that `ops` reach from the
accumulator holding the base and no saved power. -/
def tabPower (P : PowCfg) (F : Impl.Weierstrass.Mont.Modulus) (tab : List Nat)
    (ops : List TabOp) : Prog isa :=
  .seq (.block (copy (2 * P.M.n) P.acc P.base ++ copy (2 * P.M.n) P.tmp P.base))
    (tabChain P F tab ops)

/-- `k` squarings before `ops`. -/
def squaresThen (k : Nat) (ops : List TabOp) : List TabOp :=
  if k = 0 then ops else .squares k :: ops

/-- The operations that leave the accumulator at `x^(e 2^k)`, then `ops`, for
`0 < e < 2^fuel` and slot `i` holding `x^(2i+1)` for `i < 8`: from the
exponent's low bit, a zero is one more squaring to come, and a one is the low
bit of a window of four bits, whose power the accumulator is multiplied by
after the four squarings that follow the bits above it. The top window's
power is copied. -/
def windowFrom : Nat → Nat → Nat → List TabOp → List TabOp
  | 0, _, _, ops => ops
  | fuel + 1, e, k, ops =>
    if e % 2 = 0 then windowFrom fuel (e / 2) (k + 1) ops
    else if e < 16 then .get (e / 2) :: squaresThen k ops
    else windowFrom fuel (e / 16) 4 (.mul (e % 16 / 2) :: squaresThen k ops)

/-- The operations that leave the accumulator `x^a` at `x^((a 2^f + e) 2^k)`,
then `ops`, for `e < 2^f` and the same saved powers: as `windowFrom`, with
every window's power multiplied in, and the squarings of the zeros above the
top window. A window is of four bits, or of the bits left if they are
fewer. -/
def windowAdd : Nat → Nat → Nat → List TabOp → List TabOp
  | 0, _, k, ops => squaresThen k ops
  | f + 4, e, k, ops =>
    if e % 2 = 0 then windowAdd (f + 3) (e / 2) (k + 1) ops
    else windowAdd f (e / 16) 4 (.mul (e % 16 / 2) :: squaresThen k ops)
  | f + 1, e, k, ops =>
    if e % 2 = 0 then windowAdd f (e / 2) (k + 1) ops
    else squaresThen (f + 1) (.mul (e / 2) :: squaresThen k ops)

/-- The odd powers below 16 in slots 0 to 7, from the accumulator holding
the base, with `x²` in slot 8. -/
def windowTable : List TabOp :=
  [.put 0, .squares 1, .put 8, .mul 0, .put 1, .mul 8, .put 2, .mul 8, .put 3, .mul 8, .put 4,
    .mul 8, .put 5, .mul 8, .put 6, .mul 8, .put 7]

/-- The power `e`, `0 < e < 2^bits`, by a sliding window of four bits. -/
def windowOps (e bits : Nat) : List TabOp := windowTable ++ windowFrom bits e 0 []

end VG.Impl.Weierstrass.X86
