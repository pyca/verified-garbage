module

public import VerifiedGarbage.Impl.Weierstrass.PPC64LE
public import VerifiedGarbage.Impl.Weierstrass.Chain

/-!
# Short Weierstrass curves on PPC64LE: powers by sliding windows

`[acc] = [base]^e` for the chain of `e` (`ChainCfg`, `Impl/Weierstrass/Chain.lean`),
as on AArch64 (`Impl/Weierstrass/AArch64/Chain.lean`): the table
`x, x³, …, x¹⁵` (and `x²`) in its slots, `acc` the first window's power, then
each step's squarings, by a loop counting `r31` down, and its multiplication by
the table, by calls of the functions of `S`. The exponent is the code's, so
nothing depends on the numbers.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.PPC64LE

open VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass

namespace ChainCfg

variable (P : Weierstrass.ChainCfg) (S : Impl.Weierstrass.Mont.Modulus)

/-- The table's odd powers after `x` and `x²`: `x^(2 i + 1) = x^(2 i - 1) x²`
for `i` from 1 to `j`, by calls of the multiplication, whose code is `mul`. (The table, and the
steps, compute it once.) -/
def oddsOf (mul : Prog isa) : Nat → Prog isa
  | 0 => .block []
  | j + 1 => .seq (oddsOf mul j) (callOp (S.fn "mul") mul (P.slot (j + 1)) (P.slot j) (P.slot 8))

/-- `oddsOf`, with the multiplication's code. -/
def odds (j : Nat) : Prog isa := oddsOf P S (Mont.mulFn S.k S.m) j

/-- The table: `x`, `x²`, then the odd powers. -/
def table : Prog isa :=
  .seq (.block (copy P.M.n (P.slot 0) P.base)) <|
  .seq (mulCall S (P.slot 8) P.base P.base) (odds P S 7)

/-- `acc = acc^(2^s)`, by calls of the multiplication, whose code is `mul`. -/
def squaresOf (mul : Prog isa) (s : Nat) : Prog isa :=
  .seq (.block [.li .r31 s])
    (.loop (.seq (.block [decCounter]) (callOp (S.fn "mul") mul P.acc P.acc P.acc)) more)

/-- `acc = acc^(2^s)`. -/
def squares (s : Nat) : Prog isa := squaresOf P S (Mont.mulFn S.k S.m) s

/-- A step: `acc = acc^(2^s) x^d`, by calls of the multiplication, whose code is `mul`. -/
def stepOf (mul : Prog isa) : Nat × Nat → Prog isa
  | (s, d) => .seq (if s = 0 then .block [] else squaresOf P S mul s)
      (if d = 0 then .block [] else callOp (S.fn "mul") mul P.acc P.acc (P.slot ((d - 1) / 2)))

/-- A step: `acc = acc^(2^s) x^d`. -/
def step (st : Nat × Nat) : Prog isa := stepOf P S (Mont.mulFn S.k S.m) st

/-- The steps in order, by calls of the multiplication, whose code is `mul`. -/
def stepsOf (mul : Prog isa) : List (Nat × Nat) → Prog isa
  | [] => .block []
  | st :: rest => .seq (stepOf P S mul st) (stepsOf mul rest)

/-- The steps in order. -/
def steps (l : List (Nat × Nat)) : Prog isa := stepsOf P S (Mont.mulFn S.k S.m) l

/-- `[acc] = [base]^e`. -/
def pow : Prog isa :=
  .seq (table P S) (.seq (.block (copy P.M.n P.acc (P.slot ((P.first - 1) / 2)))) (steps P S P.steps))

/-- `pow` as the code of a function of its own: its calls of `S`'s functions
write the link register, so it keeps it at `sv` in the working space around
them (through `r0`, which they may write). -/
def fn (sv : Nat) : Prog isa :=
  .seq (.block [.mflr .r0, .store .d .r0 wb sv]) (.seq (pow P S) (.block [.load .d .r0 wb sv, .mtlr .r0]))

/-- A call of the function `S.fn "inv"`, whose code is `fn P S sv`: one copy
of the chain for all of its callers. -/
def call (sv : Nat) : Prog isa := .call (S.fn "inv") (fn P S sv)

end ChainCfg

end VG.Impl.Weierstrass.PPC64LE
