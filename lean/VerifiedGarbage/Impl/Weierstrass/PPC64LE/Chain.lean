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
for `i` from 1 to `j`. -/
def odds : Nat → Prog isa
  | 0 => .block []
  | j + 1 => .seq (odds j) (mulCall S (P.slot (j + 1)) (P.slot j) (P.slot 8))

/-- The table: `x`, `x²`, then the odd powers. -/
def table : Prog isa :=
  .seq (.block (copy P.M.n (P.slot 0) P.base)) <|
  .seq (mulCall S (P.slot 8) P.base P.base) (odds P S 7)

/-- `acc = acc^(2^s)`. -/
def squares (s : Nat) : Prog isa :=
  .seq (.block [.li .r31 s]) (.loop (.seq (.block [decCounter]) (mulCall S P.acc P.acc P.acc)) more)

/-- A step: `acc = acc^(2^s) x^d`. -/
def step : Nat × Nat → Prog isa
  | (s, d) => .seq (if s = 0 then .block [] else squares P S s)
      (if d = 0 then .block [] else mulCall S P.acc P.acc (P.slot ((d - 1) / 2)))

/-- The steps in order. -/
def steps : List (Nat × Nat) → Prog isa
  | [] => .block []
  | st :: rest => .seq (step P S st) (steps rest)

/-- `[acc] = [base]^e`. -/
def pow : Prog isa :=
  .seq (table P S) (.seq (.block (copy P.M.n P.acc (P.slot ((P.first - 1) / 2)))) (steps P S P.steps))

end ChainCfg

end VG.Impl.Weierstrass.PPC64LE
