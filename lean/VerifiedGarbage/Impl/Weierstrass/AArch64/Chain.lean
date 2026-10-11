module

public import VerifiedGarbage.Impl.Weierstrass.AArch64
public import VerifiedGarbage.Impl.Weierstrass.Chain

/-!
# Short Weierstrass curves on AArch64: powers by sliding windows

`[acc] = [base]^e` for the chain of `e` (`ChainCfg`, `Impl/Weierstrass/Chain.lean`):
the table `x, x³, …, x¹⁵` (and `x²`) in its slots, `acc` the first window's
power, then each step's squarings, by a loop counting `x19` down, and its
multiplication by the table. The exponent is the code's, so nothing depends on
the numbers.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.AArch64

open VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass

namespace ChainCfg

variable (P : Weierstrass.ChainCfg)

/-- The table: `x`, `x²`, then `x^(2 i + 1) = x^(2 i - 1) x²`. -/
def table : List Instr :=
  copy P.M.n (P.slot 0) P.base ++ Mont.AArch64.mul P.M (P.slot 8) P.base P.base ++
    (List.range 7).flatMap fun i => Mont.AArch64.mul P.M (P.slot (i + 1)) (P.slot i) (P.slot 8)

/-- `acc = acc^(2^s)`. -/
def squares (s : Nat) : Prog isa :=
  .seq (.block [.movz .x .x19 (BitVec.ofNat 16 s) 0])
    (.loop (.block (decCounter :: Mont.AArch64.mul P.M P.acc P.acc P.acc)) (.nonzero .x .x19))

/-- A step: `acc = acc^(2^s) x^d`. -/
def step : Nat × Nat → Prog isa
  | (s, d) => .seq (if s = 0 then .block [] else squares P s)
      (.block (if d = 0 then [] else Mont.AArch64.mul P.M P.acc P.acc (P.slot ((d - 1) / 2))))

/-- The steps in order. -/
def steps : List (Nat × Nat) → Prog isa
  | [] => .block []
  | st :: rest => .seq (step P st) (steps rest)

/-- `[acc] = [base]^e`. -/
def pow : Prog isa :=
  .seq (.block (table P ++ copy P.M.n P.acc (P.slot ((P.first - 1) / 2)))) (steps P P.steps)

end ChainCfg

end VG.Impl.Weierstrass.AArch64
