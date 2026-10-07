import VerifiedGarbage.Impl.Weierstrass.AArch64
import VerifiedGarbage.Impl.Weierstrass.Chain

/-!
# Short Weierstrass curves on AArch64: powers by sliding windows

`[acc] = [base]^e` for the chain of `e` (`ChainCfg`, `Impl/Weierstrass/Chain.lean`):
the table `x, x³, …, x¹⁵` (and `x²`) in its slots, `acc` the first window's
power, then the steps by a loop: `x19` counts the steps down in its top half
and each step's squarings in its bottom half, and a tree of `cbz` on the
bits of the step's index sets its count of squarings and copies its
multiplier from the table into `x²`'s slot (`tree`). The chain is unrolled
only in that tree's leaves, two instructions and a copy each. The exponent
is the code's, so nothing depends on the numbers: every address is `x0` plus
a constant, and every branch is on a counter.
-/

namespace VG.Impl.Weierstrass.AArch64

open VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass

namespace ChainCfg

variable (P : Weierstrass.ChainCfg)

/-- The table: `x`, `x²`, then `x^(2 i + 1) = x^(2 i - 1) x²`. -/
def table : List Instr :=
  copy P.M.n (P.slot 0) P.base ++ Mont.AArch64.mul P.M (P.slot 8) P.base P.base ++
    (List.range 7).flatMap fun i => Mont.AArch64.mul P.M (P.slot (i + 1)) (P.slot i) (P.slot 8)

/-- Step `i` of the loop, which counts down: the chain's step `L - 1 - i`
(`L` steps), or a filler past them. -/
def stepAt (i : Nat) : Nat × Nat := P.steps.reverse.getD i (1, 1)

/-- The steps' count, in the top half of `x19`. -/
def len : Nat := P.steps.length

/-- A step's data: its squarings added to the bottom half of `x19`, and its
multiplier, the table's `x^d`, copied into slot `8` (`x²`, which only the
table needs). -/
def leaf (st : Nat × Nat) : List Instr :=
  [.movz .x .x2 (BitVec.ofNat 16 st.1) 0, .add .x .x19 .x19 .x2] ++
    copy P.M.n (P.slot 8) (P.slot ((st.2 - 1) / 2))

/-- The data of step `x1` among `[base, base + 2^b)`, by its bits from `b - 1`
down (`cbz` on each, shifted down into `x2`), but for bits that no step below
`len` sets. -/
def tree : Nat → Nat → Prog isa
  | 0, base => .block (leaf P (stepAt P base))
  | b + 1, base =>
    if len P ≤ base + 2 ^ b then tree b base
    else .seq (.block [.lsr .x .x2 .x1 b, .movz .x .x3 1 0, .logic .and .x .x2 .x2 .x3])
      (.ite (.zero .x .x2) (tree b base) (tree b (base + 2 ^ b)))

/-- The bits of the steps' indices. -/
def depth : Nat := Nat.log2 (len P - 1) + 1

/-- A step, with `x19 = 2³² (i + 1)`: `x19 = 2³² i`, then the step's data
(`tree`), its squarings, counting the bottom half of `x19` down to zero, and
its multiplication. -/
def body : Prog isa :=
  .seq (.block [.movz .x .x3 1 2, .sub .x .x19 .x19 .x3, .lsr .x .x1 .x19 32]) <|
  .seq (tree P (depth P) 0) <|
  .seq (.loop (.block (decCounter :: Mont.AArch64.mul P.M P.acc P.acc P.acc)) (.nonzero .w .x19)) <|
  .block (Mont.AArch64.mul P.M P.acc P.acc (P.slot 8))

/-- `[acc] = [base]^e`: the table and the first window's power, then the
steps by a loop counting the top half of `x19` down. -/
def pow : Prog isa :=
  .seq (.block (table P ++ copy P.M.n P.acc (P.slot ((P.first - 1) / 2)) ++
    [.movz .x .x19 (BitVec.ofNat 16 (len P)) 2])) (.loop (body P) (.nonzero .x .x19))

end ChainCfg

end VG.Impl.Weierstrass.AArch64
