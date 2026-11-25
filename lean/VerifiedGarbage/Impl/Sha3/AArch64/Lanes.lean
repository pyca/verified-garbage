module

public import VerifiedGarbage.Impl.Sha3.AArch64

/-!
# Keccak-f[1600] on AArch64: where the lanes are

Both implementations (general registers, `Scalar/Round.lean`; vector
registers, `Sha3/Vector.lean`) are a loop of two rounds that keeps the 25
lanes in 25 registers and works in place.

A round writes lane `(x, y)` of its output to the register that held, before
the round, lane `(2x + y, 2x + 3y)` (`swap`), which is one of the five lanes
output row `y` is computed from: so a row is written over its own inputs.
Modulo 5 that map is an involution (the matrix `[[2, 1], [2, 3]]` has square
1), so after two rounds every lane is again where it began, with no moves,
and the code of the two rounds is the body of a loop.

Within a row, with `B₀ … B₄` its inputs from output column `2y` on, the
output of column `2y + k` goes to the register of `B₂ₖ`: a cycle
`1 → 2 → 4 → 3 → 1` and a fixed point. The cycle is broken where θ is
applied: that XOR can write a register other than its operand's, so `B₁`
(and, in vector registers, `B₃`) is computed into a spare register just
before its row. Those inputs are column 1's lanes (and 3's) before the round,
in every row, so that only `D₁` (and `D₃`) stays live among the rows.
-/

@[expose] public section

namespace VG.Impl.Sha3.AArch64.Lanes

open VG.Impl.Sha3 (rhoOff)

/-- Lane `(x, y)`'s index. -/
def idx (x y : Nat) : Nat := x % 5 + 5 * (y % 5)

/-- The lane whose register output lane `i` is written to. -/
def swap (i : Nat) : Nat := idx (2 * (i % 5) + i / 5) (2 * (i % 5) + 3 * (i / 5))

/-- The home register of lane `i` before round `r` of the loop's body. -/
def home (r i : Nat) : Nat := if r % 2 = 0 then i else swap i

/-- The lane of `θ`'s output that is `Bₖ` of row `y` (column `2y + k` after ρ and π). -/
def rowSrc (y k : Nat) : Nat := idx (k + 2 * y + 3 * y) (k + 2 * y)

/-- The lane that is output `k` of row `y`. -/
def rowOut (y k : Nat) : Nat := idx (k + 2 * y) y

end VG.Impl.Sha3.AArch64.Lanes
