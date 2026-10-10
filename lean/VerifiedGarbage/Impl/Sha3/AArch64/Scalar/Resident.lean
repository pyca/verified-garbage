import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Unrolled
import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.Vector.Resident

/-!
# The scalar sponge absorbing whole blocks with the state in registers

`bulk` runs where the SHA-3 resident absorber's does (`Sha3.Vector.Resident`:
at an aligned position, with at least one whole block of data; `x0` =
state, `x1` = `x5` = scratch, `x3` = data, `x4` = its length, `x6` = the
rate). It loads the 25 lanes into general registers once, and for each
whole block XORs the block's words into them and runs the unrolled rounds
of `unrolledPermute`, then stores them once. The callee-saved registers and
the pointers are kept in AdvSIMD registers, as by the permutation's
boundary (`Boundary.save`), and the data pointer, the length left and the
rate in v19–v21; nothing is written to memory but the state at the end.
-/

namespace VG.Impl.Sha3.AArch64.Scalar.Resident

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Scalar
open VG.Impl.Sha3.AArch64 (mov)

/-- The data pointer, the length left and the rate, kept in AdvSIMD registers. -/
def keep : List Instr :=
  [.vop (.dup .d2 .v19 .x3), .vop (.dup .d2 .v20 .x4), .vop (.dup .d2 .v21 .x6)]

def setup : List Instr := Boundary.save ++ keep ++ Boundary.load

/-- XOR the `n` words of data at `x27` into lanes `0 … n-1`, through `x26`. -/
def absorbLanes (n : Nat) : List Instr :=
  (List.range n).flatMap fun i => [.ldr .x .x26 .x27 (8 * i), .logic .eor .x (laneReg i) (laneReg i) .x26]

/-- The block of the rate in `x28`, one of `rates` or else 168. -/
def selectFrom (rates : List Nat) : Prog isa :=
  rates.foldr (fun rate rest =>
    .seq (.block [.subImm .x .x26 .x28 rate])
      (.ite (.zero .x .x26) (.block (absorbLanes (rate / 8))) rest))
    (.block (absorbLanes 21))

/-- The rate's block, selected on the rate in `x28`: one of the five FIPS 202
rates (the last, 168, without a test). -/
def select : Prog isa := selectFrom [72, 104, 136, 144]

def xorBlock : Prog isa := .seq (.block [.umov .x .x27 .v19 0, .umov .x .x28 .v21 0]) select

/-- Advance the data pointer and the length by the rate, and set `x26 = 0`
exactly when another whole block is left (the test of `Sha3.Vector.Resident`). -/
def advance : List Instr :=
  [.umov .x .x26 .v19 0, .umov .x .x27 .v20 0, .umov .x .x28 .v21 0,
   .add .x .x26 .x26 .x28, .sub .x .x27 .x27 .x28,
   .vop (.dup .d2 .v19 .x26), .vop (.dup .d2 .v20 .x27),
   .sub .x .x26 .x27 .x28, .lsr .x .x26 .x26 63]

def body : Prog isa := .seq xorBlock (.seq (.block unrolledRounds) (.block advance))

/-- Store the lanes, restore the callee-saved registers, and the arguments
`Sha3.Vector.Resident`'s caller expects (`x2 = 0`, `x5 = x1`). -/
def finish : List Instr :=
  Boundary.store ++ Boundary.restore ++
  [.umov .x .x0 .v30 0, .umov .x .x1 .v31 0, .umov .x .x3 .v19 0, .umov .x .x4 .v20 0,
   .umov .x .x6 .v21 0, mov .x5 .x1, .movz .x .x2 0 0]

def bulk : Prog isa := .seq (.block setup) (.seq (.loop body (.zero .x .x26)) (.block finish))

end VG.Impl.Sha3.AArch64.Scalar.Resident
