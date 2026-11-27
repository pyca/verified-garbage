module

public import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.Common

/-!
# ML-DSA on AArch64: an iteration of `RejBoundedPoly`'s loop

One iteration of `RejBoundedPoly`'s loop on a byte of SHAKE256 output
(`rbBody η`, one for each `η`), which `Optimized/BoundedFour.lean` runs on
the bytes its vector steps leave: with `x2` at the byte, `x3` at coefficient
`j` of `a`, `x4` = `256 - j` and `x5` counting down, while `j < 256`, each
half-byte `b` of the byte (low first, in `x7`) is tried: the coefficient
`η - (b mod 5)` or `η - b` modulo `q` is stored as coefficient `j`, and `j`
is incremented if `CoeffFromHalfByte` accepts `b` (`b < 15` for `η = 2`,
`b < 9` for `η = 4`); the high half-byte only if `j < 256` still.

A try has no branch and no table (`rbTry`): `b mod 5` is computed by
subtracting 10 and then 5, and adding them back where the result is
negative (its sign bit, times the constant, by `madd`), and `q` is added to
`η - (b mod 5)` where that is negative. So the iteration's branches and the
addresses of its stores depend only on `j`, which counts the half-bytes
accepted, which the contract lets it leak, not on the coefficients.
-/

@[expose] public section

namespace VG.Impl.MlDsa.AArch64.Sample

open VG.AArch64
open VG.Impl.MlKem.AArch64 (mov csub)

/-- The coefficient of the half-byte `b` (in `x7`) modulo `q`, in `x13`:
`η - (b mod 5)` for `η = 2` (for `b < 15`), `η - b` for `η = 4` (for
`b < 9`), with `η` in `x10`, `q` in `x9`, 10 in `x16` and 5 in `x17`. -/
def rbVal : Nat → List Instr
  | 2 => mov .x13 .x7 :: csub .x13 .x14 .x16 ++ csub .x13 .x14 .x17 ++
      ([.sub .x .x13 .x10 .x13, .lsr .x .x14 .x13 63, .madd .x .x13 .x14 .x9 .x13] : List Instr)
  | _ => [.sub .x .x13 .x10 .x7, .lsr .x .x14 .x13 63, .madd .x .x13 .x14 .x9 .x13]

/-- The half-bytes `CoeffFromHalfByte` accepts: those less than this. -/
def rbBound : Nat → Nat
  | 2 => 15
  | _ => 9

/-- Try the half-byte `b` in `x7`: whether it is accepted (less than the
bound in `x15`) in `x12`, its coefficient stored as coefficient `j`, and `j`
incremented if it is accepted. -/
def rbTry (η : Nat) : List Instr :=
  ([.sub .x .x8 .x7 .x15, .lsr .x .x12 .x8 63] : List Instr) ++ rbVal η ++
    ([.str .w .x13 .x3 0, .lsl .x .x14 .x12 2, .add .x .x3 .x3 .x14, .sub .x .x4 .x4 .x12] : List Instr)

/-- The byte at `x2` in `x6`, its low half-byte in `x7`. -/
def rbLoad : List Instr :=
  [.ldrb .x6 .x2 0, .addImm .x .x2 .x2 1, .subImm .x .x5 .x5 1, .logic .and .x .x7 .x6 .x11]

def rbBody (η : Nat) : Prog isa :=
  .seq (.block rbLoad)
    (.ite (.zero .x .x4) (.block [])
      (.seq (.block (rbTry η ++ ([.lsr .x .x7 .x6 4] : List Instr)))
        (.ite (.zero .x .x4) (.block []) (.block (rbTry η)))))

end VG.Impl.MlDsa.AArch64.Sample
